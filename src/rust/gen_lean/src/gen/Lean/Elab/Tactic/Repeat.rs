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
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalRepeat___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__2_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__3_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__3_value)
                as *mut leanh::LeanObject,
            16592576665728214421 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat___closed__5_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__5_value)
                as *mut leanh::LeanObject,
            8504843326314613972 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__6_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 118, 97, 108, 82, 101, 112, 101, 97, 116, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__1_value) as *mut leanh::LeanObject,16974933337766822453 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1: usize = 0;
pub static l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat_x27___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__0_value)
                as *mut leanh::LeanObject,
            4309869778282365895 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat_x27___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat_x27___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [101, 118, 97, 108, 82, 101, 112, 101, 97, 116, 39, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__0_value) as *mut leanh::LeanObject,14670036760128995796 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 17 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 13 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 15 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 15 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [96, 114, 101, 112, 101, 97, 116, 49, 39, 96, 32, 109, 97, 100, 101, 32, 110, 111, 32, 112, 114, 111, 103, 114, 101, 115, 115, 0]};
static mut l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value)
                as *mut leanh::LeanObject,
            18344149449936419494 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__0_value)
                as *mut leanh::LeanObject,
            9350812594340289083 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 118, 97, 108, 82, 101, 112, 101, 97, 116, 49, 39, 0]};
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_evalRepeat___closed__2_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__0_value) as *mut leanh::LeanObject,11253676299092030557 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 24 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__0_value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__1_value) as *mut leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 20 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 16 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__3_value) as *mut leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__4_value) as *mut leanh::LeanObject,((( 16 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__2_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__5_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1100_ = leanh::lean_box(0);
    v___x_1101_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1102_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1102_, 0, v___x_1101_);
    leanh::lean_ctor_set(v___x_1102_, 1, v___x_1100_);
    return v___x_1102_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1104_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___closed__0);
    v___x_1105_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1105_, 0, v___x_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg___boxed(
    mut v___y_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
    return v_res_1107_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0(
    mut v_00_u03b1_1108_: *mut leanh::LeanObject,
    mut v___y_1109_: *mut leanh::LeanObject,
    mut v___y_1110_: *mut leanh::LeanObject,
    mut v___y_1111_: *mut leanh::LeanObject,
    mut v___y_1112_: *mut leanh::LeanObject,
    mut v___y_1113_: *mut leanh::LeanObject,
    mut v___y_1114_: *mut leanh::LeanObject,
    mut v___y_1115_: *mut leanh::LeanObject,
    mut v___y_1116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1118_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
    return v___x_1118_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___boxed(
    mut v_00_u03b1_1119_: *mut leanh::LeanObject,
    mut v___y_1120_: *mut leanh::LeanObject,
    mut v___y_1121_: *mut leanh::LeanObject,
    mut v___y_1122_: *mut leanh::LeanObject,
    mut v___y_1123_: *mut leanh::LeanObject,
    mut v___y_1124_: *mut leanh::LeanObject,
    mut v___y_1125_: *mut leanh::LeanObject,
    mut v___y_1126_: *mut leanh::LeanObject,
    mut v___y_1127_: *mut leanh::LeanObject,
    mut v___y_1128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1127_);
    leanh::lean_dec_ref(v___y_1126_);
    leanh::lean_dec(v___y_1125_);
    leanh::lean_dec_ref(v___y_1124_);
    leanh::lean_dec(v___y_1123_);
    leanh::lean_dec_ref(v___y_1122_);
    leanh::lean_dec(v___y_1121_);
    leanh::lean_dec_ref(v___y_1120_);
    return v_res_1129_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(
    mut v___x_1130_: *mut leanh::LeanObject,
    mut v___y_1131_: *mut leanh::LeanObject,
    mut v___y_1132_: *mut leanh::LeanObject,
    mut v___y_1133_: *mut leanh::LeanObject,
    mut v___y_1134_: *mut leanh::LeanObject,
    mut v___y_1135_: *mut leanh::LeanObject,
    mut v___y_1136_: *mut leanh::LeanObject,
    mut v___y_1137_: *mut leanh::LeanObject,
    mut v___y_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1147_: u8 = 0;
    let mut v___x_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1155_: u8 = 0;
    let mut v_unused_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: u8 = 0;
    let mut v___x_1158_: u8 = 0;
    let mut v_a_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1162_: u8 = 0;
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1140_) == 0 {
                    v_a_1141_ = leanh::lean_ctor_get(v___x_1140_, 0);
                    leanh::lean_inc(v_a_1141_);
                    leanh::lean_dec_ref_known(v___x_1140_, 1);
                    leanh::lean_inc(v___x_1130_);
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
                    if leanh::lean_obj_tag(v___x_1142_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1142_, 1);
                        leanh::lean_dec(v_a_1141_);
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1130_);
                        v_a_1144_ = leanh::lean_ctor_get(v___x_1142_, 0);
                        leanh::lean_inc(v_a_1144_);
                        v___x_1145_ = leanh::lean_box(0);
                        v___x_1157_ = l_Lean_Exception_isInterrupt(v_a_1144_);
                        if v___x_1157_ == 0 {
                            v___x_1158_ = l_Lean_Exception_isRuntime(v_a_1144_);
                            v___y_1147_ = v___x_1158_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_1144_);
                            v___y_1147_ = v___x_1157_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1130_);
                    v_a_1159_ = leanh::lean_ctor_get(v___x_1140_, 0);
                    v_isSharedCheck_1166_ = (!leanh::lean_is_exclusive(v___x_1140_)) as u8;
                    if v_isSharedCheck_1166_ == 0 {
                        v___x_1161_ = v___x_1140_;
                        v_isShared_1162_ = v_isSharedCheck_1166_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1159_);
                        leanh::lean_dec(v___x_1140_);
                        v___x_1161_ = leanh::lean_box(0);
                        v_isShared_1162_ = v_isSharedCheck_1166_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1147_ == 0 {
                    leanh::lean_dec_ref_known(v___x_1142_, 1);
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
                    if leanh::lean_obj_tag(v___x_1148_) == 0 {
                        v_isSharedCheck_1155_ =
                            (!leanh::lean_is_exclusive(v___x_1148_)) as u8;
                        if v_isSharedCheck_1155_ == 0 {
                            v_unused_1156_ = leanh::lean_ctor_get(v___x_1148_, 0);
                            leanh::lean_dec(v_unused_1156_);
                            v___x_1150_ = v___x_1148_;
                            v_isShared_1151_ = v_isSharedCheck_1155_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1148_);
                            v___x_1150_ = leanh::lean_box(0);
                            v_isShared_1151_ = v_isSharedCheck_1155_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_1148_;
                    }
                } else {
                    leanh::lean_dec(v_a_1141_);
                    return v___x_1142_;
                }
            }
            2 => {
                if v_isShared_1151_ == 0 {
                    leanh::lean_ctor_set(v___x_1150_, 0, v___x_1145_);
                    v___x_1153_ = v___x_1150_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1154_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1154_, 0, v___x_1145_);
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
                    v_reuseFailAlloc_1165_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
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
    mut v___x_1167_: *mut leanh::LeanObject,
    mut v___y_1168_: *mut leanh::LeanObject,
    mut v___y_1169_: *mut leanh::LeanObject,
    mut v___y_1170_: *mut leanh::LeanObject,
    mut v___y_1171_: *mut leanh::LeanObject,
    mut v___y_1172_: *mut leanh::LeanObject,
    mut v___y_1173_: *mut leanh::LeanObject,
    mut v___y_1174_: *mut leanh::LeanObject,
    mut v___y_1175_: *mut leanh::LeanObject,
    mut v___y_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1177_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_);
    leanh::lean_dec(v___y_1175_);
    leanh::lean_dec_ref(v___y_1174_);
    leanh::lean_dec(v___y_1173_);
    leanh::lean_dec_ref(v___y_1172_);
    leanh::lean_dec(v___y_1171_);
    leanh::lean_dec_ref(v___y_1170_);
    leanh::lean_dec(v___y_1169_);
    leanh::lean_dec_ref(v___y_1168_);
    return v_res_1177_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat___lam__0(
    mut v___x_1178_: *mut leanh::LeanObject,
    mut v___x_1179_: *mut leanh::LeanObject,
    mut v___y_1180_: *mut leanh::LeanObject,
    mut v___y_1181_: *mut leanh::LeanObject,
    mut v___y_1182_: *mut leanh::LeanObject,
    mut v___y_1183_: *mut leanh::LeanObject,
    mut v___y_1184_: *mut leanh::LeanObject,
    mut v___y_1185_: *mut leanh::LeanObject,
    mut v___y_1186_: *mut leanh::LeanObject,
    mut v___y_1187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1192_: u8 = 0;
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1196_: u8 = 0;
    let mut v_unused_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1189_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_1178_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
                if leanh::lean_obj_tag(v___x_1189_) == 0 {
                    v_isSharedCheck_1196_ = (!leanh::lean_is_exclusive(v___x_1189_)) as u8;
                    if v_isSharedCheck_1196_ == 0 {
                        v_unused_1197_ = leanh::lean_ctor_get(v___x_1189_, 0);
                        leanh::lean_dec(v_unused_1197_);
                        v___x_1191_ = v___x_1189_;
                        v_isShared_1192_ = v_isSharedCheck_1196_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_1189_);
                        v___x_1191_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_1191_, 0, v___x_1179_);
                    v___x_1194_ = v___x_1191_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1195_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1195_, 0, v___x_1179_);
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
    mut v___x_1198_: *mut leanh::LeanObject,
    mut v___x_1199_: *mut leanh::LeanObject,
    mut v___y_1200_: *mut leanh::LeanObject,
    mut v___y_1201_: *mut leanh::LeanObject,
    mut v___y_1202_: *mut leanh::LeanObject,
    mut v___y_1203_: *mut leanh::LeanObject,
    mut v___y_1204_: *mut leanh::LeanObject,
    mut v___y_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1207_);
    leanh::lean_dec_ref(v___y_1206_);
    leanh::lean_dec(v___y_1205_);
    leanh::lean_dec_ref(v___y_1204_);
    leanh::lean_dec(v___y_1203_);
    leanh::lean_dec_ref(v___y_1202_);
    leanh::lean_dec(v___y_1201_);
    leanh::lean_dec_ref(v___y_1200_);
    return v_res_1209_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat(
    mut v_stx_1225_: *mut leanh::LeanObject,
    mut v_a_1226_: *mut leanh::LeanObject,
    mut v_a_1227_: *mut leanh::LeanObject,
    mut v_a_1228_: *mut leanh::LeanObject,
    mut v_a_1229_: *mut leanh::LeanObject,
    mut v_a_1230_: *mut leanh::LeanObject,
    mut v_a_1231_: *mut leanh::LeanObject,
    mut v_a_1232_: *mut leanh::LeanObject,
    mut v_a_1233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: u8 = 0;
    v___x_1235_ = l_Lean_Elab_Tactic_evalRepeat___closed__4;
    leanh::lean_inc(v_stx_1225_);
    v___x_1236_ = l_Lean_Syntax_isOfKind(v_stx_1225_, v___x_1235_);
    if v___x_1236_ == 0 {
        let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_1225_);
        v___x_1237_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
        return v___x_1237_;
    } else {
        let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1241_: u8 = 0;
        v___x_1238_ = leanh::lean_unsigned_to_nat(1);
        v___x_1239_ = l_Lean_Syntax_getArg(v_stx_1225_, v___x_1238_);
        leanh::lean_dec(v_stx_1225_);
        v___x_1240_ = l_Lean_Elab_Tactic_evalRepeat___closed__6;
        leanh::lean_inc(v___x_1239_);
        v___x_1241_ = l_Lean_Syntax_isOfKind(v___x_1239_, v___x_1240_);
        if v___x_1241_ == 0 {
            let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1239_);
            v___x_1242_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
            return v___x_1242_;
        } else {
            let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1243_ = leanh::lean_box(0);
            v___f_1244_ = leanh::lean_alloc_closure(
                l_Lean_Elab_Tactic_evalRepeat___lam__0___boxed as *mut core::ffi::c_void,
                11,
                2,
            );
            leanh::lean_closure_set(v___f_1244_, 0, v___x_1239_);
            leanh::lean_closure_set(v___f_1244_, 1, v___x_1243_);
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
    mut v_stx_1246_: *mut leanh::LeanObject,
    mut v_a_1247_: *mut leanh::LeanObject,
    mut v_a_1248_: *mut leanh::LeanObject,
    mut v_a_1249_: *mut leanh::LeanObject,
    mut v_a_1250_: *mut leanh::LeanObject,
    mut v_a_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
    mut v_a_1253_: *mut leanh::LeanObject,
    mut v_a_1254_: *mut leanh::LeanObject,
    mut v_a_1255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1254_);
    leanh::lean_dec_ref(v_a_1253_);
    leanh::lean_dec(v_a_1252_);
    leanh::lean_dec_ref(v_a_1251_);
    leanh::lean_dec(v_a_1250_);
    leanh::lean_dec_ref(v_a_1249_);
    leanh::lean_dec(v_a_1248_);
    leanh::lean_dec_ref(v_a_1247_);
    return v_res_1256_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1(
    mut v___x_1257_: *mut leanh::LeanObject,
    mut v_inst_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
    mut v___y_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v___y_1264_: *mut leanh::LeanObject,
    mut v___y_1265_: *mut leanh::LeanObject,
    mut v___y_1266_: *mut leanh::LeanObject,
    mut v___y_1267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1269_ = l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___redArg(v___x_1257_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_);
    return v___x_1269_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Elab_Tactic_evalRepeat_spec__1___boxed(
    mut v___x_1270_: *mut leanh::LeanObject,
    mut v_inst_1271_: *mut leanh::LeanObject,
    mut v_a_1272_: *mut leanh::LeanObject,
    mut v___y_1273_: *mut leanh::LeanObject,
    mut v___y_1274_: *mut leanh::LeanObject,
    mut v___y_1275_: *mut leanh::LeanObject,
    mut v___y_1276_: *mut leanh::LeanObject,
    mut v___y_1277_: *mut leanh::LeanObject,
    mut v___y_1278_: *mut leanh::LeanObject,
    mut v___y_1279_: *mut leanh::LeanObject,
    mut v___y_1280_: *mut leanh::LeanObject,
    mut v___y_1281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1280_);
    leanh::lean_dec_ref(v___y_1279_);
    leanh::lean_dec(v___y_1278_);
    leanh::lean_dec_ref(v___y_1277_);
    leanh::lean_dec(v___y_1276_);
    leanh::lean_dec_ref(v___y_1275_);
    leanh::lean_dec(v___y_1274_);
    leanh::lean_dec_ref(v___y_1273_);
    return v_res_1282_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1()
-> *mut leanh::LeanObject {
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1292_ = l_Lean_Elab_Tactic_evalRepeat___closed__4;
    v___x_1293_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1___closed__2;
    v___x_1294_ = leanh::lean_alloc_closure(
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
    mut v_a_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1297_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
    return v_res_1297_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_x_1298_: *mut leanh::LeanObject,
    mut v___y_1299_: *mut leanh::LeanObject,
    mut v___y_1300_: *mut leanh::LeanObject,
    mut v___y_1301_: *mut leanh::LeanObject,
    mut v___y_1302_: *mut leanh::LeanObject,
    mut v___y_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
    mut v___y_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v_a_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1325_: u8 = 0;
    let mut v___y_1327_: u8 = 0;
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1337_: u8 = 0;
    let mut v_unused_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1342_: u8 = 0;
    let mut v___x_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1346_: u8 = 0;
    let mut v_a_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: u8 = 0;
    let mut v___x_1359_: u8 = 0;
    let mut v_isSharedCheck_1360_: u8 = 0;
    let mut v_a_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1368_: u8 = 0;
    let mut v_a_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1372_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1308_) == 0 {
                    v_a_1309_ = leanh::lean_ctor_get(v___x_1308_, 0);
                    leanh::lean_inc(v_a_1309_);
                    leanh::lean_dec_ref_known(v___x_1308_, 1);
                    v___x_1310_ = l_Lean_Elab_Tactic_saveState___redArg(
                        v___y_1300_,
                        v___y_1302_,
                        v___y_1304_,
                        v___y_1306_,
                    );
                    if leanh::lean_obj_tag(v___x_1310_) == 0 {
                        v_a_1311_ = leanh::lean_ctor_get(v___x_1310_, 0);
                        leanh::lean_inc(v_a_1311_);
                        leanh::lean_dec_ref_known(v___x_1310_, 1);
                        leanh::lean_inc(v___y_1306_);
                        leanh::lean_inc_ref(v___y_1305_);
                        leanh::lean_inc(v___y_1304_);
                        leanh::lean_inc_ref(v___y_1303_);
                        leanh::lean_inc(v___y_1302_);
                        leanh::lean_inc_ref(v___y_1301_);
                        leanh::lean_inc(v___y_1300_);
                        leanh::lean_inc_ref(v___y_1299_);
                        v___x_1312_ = leanh::lean_apply_9(
                            v_x_1298_,
                            v___y_1299_,
                            v___y_1300_,
                            v___y_1301_,
                            v___y_1302_,
                            v___y_1303_,
                            v___y_1304_,
                            v___y_1305_,
                            v___y_1306_,
                            leanh::lean_box(0),
                        );
                        if leanh::lean_obj_tag(v___x_1312_) == 0 {
                            leanh::lean_dec(v_a_1311_);
                            leanh::lean_dec(v_a_1309_);
                            v_a_1313_ = leanh::lean_ctor_get(v___x_1312_, 0);
                            v_isSharedCheck_1321_ =
                                (!leanh::lean_is_exclusive(v___x_1312_)) as u8;
                            if v_isSharedCheck_1321_ == 0 {
                                v___x_1315_ = v___x_1312_;
                                v_isShared_1316_ = v_isSharedCheck_1321_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1313_);
                                leanh::lean_dec(v___x_1312_);
                                v___x_1315_ = leanh::lean_box(0);
                                v_isShared_1316_ = v_isSharedCheck_1321_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_1322_ = leanh::lean_ctor_get(v___x_1312_, 0);
                            v_isSharedCheck_1360_ =
                                (!leanh::lean_is_exclusive(v___x_1312_)) as u8;
                            if v_isSharedCheck_1360_ == 0 {
                                v___x_1324_ = v___x_1312_;
                                v_isShared_1325_ = v_isSharedCheck_1360_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1322_);
                                leanh::lean_dec(v___x_1312_);
                                v___x_1324_ = leanh::lean_box(0);
                                v_isShared_1325_ = v_isSharedCheck_1360_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1309_);
                        leanh::lean_dec_ref(v_x_1298_);
                        v_a_1361_ = leanh::lean_ctor_get(v___x_1310_, 0);
                        v_isSharedCheck_1368_ =
                            (!leanh::lean_is_exclusive(v___x_1310_)) as u8;
                        if v_isSharedCheck_1368_ == 0 {
                            v___x_1363_ = v___x_1310_;
                            v_isShared_1364_ = v_isSharedCheck_1368_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1361_);
                            leanh::lean_dec(v___x_1310_);
                            v___x_1363_ = leanh::lean_box(0);
                            v_isShared_1364_ = v_isSharedCheck_1368_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_1298_);
                    v_a_1369_ = leanh::lean_ctor_get(v___x_1308_, 0);
                    v_isSharedCheck_1376_ = (!leanh::lean_is_exclusive(v___x_1308_)) as u8;
                    if v_isSharedCheck_1376_ == 0 {
                        v___x_1371_ = v___x_1308_;
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1369_);
                        leanh::lean_dec(v___x_1308_);
                        v___x_1371_ = leanh::lean_box(0);
                        v_isShared_1372_ = v_isSharedCheck_1376_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1317_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1317_, 0, v_a_1313_);
                if v_isShared_1316_ == 0 {
                    leanh::lean_ctor_set(v___x_1315_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1315_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1320_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
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
                    leanh::lean_inc(v_a_1322_);
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
                    leanh::lean_del_object(v___x_1324_);
                    leanh::lean_dec(v_a_1322_);
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
                    if leanh::lean_obj_tag(v___x_1328_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1328_, 1);
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
                        if leanh::lean_obj_tag(v___x_1329_) == 0 {
                            v_isSharedCheck_1337_ =
                                (!leanh::lean_is_exclusive(v___x_1329_)) as u8;
                            if v_isSharedCheck_1337_ == 0 {
                                v_unused_1338_ = leanh::lean_ctor_get(v___x_1329_, 0);
                                leanh::lean_dec(v_unused_1338_);
                                v___x_1331_ = v___x_1329_;
                                v_isShared_1332_ = v_isSharedCheck_1337_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1329_);
                                v___x_1331_ = leanh::lean_box(0);
                                v_isShared_1332_ = v_isSharedCheck_1337_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_1339_ = leanh::lean_ctor_get(v___x_1329_, 0);
                            v_isSharedCheck_1346_ =
                                (!leanh::lean_is_exclusive(v___x_1329_)) as u8;
                            if v_isSharedCheck_1346_ == 0 {
                                v___x_1341_ = v___x_1329_;
                                v_isShared_1342_ = v_isSharedCheck_1346_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1339_);
                                leanh::lean_dec(v___x_1329_);
                                v___x_1341_ = leanh::lean_box(0);
                                v_isShared_1342_ = v_isSharedCheck_1346_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1309_);
                        v_a_1347_ = leanh::lean_ctor_get(v___x_1328_, 0);
                        v_isSharedCheck_1354_ =
                            (!leanh::lean_is_exclusive(v___x_1328_)) as u8;
                        if v_isSharedCheck_1354_ == 0 {
                            v___x_1349_ = v___x_1328_;
                            v_isShared_1350_ = v_isSharedCheck_1354_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1347_);
                            leanh::lean_dec(v___x_1328_);
                            v___x_1349_ = leanh::lean_box(0);
                            v_isShared_1350_ = v_isSharedCheck_1354_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_1311_);
                    leanh::lean_dec(v_a_1309_);
                    if v_isShared_1325_ == 0 {
                        v___x_1356_ = v___x_1324_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1357_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1322_);
                        v___x_1356_ = v_reuseFailAlloc_1357_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1333_ = leanh::lean_box(0);
                if v_isShared_1332_ == 0 {
                    leanh::lean_ctor_set(v___x_1331_, 0, v___x_1333_);
                    v___x_1335_ = v___x_1331_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
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
                    v_reuseFailAlloc_1345_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
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
                    v_reuseFailAlloc_1353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
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
                    v_reuseFailAlloc_1367_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
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
                    v_reuseFailAlloc_1375_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
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
    mut v_x_1377_: *mut leanh::LeanObject,
    mut v___y_1378_: *mut leanh::LeanObject,
    mut v___y_1379_: *mut leanh::LeanObject,
    mut v___y_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
    mut v___y_1382_: *mut leanh::LeanObject,
    mut v___y_1383_: *mut leanh::LeanObject,
    mut v___y_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
    leanh::lean_dec(v___y_1385_);
    leanh::lean_dec_ref(v___y_1384_);
    leanh::lean_dec(v___y_1383_);
    leanh::lean_dec_ref(v___y_1382_);
    leanh::lean_dec(v___y_1381_);
    leanh::lean_dec_ref(v___y_1380_);
    leanh::lean_dec(v___y_1379_);
    leanh::lean_dec_ref(v___y_1378_);
    return v_res_1387_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(
    mut v_keys_1388_: *mut leanh::LeanObject,
    mut v_i_1389_: *mut leanh::LeanObject,
    mut v_k_1390_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: u8 = 0;
    let mut v_k_x27_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: u8 = 0;
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1391_ = lean_array_get_size(v_keys_1388_);
                v___x_1392_ = lean_nat_dec_lt(v_i_1389_, v___x_1391_);
                if v___x_1392_ == 0 {
                    leanh::lean_dec(v_i_1389_);
                    return v___x_1392_;
                } else {
                    v_k_x27_1393_ = lean_array_fget_borrowed(v_keys_1388_, v_i_1389_);
                    v___x_1394_ = l_Lean_instBEqMVarId_beq(v_k_1390_, v_k_x27_1393_);
                    if v___x_1394_ == 0 {
                        v___x_1395_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1396_ = lean_nat_add(v_i_1389_, v___x_1395_);
                        leanh::lean_dec(v_i_1389_);
                        v_i_1389_ = v___x_1396_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_1389_);
                        return v___x_1394_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg___boxed(
    mut v_keys_1398_: *mut leanh::LeanObject,
    mut v_i_1399_: *mut leanh::LeanObject,
    mut v_k_1400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1401_: u8 = 0;
    let mut v_r_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1401_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_1398_, v_i_1399_, v_k_1400_);
    leanh::lean_dec(v_k_1400_);
    leanh::lean_dec_ref(v_keys_1398_);
    v_r_1402_ = leanh::lean_box((v_res_1401_) as usize);
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
    v___x_1407_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__0);
    v___x_1408_ = lean_usize_sub(v___x_1407_, v___x_1406_);
    return v___x_1408_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(
    mut v_x_1409_: *mut leanh::LeanObject,
    mut v_x_1410_: usize,
    mut v_x_1411_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: usize = 0;
    let mut v___x_1415_: usize = 0;
    let mut v___x_1416_: usize = 0;
    let mut v_j_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: u8 = 0;
    let mut v_node_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: usize = 0;
    let mut v___x_1424_: u8 = 0;
    let mut v_ks_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1409_) == 0 {
                    v_es_1412_ = leanh::lean_ctor_get(v_x_1409_, 0);
                    v___x_1413_ = leanh::lean_box(2);
                    v___x_1414_ = 5usize;
                    v___x_1415_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___closed__1);
                    v___x_1416_ = lean_usize_land(v_x_1410_, v___x_1415_);
                    v_j_1417_ = lean_usize_to_nat(v___x_1416_);
                    v___x_1418_ = lean_array_get_borrowed(v___x_1413_, v_es_1412_, v_j_1417_);
                    leanh::lean_dec(v_j_1417_);
                    match leanh::lean_obj_tag(v___x_1418_) {
                        0 => {
                            v_key_1419_ = leanh::lean_ctor_get(v___x_1418_, 0);
                            v___x_1420_ = l_Lean_instBEqMVarId_beq(v_x_1411_, v_key_1419_);
                            return v___x_1420_;
                        }
                        1 => {
                            v_node_1421_ = leanh::lean_ctor_get(v___x_1418_, 0);
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
                    v_ks_1425_ = leanh::lean_ctor_get(v_x_1409_, 0);
                    v___x_1426_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1427_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_ks_1425_, v___x_1426_, v_x_1411_);
                    return v___x_1427_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg___boxed(
    mut v_x_1428_: *mut leanh::LeanObject,
    mut v_x_1429_: *mut leanh::LeanObject,
    mut v_x_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4769__boxed_1431_: usize = 0;
    let mut v_res_1432_: u8 = 0;
    let mut v_r_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4769__boxed_1431_ = leanh::lean_unbox_usize(v_x_1429_);
    leanh::lean_dec(v_x_1429_);
    v_res_1432_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_1428_, v_x_4769__boxed_1431_, v_x_1430_);
    leanh::lean_dec(v_x_1430_);
    leanh::lean_dec_ref(v_x_1428_);
    v_r_1433_ = leanh::lean_box((v_res_1432_) as usize);
    return v_r_1433_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_x_1434_: *mut leanh::LeanObject,
    mut v_x_1435_: *mut leanh::LeanObject,
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
    mut v_x_1439_: *mut leanh::LeanObject,
    mut v_x_1440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1441_: u8 = 0;
    let mut v_r_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1441_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1439_, v_x_1440_);
    leanh::lean_dec(v_x_1440_);
    leanh::lean_dec_ref(v_x_1439_);
    v_r_1442_ = leanh::lean_box((v_res_1441_) as usize);
    return v_r_1442_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(
    mut v_mvarId_1443_: *mut leanh::LeanObject,
    mut v___y_1444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: u8 = 0;
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = lean_st_ref_get(v___y_1444_);
    v_mctx_1447_ = leanh::lean_ctor_get(v___x_1446_, 0);
    leanh::lean_inc_ref(v_mctx_1447_);
    leanh::lean_dec(v___x_1446_);
    v_eAssignment_1448_ = leanh::lean_ctor_get(v_mctx_1447_, 8);
    leanh::lean_inc_ref(v_eAssignment_1448_);
    leanh::lean_dec_ref(v_mctx_1447_);
    v___x_1449_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_eAssignment_1448_, v_mvarId_1443_);
    leanh::lean_dec_ref(v_eAssignment_1448_);
    v___x_1450_ = leanh::lean_box((v___x_1449_) as usize);
    v___x_1451_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1451_, 0, v___x_1450_);
    return v___x_1451_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_mvarId_1452_: *mut leanh::LeanObject,
    mut v___y_1453_: *mut leanh::LeanObject,
    mut v___y_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1455_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_1452_, v___y_1453_);
    leanh::lean_dec(v___y_1453_);
    leanh::lean_dec(v_mvarId_1452_);
    return v_res_1455_;
}
pub unsafe fn l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(
    mut v_x_1456_: *mut leanh::LeanObject,
    mut v_x_1457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1457_) == 0 {
                    return v_x_1456_;
                } else {
                    v_head_1458_ = leanh::lean_ctor_get(v_x_1457_, 0);
                    leanh::lean_inc(v_head_1458_);
                    v_tail_1459_ = leanh::lean_ctor_get(v_x_1457_, 1);
                    leanh::lean_inc(v_tail_1459_);
                    leanh::lean_dec_ref_known(v_x_1457_, 2);
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
    mut v_f_1462_: *mut leanh::LeanObject,
    mut v_a_1463_: *mut leanh::LeanObject,
    mut v_a_1464_: u8,
    mut v_a_1465_: *mut leanh::LeanObject,
    mut v_a_1466_: *mut leanh::LeanObject,
    mut v_a_1467_: *mut leanh::LeanObject,
    mut v___y_1468_: *mut leanh::LeanObject,
    mut v___y_1469_: *mut leanh::LeanObject,
    mut v___y_1470_: *mut leanh::LeanObject,
    mut v___y_1471_: *mut leanh::LeanObject,
    mut v___y_1472_: *mut leanh::LeanObject,
    mut v___y_1473_: *mut leanh::LeanObject,
    mut v___y_1474_: *mut leanh::LeanObject,
    mut v___y_1475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1487_: u8 = 0;
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1492_: u8 = 0;
    let mut v___x_1493_: u8 = 0;
    let mut v_zero_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1495_: u8 = 0;
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1520_: u8 = 0;
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1524_: u8 = 0;
    let mut v_isSharedCheck_1526_: u8 = 0;
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1465_) == 0 {
                    if leanh::lean_obj_tag(v_a_1466_) == 0 {
                        leanh::lean_dec(v_a_1463_);
                        leanh::lean_dec_ref(v_f_1462_);
                        v___x_1477_ = leanh::lean_box((v_a_1464_) as usize);
                        v___x_1478_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1478_, 0, v___x_1477_);
                        leanh::lean_ctor_set(v___x_1478_, 1, v_a_1467_);
                        v___x_1479_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1479_, 0, v___x_1478_);
                        return v___x_1479_;
                    } else {
                        v_head_1480_ = leanh::lean_ctor_get(v_a_1466_, 0);
                        leanh::lean_inc(v_head_1480_);
                        v_tail_1481_ = leanh::lean_ctor_get(v_a_1466_, 1);
                        leanh::lean_inc(v_tail_1481_);
                        leanh::lean_dec_ref_known(v_a_1466_, 2);
                        v_a_1465_ = v_head_1480_;
                        v_a_1466_ = v_tail_1481_;
                        state = 0;
                        continue;
                    }
                } else {
                    v_head_1483_ = leanh::lean_ctor_get(v_a_1465_, 0);
                    v_tail_1484_ = leanh::lean_ctor_get(v_a_1465_, 1);
                    v_isSharedCheck_1527_ = (!leanh::lean_is_exclusive(v_a_1465_)) as u8;
                    if v_isSharedCheck_1527_ == 0 {
                        v___x_1486_ = v_a_1465_;
                        v_isShared_1487_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1484_);
                        leanh::lean_inc(v_head_1483_);
                        leanh::lean_dec(v_a_1465_);
                        v___x_1486_ = leanh::lean_box(0);
                        v_isShared_1487_ = v_isSharedCheck_1527_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1488_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_head_1483_, v___y_1473_);
                v_a_1489_ = leanh::lean_ctor_get(v___x_1488_, 0);
                v_isSharedCheck_1526_ = (!leanh::lean_is_exclusive(v___x_1488_)) as u8;
                if v_isSharedCheck_1526_ == 0 {
                    v___x_1491_ = v___x_1488_;
                    v_isShared_1492_ = v_isSharedCheck_1526_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1489_);
                    leanh::lean_dec(v___x_1488_);
                    v___x_1491_ = leanh::lean_box(0);
                    v_isShared_1492_ = v_isSharedCheck_1526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1493_ = (leanh::lean_unbox(v_a_1489_) as u8);
                leanh::lean_dec(v_a_1489_);
                if v___x_1493_ == 0 {
                    v_zero_1494_ = leanh::lean_unsigned_to_nat(0);
                    v_isZero_1495_ = lean_nat_dec_eq(v_a_1463_, v_zero_1494_);
                    if v_isZero_1495_ == 1 {
                        leanh::lean_del_object(v___x_1486_);
                        leanh::lean_dec(v_a_1463_);
                        leanh::lean_dec_ref(v_f_1462_);
                        v___x_1496_ = lean_array_push(v_a_1467_, v_head_1483_);
                        v___x_1497_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                            v___x_1496_,
                            v_tail_1484_,
                        );
                        v___x_1498_ = l_List_foldl___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__3(v___x_1497_, v_a_1466_);
                        v___x_1499_ = leanh::lean_box((v_a_1464_) as usize);
                        v___x_1500_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1500_, 0, v___x_1499_);
                        leanh::lean_ctor_set(v___x_1500_, 1, v___x_1498_);
                        if v_isShared_1492_ == 0 {
                            leanh::lean_ctor_set(v___x_1491_, 0, v___x_1500_);
                            v___x_1502_ = v___x_1491_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1503_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1503_, 0, v___x_1500_);
                            v___x_1502_ = v_reuseFailAlloc_1503_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_1491_);
                        leanh::lean_inc_ref(v_f_1462_);
                        leanh::lean_inc(v_head_1483_);
                        v___x_1504_ = leanh::lean_apply_1(v_f_1462_, v_head_1483_);
                        v___x_1505_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1504_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_);
                        if leanh::lean_obj_tag(v___x_1505_) == 0 {
                            v_a_1506_ = leanh::lean_ctor_get(v___x_1505_, 0);
                            leanh::lean_inc(v_a_1506_);
                            leanh::lean_dec_ref_known(v___x_1505_, 1);
                            v_one_1507_ = leanh::lean_unsigned_to_nat(1);
                            v_n_1508_ = lean_nat_sub(v_a_1463_, v_one_1507_);
                            leanh::lean_dec(v_a_1463_);
                            if leanh::lean_obj_tag(v_a_1506_) == 0 {
                                leanh::lean_del_object(v___x_1486_);
                                v___x_1509_ = lean_array_push(v_a_1467_, v_head_1483_);
                                v_a_1463_ = v_n_1508_;
                                v_a_1465_ = v_tail_1484_;
                                v_a_1467_ = v___x_1509_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v_head_1483_);
                                v_val_1511_ = leanh::lean_ctor_get(v_a_1506_, 0);
                                leanh::lean_inc(v_val_1511_);
                                leanh::lean_dec_ref_known(v_a_1506_, 1);
                                v___x_1512_ = 1;
                                if v_isShared_1487_ == 0 {
                                    leanh::lean_ctor_set(v___x_1486_, 1, v_a_1466_);
                                    leanh::lean_ctor_set(v___x_1486_, 0, v_tail_1484_);
                                    v___x_1514_ = v___x_1486_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1516_ =
                                        leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1516_,
                                        0,
                                        v_tail_1484_,
                                    );
                                    leanh::lean_ctor_set(
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
                            leanh::lean_del_object(v___x_1486_);
                            leanh::lean_dec(v_tail_1484_);
                            leanh::lean_dec(v_head_1483_);
                            leanh::lean_dec_ref(v_a_1467_);
                            leanh::lean_dec(v_a_1466_);
                            leanh::lean_dec(v_a_1463_);
                            leanh::lean_dec_ref(v_f_1462_);
                            v_a_1517_ = leanh::lean_ctor_get(v___x_1505_, 0);
                            v_isSharedCheck_1524_ =
                                (!leanh::lean_is_exclusive(v___x_1505_)) as u8;
                            if v_isSharedCheck_1524_ == 0 {
                                v___x_1519_ = v___x_1505_;
                                v_isShared_1520_ = v_isSharedCheck_1524_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1517_);
                                leanh::lean_dec(v___x_1505_);
                                v___x_1519_ = leanh::lean_box(0);
                                v_isShared_1520_ = v_isSharedCheck_1524_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1491_);
                    leanh::lean_del_object(v___x_1486_);
                    leanh::lean_dec(v_head_1483_);
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
                    v_reuseFailAlloc_1523_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1523_, 0, v_a_1517_);
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
    mut v_f_1528_: *mut leanh::LeanObject,
    mut v_a_1529_: *mut leanh::LeanObject,
    mut v_a_1530_: *mut leanh::LeanObject,
    mut v_a_1531_: *mut leanh::LeanObject,
    mut v_a_1532_: *mut leanh::LeanObject,
    mut v_a_1533_: *mut leanh::LeanObject,
    mut v___y_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
    mut v___y_1538_: *mut leanh::LeanObject,
    mut v___y_1539_: *mut leanh::LeanObject,
    mut v___y_1540_: *mut leanh::LeanObject,
    mut v___y_1541_: *mut leanh::LeanObject,
    mut v___y_1542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_4854__boxed_1543_: u8 = 0;
    let mut v_res_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_4854__boxed_1543_ = (leanh::lean_unbox(v_a_1530_) as u8);
    v_res_1544_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_1528_, v_a_1529_, v_a_4854__boxed_1543_, v_a_1531_, v_a_1532_, v_a_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_);
    leanh::lean_dec(v___y_1541_);
    leanh::lean_dec_ref(v___y_1540_);
    leanh::lean_dec(v___y_1539_);
    leanh::lean_dec_ref(v___y_1538_);
    leanh::lean_dec(v___y_1537_);
    leanh::lean_dec_ref(v___y_1536_);
    leanh::lean_dec(v___y_1535_);
    leanh::lean_dec_ref(v___y_1534_);
    return v_res_1544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(
    mut v_as_1545_: *mut leanh::LeanObject,
    mut v_i_1546_: usize,
    mut v_stop_1547_: usize,
    mut v_b_1548_: *mut leanh::LeanObject,
    mut v___y_1549_: *mut leanh::LeanObject,
    mut v___y_1550_: *mut leanh::LeanObject,
    mut v___y_1551_: *mut leanh::LeanObject,
    mut v___y_1552_: *mut leanh::LeanObject,
    mut v___y_1553_: *mut leanh::LeanObject,
    mut v___y_1554_: *mut leanh::LeanObject,
    mut v___y_1555_: *mut leanh::LeanObject,
    mut v___y_1556_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: usize = 0;
    let mut v___x_1561_: usize = 0;
    let mut v___x_1563_: u8 = 0;
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v_a_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v_a_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1575_: u8 = 0;
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1579_: u8 = 0;
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1563_ = lean_usize_dec_eq(v_i_1546_, v_stop_1547_);
                if v___x_1563_ == 0 {
                    v___x_1564_ = lean_array_uget_borrowed(v_as_1545_, v_i_1546_);
                    v___x_1567_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v___x_1564_, v___y_1554_);
                    if leanh::lean_obj_tag(v___x_1567_) == 0 {
                        v_a_1568_ = leanh::lean_ctor_get(v___x_1567_, 0);
                        leanh::lean_inc(v_a_1568_);
                        leanh::lean_dec_ref_known(v___x_1567_, 1);
                        v___x_1569_ = (leanh::lean_unbox(v_a_1568_) as u8);
                        leanh::lean_dec(v_a_1568_);
                        if v___x_1569_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_1559_ = v_b_1548_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_1567_) == 0 {
                            v_a_1570_ = leanh::lean_ctor_get(v___x_1567_, 0);
                            leanh::lean_inc(v_a_1570_);
                            leanh::lean_dec_ref_known(v___x_1567_, 1);
                            v___x_1571_ = (leanh::lean_unbox(v_a_1570_) as u8);
                            leanh::lean_dec(v_a_1570_);
                            if v___x_1571_ == 0 {
                                v_a_1559_ = v_b_1548_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_b_1548_);
                            v_a_1572_ = leanh::lean_ctor_get(v___x_1567_, 0);
                            v_isSharedCheck_1579_ =
                                (!leanh::lean_is_exclusive(v___x_1567_)) as u8;
                            if v_isSharedCheck_1579_ == 0 {
                                v___x_1574_ = v___x_1567_;
                                v_isShared_1575_ = v_isSharedCheck_1579_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1572_);
                                leanh::lean_dec(v___x_1567_);
                                v___x_1574_ = leanh::lean_box(0);
                                v_isShared_1575_ = v_isSharedCheck_1579_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_1580_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1580_, 0, v_b_1548_);
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
                leanh::lean_inc(v___x_1564_);
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
                    v_reuseFailAlloc_1578_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
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
    mut v_as_1581_: *mut leanh::LeanObject,
    mut v_i_1582_: *mut leanh::LeanObject,
    mut v_stop_1583_: *mut leanh::LeanObject,
    mut v_b_1584_: *mut leanh::LeanObject,
    mut v___y_1585_: *mut leanh::LeanObject,
    mut v___y_1586_: *mut leanh::LeanObject,
    mut v___y_1587_: *mut leanh::LeanObject,
    mut v___y_1588_: *mut leanh::LeanObject,
    mut v___y_1589_: *mut leanh::LeanObject,
    mut v___y_1590_: *mut leanh::LeanObject,
    mut v___y_1591_: *mut leanh::LeanObject,
    mut v___y_1592_: *mut leanh::LeanObject,
    mut v___y_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1594_: usize = 0;
    let mut v_stop_boxed_1595_: usize = 0;
    let mut v_res_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1594_ = leanh::lean_unbox_usize(v_i_1582_);
    leanh::lean_dec(v_i_1582_);
    v_stop_boxed_1595_ = leanh::lean_unbox_usize(v_stop_1583_);
    leanh::lean_dec(v_stop_1583_);
    v_res_1596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_as_1581_, v_i_boxed_1594_, v_stop_boxed_1595_, v_b_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
    leanh::lean_dec(v___y_1592_);
    leanh::lean_dec_ref(v___y_1591_);
    leanh::lean_dec(v___y_1590_);
    leanh::lean_dec_ref(v___y_1589_);
    leanh::lean_dec(v___y_1588_);
    leanh::lean_dec_ref(v___y_1587_);
    leanh::lean_dec(v___y_1586_);
    leanh::lean_dec_ref(v___y_1585_);
    leanh::lean_dec_ref(v_as_1581_);
    return v_res_1596_;
}
pub unsafe fn _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0;
    v___x_1600_ = lean_array_to_list(v___x_1599_);
    return v___x_1600_;
}
pub unsafe fn l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(
    mut v_f_1601_: *mut leanh::LeanObject,
    mut v_goals_1602_: *mut leanh::LeanObject,
    mut v_maxIters_1603_: *mut leanh::LeanObject,
    mut v___y_1604_: *mut leanh::LeanObject,
    mut v___y_1605_: *mut leanh::LeanObject,
    mut v___y_1606_: *mut leanh::LeanObject,
    mut v___y_1607_: *mut leanh::LeanObject,
    mut v___y_1608_: *mut leanh::LeanObject,
    mut v___y_1609_: *mut leanh::LeanObject,
    mut v___y_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v_fst_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v_____do__lift_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: u8 = 0;
    let mut v___x_1642_: usize = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1649_: u8 = 0;
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1653_: u8 = 0;
    let mut v___x_1654_: usize = 0;
    let mut v___x_1655_: usize = 0;
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1661_: u8 = 0;
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1665_: u8 = 0;
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut v_isSharedCheck_1667_: u8 = 0;
    let mut v_a_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1675_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1613_ = 0;
                v___x_1614_ = leanh::lean_box(0);
                v___x_1615_ = leanh::lean_unsigned_to_nat(0);
                v___x_1616_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__0;
                v___x_1617_ = l___private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1(v_f_1601_, v_maxIters_1603_, v___x_1613_, v_goals_1602_, v___x_1614_, v___x_1616_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
                if leanh::lean_obj_tag(v___x_1617_) == 0 {
                    v_a_1618_ = leanh::lean_ctor_get(v___x_1617_, 0);
                    v_isSharedCheck_1667_ = (!leanh::lean_is_exclusive(v___x_1617_)) as u8;
                    if v_isSharedCheck_1667_ == 0 {
                        v___x_1620_ = v___x_1617_;
                        v_isShared_1621_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1618_);
                        leanh::lean_dec(v___x_1617_);
                        v___x_1620_ = leanh::lean_box(0);
                        v_isShared_1621_ = v_isSharedCheck_1667_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1668_ = leanh::lean_ctor_get(v___x_1617_, 0);
                    v_isSharedCheck_1675_ = (!leanh::lean_is_exclusive(v___x_1617_)) as u8;
                    if v_isSharedCheck_1675_ == 0 {
                        v___x_1670_ = v___x_1617_;
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1668_);
                        leanh::lean_dec(v___x_1617_);
                        v___x_1670_ = leanh::lean_box(0);
                        v_isShared_1671_ = v_isSharedCheck_1675_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1622_ = leanh::lean_ctor_get(v_a_1618_, 0);
                v_snd_1623_ = leanh::lean_ctor_get(v_a_1618_, 1);
                v_isSharedCheck_1666_ = (!leanh::lean_is_exclusive(v_a_1618_)) as u8;
                if v_isSharedCheck_1666_ == 0 {
                    v___x_1625_ = v_a_1618_;
                    v_isShared_1626_ = v_isSharedCheck_1666_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1623_);
                    leanh::lean_inc(v_fst_1622_);
                    leanh::lean_dec(v_a_1618_);
                    v___x_1625_ = leanh::lean_box(0);
                    v_isShared_1626_ = v_isSharedCheck_1666_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1636_ = lean_array_get_size(v_snd_1623_);
                v___x_1637_ = lean_nat_dec_lt(v___x_1615_, v___x_1636_);
                if v___x_1637_ == 0 {
                    leanh::lean_del_object(v___x_1625_);
                    leanh::lean_dec(v_snd_1623_);
                    leanh::lean_del_object(v___x_1620_);
                    v___x_1638_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1_once), _init_l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___closed__1);
                    v___x_1639_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1639_, 0, v_fst_1622_);
                    leanh::lean_ctor_set(v___x_1639_, 1, v___x_1638_);
                    v___x_1640_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1640_, 0, v___x_1639_);
                    return v___x_1640_;
                } else {
                    v___x_1641_ = lean_nat_dec_le(v___x_1636_, v___x_1636_);
                    if v___x_1641_ == 0 {
                        if v___x_1637_ == 0 {
                            leanh::lean_dec(v_snd_1623_);
                            v_____do__lift_1628_ = v___x_1616_;
                            state = 3;
                            continue;
                        } else {
                            v___x_1642_ = 0usize;
                            v___x_1643_ = lean_usize_of_nat(v___x_1636_);
                            v___x_1644_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__3(v_snd_1623_, v___x_1642_, v___x_1643_, v___x_1616_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
                            leanh::lean_dec(v_snd_1623_);
                            if leanh::lean_obj_tag(v___x_1644_) == 0 {
                                v_a_1645_ = leanh::lean_ctor_get(v___x_1644_, 0);
                                leanh::lean_inc(v_a_1645_);
                                leanh::lean_dec_ref_known(v___x_1644_, 1);
                                v_____do__lift_1628_ = v_a_1645_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_del_object(v___x_1625_);
                                leanh::lean_dec(v_fst_1622_);
                                leanh::lean_del_object(v___x_1620_);
                                v_a_1646_ = leanh::lean_ctor_get(v___x_1644_, 0);
                                v_isSharedCheck_1653_ =
                                    (!leanh::lean_is_exclusive(v___x_1644_)) as u8;
                                if v_isSharedCheck_1653_ == 0 {
                                    v___x_1648_ = v___x_1644_;
                                    v_isShared_1649_ = v_isSharedCheck_1653_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1646_);
                                    leanh::lean_dec(v___x_1644_);
                                    v___x_1648_ = leanh::lean_box(0);
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
                        leanh::lean_dec(v_snd_1623_);
                        if leanh::lean_obj_tag(v___x_1656_) == 0 {
                            v_a_1657_ = leanh::lean_ctor_get(v___x_1656_, 0);
                            leanh::lean_inc(v_a_1657_);
                            leanh::lean_dec_ref_known(v___x_1656_, 1);
                            v_____do__lift_1628_ = v_a_1657_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_1625_);
                            leanh::lean_dec(v_fst_1622_);
                            leanh::lean_del_object(v___x_1620_);
                            v_a_1658_ = leanh::lean_ctor_get(v___x_1656_, 0);
                            v_isSharedCheck_1665_ =
                                (!leanh::lean_is_exclusive(v___x_1656_)) as u8;
                            if v_isSharedCheck_1665_ == 0 {
                                v___x_1660_ = v___x_1656_;
                                v_isShared_1661_ = v_isSharedCheck_1665_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1658_);
                                leanh::lean_dec(v___x_1656_);
                                v___x_1660_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_1625_, 1, v___x_1629_);
                    v___x_1631_ = v___x_1625_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1635_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_fst_1622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 1, v___x_1629_);
                    v___x_1631_ = v_reuseFailAlloc_1635_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1621_ == 0 {
                    leanh::lean_ctor_set(v___x_1620_, 0, v___x_1631_);
                    v___x_1633_ = v___x_1620_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1634_, 0, v___x_1631_);
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
                    v_reuseFailAlloc_1652_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
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
                    v_reuseFailAlloc_1664_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1664_, 0, v_a_1658_);
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
                    v_reuseFailAlloc_1674_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
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
    mut v_f_1676_: *mut leanh::LeanObject,
    mut v_goals_1677_: *mut leanh::LeanObject,
    mut v_maxIters_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
    mut v___y_1682_: *mut leanh::LeanObject,
    mut v___y_1683_: *mut leanh::LeanObject,
    mut v___y_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
    mut v___y_1687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1688_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_1676_, v_goals_1677_, v_maxIters_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
    leanh::lean_dec(v___y_1686_);
    leanh::lean_dec_ref(v___y_1685_);
    leanh::lean_dec(v___y_1684_);
    leanh::lean_dec_ref(v___y_1683_);
    leanh::lean_dec(v___y_1682_);
    leanh::lean_dec_ref(v___y_1681_);
    leanh::lean_dec(v___y_1680_);
    leanh::lean_dec_ref(v___y_1679_);
    return v_res_1688_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(
    mut v_x_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_snd_1690_ = leanh::lean_ctor_get(v_x_1689_, 1);
    leanh::lean_inc(v_snd_1690_);
    return v_snd_1690_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0___boxed(
    mut v_x_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1692_ =
        l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___lam__0(v_x_1691_);
    leanh::lean_dec_ref(v_x_1691_);
    return v_res_1692_;
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(
    mut v_a_1693_: *mut leanh::LeanObject,
    mut v_f_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
    mut v___y_1699_: *mut leanh::LeanObject,
    mut v___y_1700_: *mut leanh::LeanObject,
    mut v___y_1701_: *mut leanh::LeanObject,
    mut v___y_1702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1713_: u8 = 0;
    let mut v_a_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1721_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1702_);
                leanh::lean_inc_ref(v___y_1701_);
                leanh::lean_inc(v___y_1700_);
                leanh::lean_inc_ref(v___y_1699_);
                leanh::lean_inc(v___y_1698_);
                leanh::lean_inc_ref(v___y_1697_);
                leanh::lean_inc(v___y_1696_);
                leanh::lean_inc_ref(v___y_1695_);
                v___x_1704_ = leanh::lean_apply_9(
                    v_a_1693_,
                    v___y_1695_,
                    v___y_1696_,
                    v___y_1697_,
                    v___y_1698_,
                    v___y_1699_,
                    v___y_1700_,
                    v___y_1701_,
                    v___y_1702_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1704_) == 0 {
                    v_a_1705_ = leanh::lean_ctor_get(v___x_1704_, 0);
                    v_isSharedCheck_1713_ = (!leanh::lean_is_exclusive(v___x_1704_)) as u8;
                    if v_isSharedCheck_1713_ == 0 {
                        v___x_1707_ = v___x_1704_;
                        v_isShared_1708_ = v_isSharedCheck_1713_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1705_);
                        leanh::lean_dec(v___x_1704_);
                        v___x_1707_ = leanh::lean_box(0);
                        v_isShared_1708_ = v_isSharedCheck_1713_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_f_1694_);
                    v_a_1714_ = leanh::lean_ctor_get(v___x_1704_, 0);
                    v_isSharedCheck_1721_ = (!leanh::lean_is_exclusive(v___x_1704_)) as u8;
                    if v_isSharedCheck_1721_ == 0 {
                        v___x_1716_ = v___x_1704_;
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1714_);
                        leanh::lean_dec(v___x_1704_);
                        v___x_1716_ = leanh::lean_box(0);
                        v_isShared_1717_ = v_isSharedCheck_1721_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1709_ = leanh::lean_apply_1(v_f_1694_, v_a_1705_);
                if v_isShared_1708_ == 0 {
                    leanh::lean_ctor_set(v___x_1707_, 0, v___x_1709_);
                    v___x_1711_ = v___x_1707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1712_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1709_);
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
                    v_reuseFailAlloc_1720_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1720_, 0, v_a_1714_);
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
    mut v_a_1722_: *mut leanh::LeanObject,
    mut v_f_1723_: *mut leanh::LeanObject,
    mut v___y_1724_: *mut leanh::LeanObject,
    mut v___y_1725_: *mut leanh::LeanObject,
    mut v___y_1726_: *mut leanh::LeanObject,
    mut v___y_1727_: *mut leanh::LeanObject,
    mut v___y_1728_: *mut leanh::LeanObject,
    mut v___y_1729_: *mut leanh::LeanObject,
    mut v___y_1730_: *mut leanh::LeanObject,
    mut v___y_1731_: *mut leanh::LeanObject,
    mut v___y_1732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1733_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_1722_, v_f_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
    leanh::lean_dec(v___y_1731_);
    leanh::lean_dec_ref(v___y_1730_);
    leanh::lean_dec(v___y_1729_);
    leanh::lean_dec_ref(v___y_1728_);
    leanh::lean_dec(v___y_1727_);
    leanh::lean_dec_ref(v___y_1726_);
    leanh::lean_dec(v___y_1725_);
    leanh::lean_dec_ref(v___y_1724_);
    return v_res_1733_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(
    mut v_f_1735_: *mut leanh::LeanObject,
    mut v_goals_1736_: *mut leanh::LeanObject,
    mut v_maxIters_1737_: *mut leanh::LeanObject,
    mut v___y_1738_: *mut leanh::LeanObject,
    mut v___y_1739_: *mut leanh::LeanObject,
    mut v___y_1740_: *mut leanh::LeanObject,
    mut v___y_1741_: *mut leanh::LeanObject,
    mut v___y_1742_: *mut leanh::LeanObject,
    mut v___y_1743_: *mut leanh::LeanObject,
    mut v___y_1744_: *mut leanh::LeanObject,
    mut v___y_1745_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1747_ =
        l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___closed__0;
    v___x_1748_ = leanh::lean_alloc_closure(l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0___boxed as *mut core::ffi::c_void, 12, 3);
    leanh::lean_closure_set(v___x_1748_, 0, v_f_1735_);
    leanh::lean_closure_set(v___x_1748_, 1, v_goals_1736_);
    leanh::lean_closure_set(v___x_1748_, 2, v_maxIters_1737_);
    v___x_1749_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v___x_1748_, v___f_1747_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
    return v___x_1749_;
}
pub unsafe fn l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0___boxed(
    mut v_f_1750_: *mut leanh::LeanObject,
    mut v_goals_1751_: *mut leanh::LeanObject,
    mut v_maxIters_1752_: *mut leanh::LeanObject,
    mut v___y_1753_: *mut leanh::LeanObject,
    mut v___y_1754_: *mut leanh::LeanObject,
    mut v___y_1755_: *mut leanh::LeanObject,
    mut v___y_1756_: *mut leanh::LeanObject,
    mut v___y_1757_: *mut leanh::LeanObject,
    mut v___y_1758_: *mut leanh::LeanObject,
    mut v___y_1759_: *mut leanh::LeanObject,
    mut v___y_1760_: *mut leanh::LeanObject,
    mut v___y_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1760_);
    leanh::lean_dec_ref(v___y_1759_);
    leanh::lean_dec(v___y_1758_);
    leanh::lean_dec_ref(v___y_1757_);
    leanh::lean_dec(v___y_1756_);
    leanh::lean_dec_ref(v___y_1755_);
    leanh::lean_dec(v___y_1754_);
    leanh::lean_dec_ref(v___y_1753_);
    return v_res_1762_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat_x27(
    mut v_stx_1769_: *mut leanh::LeanObject,
    mut v_a_1770_: *mut leanh::LeanObject,
    mut v_a_1771_: *mut leanh::LeanObject,
    mut v_a_1772_: *mut leanh::LeanObject,
    mut v_a_1773_: *mut leanh::LeanObject,
    mut v_a_1774_: *mut leanh::LeanObject,
    mut v_a_1775_: *mut leanh::LeanObject,
    mut v_a_1776_: *mut leanh::LeanObject,
    mut v_a_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1801_: u8 = 0;
    let mut v_a_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1779_ = l_Lean_Elab_Tactic_evalRepeat_x27___closed__1;
                leanh::lean_inc(v_stx_1769_);
                v___x_1780_ = l_Lean_Syntax_isOfKind(v_stx_1769_, v___x_1779_);
                if v___x_1780_ == 0 {
                    leanh::lean_dec(v_stx_1769_);
                    v___x_1781_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                    return v___x_1781_;
                } else {
                    v___x_1782_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1783_ = l_Lean_Syntax_getArg(v_stx_1769_, v___x_1782_);
                    leanh::lean_dec(v_stx_1769_);
                    v___x_1784_ = l_Lean_Elab_Tactic_evalRepeat___closed__6;
                    leanh::lean_inc(v___x_1783_);
                    v___x_1785_ = l_Lean_Syntax_isOfKind(v___x_1783_, v___x_1784_);
                    if v___x_1785_ == 0 {
                        leanh::lean_dec(v___x_1783_);
                        v___x_1786_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                        return v___x_1786_;
                    } else {
                        v___x_1787_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_1771_);
                        if leanh::lean_obj_tag(v___x_1787_) == 0 {
                            v_a_1788_ = leanh::lean_ctor_get(v___x_1787_, 0);
                            leanh::lean_inc(v_a_1788_);
                            leanh::lean_dec_ref_known(v___x_1787_, 1);
                            v___x_1789_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_evalTacticAtRaw___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                1,
                            );
                            leanh::lean_closure_set(v___x_1789_, 0, v___x_1783_);
                            v___x_1790_ = leanh::lean_unsigned_to_nat(100000);
                            v___x_1791_ = l_Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0(v___x_1789_, v_a_1788_, v___x_1790_, v_a_1770_, v_a_1771_, v_a_1772_, v_a_1773_, v_a_1774_, v_a_1775_, v_a_1776_, v_a_1777_);
                            if leanh::lean_obj_tag(v___x_1791_) == 0 {
                                v_a_1792_ = leanh::lean_ctor_get(v___x_1791_, 0);
                                leanh::lean_inc(v_a_1792_);
                                leanh::lean_dec_ref_known(v___x_1791_, 1);
                                v___x_1793_ =
                                    l_Lean_Elab_Tactic_setGoals___redArg(v_a_1792_, v_a_1771_);
                                return v___x_1793_;
                            } else {
                                v_a_1794_ = leanh::lean_ctor_get(v___x_1791_, 0);
                                v_isSharedCheck_1801_ =
                                    (!leanh::lean_is_exclusive(v___x_1791_)) as u8;
                                if v_isSharedCheck_1801_ == 0 {
                                    v___x_1796_ = v___x_1791_;
                                    v_isShared_1797_ = v_isSharedCheck_1801_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1794_);
                                    leanh::lean_dec(v___x_1791_);
                                    v___x_1796_ = leanh::lean_box(0);
                                    v_isShared_1797_ = v_isSharedCheck_1801_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_1783_);
                            v_a_1802_ = leanh::lean_ctor_get(v___x_1787_, 0);
                            v_isSharedCheck_1809_ =
                                (!leanh::lean_is_exclusive(v___x_1787_)) as u8;
                            if v_isSharedCheck_1809_ == 0 {
                                v___x_1804_ = v___x_1787_;
                                v_isShared_1805_ = v_isSharedCheck_1809_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1802_);
                                leanh::lean_dec(v___x_1787_);
                                v___x_1804_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1800_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1800_, 0, v_a_1794_);
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
                    v_reuseFailAlloc_1808_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_a_1802_);
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
    mut v_stx_1810_: *mut leanh::LeanObject,
    mut v_a_1811_: *mut leanh::LeanObject,
    mut v_a_1812_: *mut leanh::LeanObject,
    mut v_a_1813_: *mut leanh::LeanObject,
    mut v_a_1814_: *mut leanh::LeanObject,
    mut v_a_1815_: *mut leanh::LeanObject,
    mut v_a_1816_: *mut leanh::LeanObject,
    mut v_a_1817_: *mut leanh::LeanObject,
    mut v_a_1818_: *mut leanh::LeanObject,
    mut v_a_1819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_1818_);
    leanh::lean_dec_ref(v_a_1817_);
    leanh::lean_dec(v_a_1816_);
    leanh::lean_dec_ref(v_a_1815_);
    leanh::lean_dec(v_a_1814_);
    leanh::lean_dec_ref(v_a_1813_);
    leanh::lean_dec(v_a_1812_);
    leanh::lean_dec_ref(v_a_1811_);
    return v_res_1820_;
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(
    mut v_00_u03b1_1821_: *mut leanh::LeanObject,
    mut v_00_u03b2_1822_: *mut leanh::LeanObject,
    mut v_a_1823_: *mut leanh::LeanObject,
    mut v_f_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
    mut v___y_1826_: *mut leanh::LeanObject,
    mut v___y_1827_: *mut leanh::LeanObject,
    mut v___y_1828_: *mut leanh::LeanObject,
    mut v___y_1829_: *mut leanh::LeanObject,
    mut v___y_1830_: *mut leanh::LeanObject,
    mut v___y_1831_: *mut leanh::LeanObject,
    mut v___y_1832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1834_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___redArg(v_a_1823_, v_f_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
    return v___x_1834_;
}
pub unsafe fn l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1___boxed(
    mut v_00_u03b1_1835_: *mut leanh::LeanObject,
    mut v_00_u03b2_1836_: *mut leanh::LeanObject,
    mut v_a_1837_: *mut leanh::LeanObject,
    mut v_f_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
    mut v___y_1844_: *mut leanh::LeanObject,
    mut v___y_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1848_ = l_Functor_mapRev___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__1(v_00_u03b1_1835_, v_00_u03b2_1836_, v_a_1837_, v_f_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_, v___y_1846_);
    leanh::lean_dec(v___y_1846_);
    leanh::lean_dec_ref(v___y_1845_);
    leanh::lean_dec(v___y_1844_);
    leanh::lean_dec_ref(v___y_1843_);
    leanh::lean_dec(v___y_1842_);
    leanh::lean_dec_ref(v___y_1841_);
    leanh::lean_dec(v___y_1840_);
    leanh::lean_dec_ref(v___y_1839_);
    return v_res_1848_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1849_: *mut leanh::LeanObject,
    mut v_x_1850_: *mut leanh::LeanObject,
    mut v___y_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
    mut v___y_1855_: *mut leanh::LeanObject,
    mut v___y_1856_: *mut leanh::LeanObject,
    mut v___y_1857_: *mut leanh::LeanObject,
    mut v___y_1858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1860_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___redArg(v_x_1850_, v___y_1851_, v___y_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_, v___y_1857_, v___y_1858_);
    return v___x_1860_;
}
pub unsafe fn l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1861_: *mut leanh::LeanObject,
    mut v_x_1862_: *mut leanh::LeanObject,
    mut v___y_1863_: *mut leanh::LeanObject,
    mut v___y_1864_: *mut leanh::LeanObject,
    mut v___y_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
    mut v___y_1869_: *mut leanh::LeanObject,
    mut v___y_1870_: *mut leanh::LeanObject,
    mut v___y_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Lean_observing_x3f___at___00__private_Lean_Meta_Tactic_Repeat_0__Lean_Meta_repeat_x27Core_go___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1861_, v_x_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
    leanh::lean_dec(v___y_1870_);
    leanh::lean_dec_ref(v___y_1869_);
    leanh::lean_dec(v___y_1868_);
    leanh::lean_dec_ref(v___y_1867_);
    leanh::lean_dec(v___y_1866_);
    leanh::lean_dec_ref(v___y_1865_);
    leanh::lean_dec(v___y_1864_);
    leanh::lean_dec_ref(v___y_1863_);
    return v_res_1872_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(
    mut v_mvarId_1873_: *mut leanh::LeanObject,
    mut v___y_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
    mut v___y_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
    mut v___y_1881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___redArg(v_mvarId_1873_, v___y_1879_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2___boxed(
    mut v_mvarId_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
    mut v___y_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
    mut v___y_1893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1894_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2(v_mvarId_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_);
    leanh::lean_dec(v___y_1892_);
    leanh::lean_dec_ref(v___y_1891_);
    leanh::lean_dec(v___y_1890_);
    leanh::lean_dec_ref(v___y_1889_);
    leanh::lean_dec(v___y_1888_);
    leanh::lean_dec_ref(v___y_1887_);
    leanh::lean_dec(v___y_1886_);
    leanh::lean_dec_ref(v___y_1885_);
    leanh::lean_dec(v_mvarId_1884_);
    return v_res_1894_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b2_1895_: *mut leanh::LeanObject,
    mut v_x_1896_: *mut leanh::LeanObject,
    mut v_x_1897_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1898_: u8 = 0;
    v___x_1898_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___redArg(v_x_1896_, v_x_1897_);
    return v___x_1898_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_1899_: *mut leanh::LeanObject,
    mut v_x_1900_: *mut leanh::LeanObject,
    mut v_x_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1902_: u8 = 0;
    let mut v_r_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1902_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6(v_00_u03b2_1899_, v_x_1900_, v_x_1901_);
    leanh::lean_dec(v_x_1901_);
    leanh::lean_dec_ref(v_x_1900_);
    v_r_1903_ = leanh::lean_box((v_res_1902_) as usize);
    return v_r_1903_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(
    mut v_00_u03b2_1904_: *mut leanh::LeanObject,
    mut v_x_1905_: *mut leanh::LeanObject,
    mut v_x_1906_: usize,
    mut v_x_1907_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1908_: u8 = 0;
    v___x_1908_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___redArg(v_x_1905_, v_x_1906_, v_x_1907_);
    return v___x_1908_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7___boxed(
    mut v_00_u03b2_1909_: *mut leanh::LeanObject,
    mut v_x_1910_: *mut leanh::LeanObject,
    mut v_x_1911_: *mut leanh::LeanObject,
    mut v_x_1912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5520__boxed_1913_: usize = 0;
    let mut v_res_1914_: u8 = 0;
    let mut v_r_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_5520__boxed_1913_ = leanh::lean_unbox_usize(v_x_1911_);
    leanh::lean_dec(v_x_1911_);
    v_res_1914_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7(v_00_u03b2_1909_, v_x_1910_, v_x_5520__boxed_1913_, v_x_1912_);
    leanh::lean_dec(v_x_1912_);
    leanh::lean_dec_ref(v_x_1910_);
    v_r_1915_ = leanh::lean_box((v_res_1914_) as usize);
    return v_r_1915_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(
    mut v_00_u03b2_1916_: *mut leanh::LeanObject,
    mut v_keys_1917_: *mut leanh::LeanObject,
    mut v_vals_1918_: *mut leanh::LeanObject,
    mut v_heq_1919_: *mut leanh::LeanObject,
    mut v_i_1920_: *mut leanh::LeanObject,
    mut v_k_1921_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1922_: u8 = 0;
    v___x_1922_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___redArg(v_keys_1917_, v_i_1920_, v_k_1921_);
    return v___x_1922_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9___boxed(
    mut v_00_u03b2_1923_: *mut leanh::LeanObject,
    mut v_keys_1924_: *mut leanh::LeanObject,
    mut v_vals_1925_: *mut leanh::LeanObject,
    mut v_heq_1926_: *mut leanh::LeanObject,
    mut v_i_1927_: *mut leanh::LeanObject,
    mut v_k_1928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1929_: u8 = 0;
    let mut v_r_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0_spec__2_spec__6_spec__7_spec__9(v_00_u03b2_1923_, v_keys_1924_, v_vals_1925_, v_heq_1926_, v_i_1927_, v_k_1928_);
    leanh::lean_dec(v_k_1928_);
    leanh::lean_dec_ref(v_vals_1925_);
    leanh::lean_dec_ref(v_keys_1924_);
    v_r_1930_ = leanh::lean_box((v_res_1929_) as usize);
    return v_r_1930_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1()
-> *mut leanh::LeanObject {
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1938_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1939_ = l_Lean_Elab_Tactic_evalRepeat_x27___closed__1;
    v___x_1940_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1;
    v___x_1941_ = leanh::lean_alloc_closure(
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
    mut v_a_1943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1944_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
    return v_res_1944_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1971_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1___closed__1;
    v___x_1972_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___closed__6;
    v___x_1973_ = l_Lean_addBuiltinDeclarationRanges(v___x_1971_, v___x_1972_);
    return v___x_1973_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3___boxed(
    mut v_a_1974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
    return v_res_1975_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(
    mut v_msgData_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1982_ = lean_st_ref_get(v___y_1980_);
    v_env_1983_ = leanh::lean_ctor_get(v___x_1982_, 0);
    leanh::lean_inc_ref(v_env_1983_);
    leanh::lean_dec(v___x_1982_);
    v___x_1984_ = lean_st_ref_get(v___y_1978_);
    v_mctx_1985_ = leanh::lean_ctor_get(v___x_1984_, 0);
    leanh::lean_inc_ref(v_mctx_1985_);
    leanh::lean_dec(v___x_1984_);
    v_lctx_1986_ = leanh::lean_ctor_get(v___y_1977_, 2);
    v_options_1987_ = leanh::lean_ctor_get(v___y_1979_, 2);
    leanh::lean_inc_ref(v_options_1987_);
    leanh::lean_inc_ref(v_lctx_1986_);
    v___x_1988_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1988_, 0, v_env_1983_);
    leanh::lean_ctor_set(v___x_1988_, 1, v_mctx_1985_);
    leanh::lean_ctor_set(v___x_1988_, 2, v_lctx_1986_);
    leanh::lean_ctor_set(v___x_1988_, 3, v_options_1987_);
    v___x_1989_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1989_, 0, v___x_1988_);
    leanh::lean_ctor_set(v___x_1989_, 1, v_msgData_1976_);
    v___x_1990_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1990_, 0, v___x_1989_);
    return v___x_1990_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
    mut v___y_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1997_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msgData_1991_, v___y_1992_, v___y_1993_, v___y_1994_, v___y_1995_);
    leanh::lean_dec(v___y_1995_);
    leanh::lean_dec_ref(v___y_1994_);
    leanh::lean_dec(v___y_1993_);
    leanh::lean_dec_ref(v___y_1992_);
    return v_res_1997_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(
    mut v_msg_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2009_: u8 = 0;
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2014_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2004_ = leanh::lean_ctor_get(v___y_2001_, 5);
                v___x_2005_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0_spec__1(v_msg_1998_, v___y_1999_, v___y_2000_, v___y_2001_, v___y_2002_);
                v_a_2006_ = leanh::lean_ctor_get(v___x_2005_, 0);
                v_isSharedCheck_2014_ = (!leanh::lean_is_exclusive(v___x_2005_)) as u8;
                if v_isSharedCheck_2014_ == 0 {
                    v___x_2008_ = v___x_2005_;
                    v_isShared_2009_ = v_isSharedCheck_2014_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2006_);
                    leanh::lean_dec(v___x_2005_);
                    v___x_2008_ = leanh::lean_box(0);
                    v_isShared_2009_ = v_isSharedCheck_2014_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2004_);
                v___x_2010_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2010_, 0, v_ref_2004_);
                leanh::lean_ctor_set(v___x_2010_, 1, v_a_2006_);
                if v_isShared_2009_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2008_, 1);
                    leanh::lean_ctor_set(v___x_2008_, 0, v___x_2010_);
                    v___x_2012_ = v___x_2008_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2013_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2013_, 0, v___x_2010_);
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
    mut v_msg_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
    mut v___y_2018_: *mut leanh::LeanObject,
    mut v___y_2019_: *mut leanh::LeanObject,
    mut v___y_2020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2021_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_2015_, v___y_2016_, v___y_2017_, v___y_2018_, v___y_2019_);
    leanh::lean_dec(v___y_2019_);
    leanh::lean_dec_ref(v___y_2018_);
    leanh::lean_dec(v___y_2017_);
    leanh::lean_dec_ref(v___y_2016_);
    return v_res_2021_;
}
pub unsafe fn _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2023_ =
        l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__0;
    v___x_2024_ = l_Lean_stringToMessageData(v___x_2023_);
    return v___x_2024_;
}
pub unsafe fn l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(
    mut v_f_2025_: *mut leanh::LeanObject,
    mut v_goals_2026_: *mut leanh::LeanObject,
    mut v_maxIters_2027_: *mut leanh::LeanObject,
    mut v___y_2028_: *mut leanh::LeanObject,
    mut v___y_2029_: *mut leanh::LeanObject,
    mut v___y_2030_: *mut leanh::LeanObject,
    mut v___y_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
    mut v___y_2033_: *mut leanh::LeanObject,
    mut v___y_2034_: *mut leanh::LeanObject,
    mut v___y_2035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v_fst_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v_snd_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2050_: u8 = 0;
    let mut v_a_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2054_: u8 = 0;
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2037_ = l_Lean_Meta_repeat_x27Core___at___00Lean_Meta_repeat_x27___at___00Lean_Elab_Tactic_evalRepeat_x27_spec__0_spec__0(v_f_2025_, v_goals_2026_, v_maxIters_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_);
                if leanh::lean_obj_tag(v___x_2037_) == 0 {
                    v_a_2038_ = leanh::lean_ctor_get(v___x_2037_, 0);
                    v_isSharedCheck_2050_ = (!leanh::lean_is_exclusive(v___x_2037_)) as u8;
                    if v_isSharedCheck_2050_ == 0 {
                        v___x_2040_ = v___x_2037_;
                        v_isShared_2041_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2038_);
                        leanh::lean_dec(v___x_2037_);
                        v___x_2040_ = leanh::lean_box(0);
                        v_isShared_2041_ = v_isSharedCheck_2050_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2051_ = leanh::lean_ctor_get(v___x_2037_, 0);
                    v_isSharedCheck_2058_ = (!leanh::lean_is_exclusive(v___x_2037_)) as u8;
                    if v_isSharedCheck_2058_ == 0 {
                        v___x_2053_ = v___x_2037_;
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2051_);
                        leanh::lean_dec(v___x_2037_);
                        v___x_2053_ = leanh::lean_box(0);
                        v_isShared_2054_ = v_isSharedCheck_2058_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2042_ = leanh::lean_ctor_get(v_a_2038_, 0);
                v___x_2043_ = (leanh::lean_unbox(v_fst_2042_) as u8);
                if v___x_2043_ == 1 {
                    v_snd_2044_ = leanh::lean_ctor_get(v_a_2038_, 1);
                    leanh::lean_inc(v_snd_2044_);
                    leanh::lean_dec(v_a_2038_);
                    if v_isShared_2041_ == 0 {
                        leanh::lean_ctor_set(v___x_2040_, 0, v_snd_2044_);
                        v___x_2046_ = v___x_2040_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2047_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_snd_2044_);
                        v___x_2046_ = v_reuseFailAlloc_2047_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2040_);
                    leanh::lean_dec(v_a_2038_);
                    v___x_2048_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1_once), _init_l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0___closed__1);
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
                    v_reuseFailAlloc_2057_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
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
    mut v_f_2059_: *mut leanh::LeanObject,
    mut v_goals_2060_: *mut leanh::LeanObject,
    mut v_maxIters_2061_: *mut leanh::LeanObject,
    mut v___y_2062_: *mut leanh::LeanObject,
    mut v___y_2063_: *mut leanh::LeanObject,
    mut v___y_2064_: *mut leanh::LeanObject,
    mut v___y_2065_: *mut leanh::LeanObject,
    mut v___y_2066_: *mut leanh::LeanObject,
    mut v___y_2067_: *mut leanh::LeanObject,
    mut v___y_2068_: *mut leanh::LeanObject,
    mut v___y_2069_: *mut leanh::LeanObject,
    mut v___y_2070_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2069_);
    leanh::lean_dec_ref(v___y_2068_);
    leanh::lean_dec(v___y_2067_);
    leanh::lean_dec_ref(v___y_2066_);
    leanh::lean_dec(v___y_2065_);
    leanh::lean_dec_ref(v___y_2064_);
    leanh::lean_dec(v___y_2063_);
    leanh::lean_dec_ref(v___y_2062_);
    return v_res_2071_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalRepeat1_x27(
    mut v_stx_2078_: *mut leanh::LeanObject,
    mut v_a_2079_: *mut leanh::LeanObject,
    mut v_a_2080_: *mut leanh::LeanObject,
    mut v_a_2081_: *mut leanh::LeanObject,
    mut v_a_2082_: *mut leanh::LeanObject,
    mut v_a_2083_: *mut leanh::LeanObject,
    mut v_a_2084_: *mut leanh::LeanObject,
    mut v_a_2085_: *mut leanh::LeanObject,
    mut v_a_2086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: u8 = 0;
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: u8 = 0;
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2106_: u8 = 0;
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2110_: u8 = 0;
    let mut v_a_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2088_ = l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1;
                leanh::lean_inc(v_stx_2078_);
                v___x_2089_ = l_Lean_Syntax_isOfKind(v_stx_2078_, v___x_2088_);
                if v___x_2089_ == 0 {
                    leanh::lean_dec(v_stx_2078_);
                    v___x_2090_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                    return v___x_2090_;
                } else {
                    v___x_2091_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2092_ = l_Lean_Syntax_getArg(v_stx_2078_, v___x_2091_);
                    leanh::lean_dec(v_stx_2078_);
                    v___x_2093_ = l_Lean_Elab_Tactic_evalRepeat___closed__6;
                    leanh::lean_inc(v___x_2092_);
                    v___x_2094_ = l_Lean_Syntax_isOfKind(v___x_2092_, v___x_2093_);
                    if v___x_2094_ == 0 {
                        leanh::lean_dec(v___x_2092_);
                        v___x_2095_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_evalRepeat_spec__0___redArg();
                        return v___x_2095_;
                    } else {
                        v___x_2096_ = l_Lean_Elab_Tactic_getGoals___redArg(v_a_2080_);
                        if leanh::lean_obj_tag(v___x_2096_) == 0 {
                            v_a_2097_ = leanh::lean_ctor_get(v___x_2096_, 0);
                            leanh::lean_inc(v_a_2097_);
                            leanh::lean_dec_ref_known(v___x_2096_, 1);
                            v___x_2098_ = leanh::lean_alloc_closure(
                                l_Lean_Elab_Tactic_evalTacticAtRaw___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                1,
                            );
                            leanh::lean_closure_set(v___x_2098_, 0, v___x_2092_);
                            v___x_2099_ = leanh::lean_unsigned_to_nat(100000);
                            v___x_2100_ = l_Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0(v___x_2098_, v_a_2097_, v___x_2099_, v_a_2079_, v_a_2080_, v_a_2081_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
                            if leanh::lean_obj_tag(v___x_2100_) == 0 {
                                v_a_2101_ = leanh::lean_ctor_get(v___x_2100_, 0);
                                leanh::lean_inc(v_a_2101_);
                                leanh::lean_dec_ref_known(v___x_2100_, 1);
                                v___x_2102_ =
                                    l_Lean_Elab_Tactic_setGoals___redArg(v_a_2101_, v_a_2080_);
                                return v___x_2102_;
                            } else {
                                v_a_2103_ = leanh::lean_ctor_get(v___x_2100_, 0);
                                v_isSharedCheck_2110_ =
                                    (!leanh::lean_is_exclusive(v___x_2100_)) as u8;
                                if v_isSharedCheck_2110_ == 0 {
                                    v___x_2105_ = v___x_2100_;
                                    v_isShared_2106_ = v_isSharedCheck_2110_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2103_);
                                    leanh::lean_dec(v___x_2100_);
                                    v___x_2105_ = leanh::lean_box(0);
                                    v_isShared_2106_ = v_isSharedCheck_2110_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_2092_);
                            v_a_2111_ = leanh::lean_ctor_get(v___x_2096_, 0);
                            v_isSharedCheck_2118_ =
                                (!leanh::lean_is_exclusive(v___x_2096_)) as u8;
                            if v_isSharedCheck_2118_ == 0 {
                                v___x_2113_ = v___x_2096_;
                                v_isShared_2114_ = v_isSharedCheck_2118_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2111_);
                                leanh::lean_dec(v___x_2096_);
                                v___x_2113_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2109_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
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
                    v_reuseFailAlloc_2117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
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
    mut v_stx_2119_: *mut leanh::LeanObject,
    mut v_a_2120_: *mut leanh::LeanObject,
    mut v_a_2121_: *mut leanh::LeanObject,
    mut v_a_2122_: *mut leanh::LeanObject,
    mut v_a_2123_: *mut leanh::LeanObject,
    mut v_a_2124_: *mut leanh::LeanObject,
    mut v_a_2125_: *mut leanh::LeanObject,
    mut v_a_2126_: *mut leanh::LeanObject,
    mut v_a_2127_: *mut leanh::LeanObject,
    mut v_a_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_a_2127_);
    leanh::lean_dec_ref(v_a_2126_);
    leanh::lean_dec(v_a_2125_);
    leanh::lean_dec_ref(v_a_2124_);
    leanh::lean_dec(v_a_2123_);
    leanh::lean_dec_ref(v_a_2122_);
    leanh::lean_dec(v_a_2121_);
    leanh::lean_dec_ref(v_a_2120_);
    return v_res_2129_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(
    mut v_00_u03b1_2130_: *mut leanh::LeanObject,
    mut v_msg_2131_: *mut leanh::LeanObject,
    mut v___y_2132_: *mut leanh::LeanObject,
    mut v___y_2133_: *mut leanh::LeanObject,
    mut v___y_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
    mut v___y_2136_: *mut leanh::LeanObject,
    mut v___y_2137_: *mut leanh::LeanObject,
    mut v___y_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2141_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___redArg(v_msg_2131_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
    return v___x_2141_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0___boxed(
    mut v_00_u03b1_2142_: *mut leanh::LeanObject,
    mut v_msg_2143_: *mut leanh::LeanObject,
    mut v___y_2144_: *mut leanh::LeanObject,
    mut v___y_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
    mut v___y_2147_: *mut leanh::LeanObject,
    mut v___y_2148_: *mut leanh::LeanObject,
    mut v___y_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2153_ = l_Lean_throwError___at___00Lean_Meta_repeat1_x27___at___00Lean_Elab_Tactic_evalRepeat1_x27_spec__0_spec__0(v_00_u03b1_2142_, v_msg_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_);
    leanh::lean_dec(v___y_2151_);
    leanh::lean_dec_ref(v___y_2150_);
    leanh::lean_dec(v___y_2149_);
    leanh::lean_dec_ref(v___y_2148_);
    leanh::lean_dec(v___y_2147_);
    leanh::lean_dec_ref(v___y_2146_);
    leanh::lean_dec(v___y_2145_);
    leanh::lean_dec_ref(v___y_2144_);
    return v_res_2153_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1()
-> *mut leanh::LeanObject {
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_2162_ = l_Lean_Elab_Tactic_evalRepeat1_x27___closed__1;
    v___x_2163_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1;
    v___x_2164_ = leanh::lean_alloc_closure(
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
    mut v_a_2166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2167_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
    return v_res_2167_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3()
-> *mut leanh::LeanObject {
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2194_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1___closed__1;
    v___x_2195_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___closed__6;
    v___x_2196_ = l_Lean_addBuiltinDeclarationRanges(v___x_2194_, v___x_2195_);
    return v___x_2196_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3___boxed(
    mut v_a_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2198_ = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
    return v_res_2198_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Repeat(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat___regBuiltin_Lean_Elab_Tactic_evalRepeat__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat_x27_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Repeat_0__Lean_Elab_Tactic_evalRepeat1_x27___regBuiltin_Lean_Elab_Tactic_evalRepeat1_x27_declRange__3();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Repeat(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Repeat(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Repeat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Repeat(builtin);
}