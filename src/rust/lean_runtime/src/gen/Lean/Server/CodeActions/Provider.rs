// Lean compiler output
// Module: Lean.Server.CodeActions.Provider
// Imports: Std.Data.Iterators.Producers.Range Std.Data.Iterators.Combinators.StepSize Lean.Elab.BuiltinTerm Lean.Elab.BuiltinNotation Lean.Server.CodeActions.Attr
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_getTailInfo;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_getKind,
    l_Lean_Syntax_getNumArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_instInhabitedForall___redArg___lam__0___boxed,
};
use crate::r#gen::Init::System::IO::l_instInhabitedEIO___aux__1___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_FileMap_lspPosToUtf8Pos;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Elab::BuiltinNotation::{
    initialize_Lean_Elab_BuiltinNotation, runtime_initialize_Lean_Elab_BuiltinNotation,
};
use crate::r#gen::Lean::Elab::BuiltinTerm::{
    initialize_Lean_Elab_BuiltinTerm, runtime_initialize_Lean_Elab_BuiltinTerm,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_Info_updateContext_x3f, l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f,
};
use crate::r#gen::Lean::Environment::l_Lean_PersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Server::CodeActions::Attr::{
    initialize_Lean_Server_CodeActions_Attr, l_Lean_CodeAction_cmdCodeActionExt,
    l_Lean_CodeAction_holeCodeActionExt, l_Lean_CodeAction_instInhabitedCommandCodeActions_default,
    runtime_initialize_Lean_Server_CodeActions_Attr,
};
use crate::r#gen::Lean::Server::CodeActions::Basic::l_Lean_Server_addBuiltinCodeActionProvider;
use crate::r#gen::Lean::Server::InfoUtils::{
    l_Lean_Elab_Info_stx, l_Lean_Elab_InfoTree_foldInfo___redArg,
    l_Lean_Elab_InfoTree_foldInfoTree___redArg,
};
use crate::r#gen::Lean::Server::Requests::l_Lean_Server_instInhabitedRequestError_default;
use crate::r#gen::Lean::Server::Snapshots::{
    l_Lean_Server_Snapshots_Snapshot_env, l_Lean_Server_Snapshots_Snapshot_infoTree,
};
use crate::r#gen::Lean::Syntax::{l_Lean_Syntax_getRange_x3f, l_Lean_Syntax_instBEqRange_beq};
use crate::r#gen::Std::Data::Iterators::Combinators::StepSize::{
    initialize_Std_Data_Iterators_Combinators_StepSize,
    runtime_initialize_Std_Data_Iterators_Combinators_StepSize,
};
use crate::r#gen::Std::Data::Iterators::Producers::Range::{
    initialize_Std_Data_Iterators_Producers_Range,
    runtime_initialize_Std_Data_Iterators_Producers_Range,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
    lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_6, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value: LeanStringObject<
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value: LeanStringObject<
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
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value: LeanStringObject<
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value: LeanStringObject<
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
    m_data: [101, 108, 97, 98, 72, 111, 108, 101, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value)
        as *mut LeanObject;
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
            as *mut LeanObject,
        7892421401833366012 as *mut LeanObject,
    ],
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__3_value)
                as *mut LeanObject,
            11340967426965104390 as *mut LeanObject,
        ],
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value: LeanStringObject<
    18,
> = LeanStringObject {
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
        101, 108, 97, 98, 83, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0,
    ],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value)
        as *mut LeanObject;
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
            as *mut LeanObject,
        7892421401833366012 as *mut LeanObject,
    ],
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__5_value)
                as *mut LeanObject,
            8403575154271798838 as *mut LeanObject,
        ],
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value: LeanStringObject<
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
    m_data: [101, 108, 97, 98, 83, 111, 114, 114, 121, 0],
};
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value)
        as *mut LeanObject;
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_0: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value)
            as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__1_value)
            as *mut LeanObject,
        11510100434945111860 as *mut LeanObject,
    ],
};
static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__2_value)
            as *mut LeanObject,
        7892421401833366012 as *mut LeanObject,
    ],
};
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__7_value)
                as *mut LeanObject,
            6267058134344042428 as *mut LeanObject,
        ],
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__8_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__6_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__9_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__4_value)
                as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__10_value
            ) as *mut LeanObject,
        ],
    };
static mut l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_CodeAction_holeCodeActionProvider___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_CodeAction_holeCodeActionProvider___closed__3_value: LeanArrayObject<0> =
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
static mut l_Lean_CodeAction_holeCodeActionProvider___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___closed__3_value)
        as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [104, 111, 108, 101, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value) as *mut LeanObject,1630946840184265901 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__1_value) as *mut LeanObject,2550652980631965832 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__2_value) as *mut LeanObject,8504843326314613972 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 66, 114, 97, 99, 107, 101, 116, 101, 100, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__0_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__1_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__5_value) as *mut LeanObject,10468396288943149198 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1_value) as *mut LeanObject;
static mut l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0_value: LeanStringObject<33> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 83, 101, 114, 118, 101, 114, 46, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 115, 46, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [76, 101, 97, 110, 46, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 46, 99, 109, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_CodeAction_cmdCodeActionProvider___closed__2_value: LeanArrayObject<0> =
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
static mut l_Lean_CodeAction_cmdCodeActionProvider___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_CodeAction_cmdCodeActionProvider___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [99, 109, 100, 67, 111, 100, 101, 65, 99, 116, 105, 111, 110, 80, 114, 111, 118, 105, 100, 101, 114, 0]};
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__0_value) as *mut LeanObject,1630946840184265901 as *mut LeanObject] };
pub static l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__0_value) as *mut LeanObject,890343562233056736 as *mut LeanObject] };
static mut l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(
    mut v___y_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_doc_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    v_doc_1368_ = lean_ctor_get(v___y_1366_, 1);
    lean_inc_ref(v_doc_1368_);
    v___x_1369_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1369_, 0, v_doc_1368_);
    return v___x_1369_;
}
pub unsafe fn l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0___boxed(
    mut v___y_1370_: *mut LeanObject,
    mut v___y_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1372_: *mut LeanObject = core::ptr::null_mut();
    v_res_1372_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(
            v___y_1370_,
        );
    lean_dec_ref(v___y_1370_);
    return v_res_1372_;
}
pub unsafe fn l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(
    mut v_a_1373_: *mut LeanObject,
    mut v_x_1374_: *mut LeanObject,
) -> u8 {
    let mut v___x_1375_: u8 = 0;
    let mut v_head_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1374_) == 0 {
                    v___x_1375_ = 0;
                    return v___x_1375_;
                } else {
                    v_head_1376_ = lean_ctor_get(v_x_1374_, 0);
                    v_tail_1377_ = lean_ctor_get(v_x_1374_, 1);
                    v___x_1378_ = lean_name_eq(v_a_1373_, v_head_1376_);
                    if v___x_1378_ == 0 {
                        v_x_1374_ = v_tail_1377_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1378_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1___boxed(
    mut v_a_1380_: *mut LeanObject,
    mut v_x_1381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1382_: u8 = 0;
    let mut v_r_1383_: *mut LeanObject = core::ptr::null_mut();
    v_res_1382_ =
        l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(v_a_1380_, v_x_1381_);
    lean_dec(v_x_1381_);
    lean_dec(v_a_1380_);
    v_r_1383_ = lean_box((v_res_1382_) as usize);
    return v_r_1383_;
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider___lam__0(
    mut v___x_1414_: *mut LeanObject,
    mut v___x_1415_: *mut LeanObject,
    mut v_ctx_1416_: *mut LeanObject,
    mut v_info_1417_: *mut LeanObject,
    mut v_result_1418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: u8 = 0;
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toElabInfo_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elaborator_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: u8 = 0;
    let mut v___x_1434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_info_1417_) == 1 {
                    v_i_1419_ = lean_ctor_get(v_info_1417_, 0);
                    v_toElabInfo_1424_ = lean_ctor_get(v_i_1419_, 0);
                    v_elaborator_1425_ = lean_ctor_get(v_toElabInfo_1424_, 0);
                    v_stx_1426_ = lean_ctor_get(v_toElabInfo_1424_, 1);
                    v___x_1427_ = l_Lean_CodeAction_holeCodeActionProvider___lam__0___closed__11;
                    v___x_1428_ =
                        l_List_elem___at___00Lean_CodeAction_holeCodeActionProvider_spec__1(
                            v_elaborator_1425_,
                            v___x_1427_,
                        );
                    if v___x_1428_ == 0 {
                        lean_dec_ref(v_ctx_1416_);
                        return v_result_1418_;
                    } else {
                        v___x_1429_ = l_Lean_Syntax_getPos_x3f(v_stx_1426_, v___x_1428_);
                        if lean_obj_tag(v___x_1429_) == 1 {
                            v_val_1430_ = lean_ctor_get(v___x_1429_, 0);
                            lean_inc(v_val_1430_);
                            lean_dec_ref_known(v___x_1429_, 1);
                            v___x_1431_ = l_Lean_Syntax_getTailPos_x3f(v_stx_1426_, v___x_1428_);
                            if lean_obj_tag(v___x_1431_) == 1 {
                                v_val_1432_ = lean_ctor_get(v___x_1431_, 0);
                                lean_inc(v_val_1432_);
                                lean_dec_ref_known(v___x_1431_, 1);
                                v___x_1433_ = lean_nat_dec_le(v_val_1430_, v___x_1414_);
                                lean_dec(v_val_1430_);
                                if v___x_1433_ == 0 {
                                    lean_dec(v_val_1432_);
                                    v___y_1421_ = v___x_1433_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1434_ = lean_nat_dec_le(v___x_1415_, v_val_1432_);
                                    lean_dec(v_val_1432_);
                                    v___y_1421_ = v___x_1434_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_1431_);
                                lean_dec(v_val_1430_);
                                lean_dec_ref(v_ctx_1416_);
                                return v_result_1418_;
                            }
                        } else {
                            lean_dec(v___x_1429_);
                            lean_dec_ref(v_ctx_1416_);
                            return v_result_1418_;
                        }
                    }
                } else {
                    lean_dec_ref(v_ctx_1416_);
                    return v_result_1418_;
                }
            }
            1 => {
                if v___y_1421_ == 0 {
                    lean_dec_ref(v_ctx_1416_);
                    return v_result_1418_;
                } else {
                    lean_inc_ref(v_i_1419_);
                    v___x_1422_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1422_, 0, v_ctx_1416_);
                    lean_ctor_set(v___x_1422_, 1, v_i_1419_);
                    v___x_1423_ = lean_array_push(v_result_1418_, v___x_1422_);
                    return v___x_1423_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed(
    mut v___x_1435_: *mut LeanObject,
    mut v___x_1436_: *mut LeanObject,
    mut v_ctx_1437_: *mut LeanObject,
    mut v_info_1438_: *mut LeanObject,
    mut v_result_1439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1440_: *mut LeanObject = core::ptr::null_mut();
    v_res_1440_ = l_Lean_CodeAction_holeCodeActionProvider___lam__0(
        v___x_1435_,
        v___x_1436_,
        v_ctx_1437_,
        v_info_1438_,
        v_result_1439_,
    );
    lean_dec_ref(v_info_1438_);
    lean_dec(v___x_1436_);
    lean_dec(v___x_1435_);
    return v_res_1440_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(
    mut v_params_1441_: *mut LeanObject,
    mut v_snap_1442_: *mut LeanObject,
    mut v_fst_1443_: *mut LeanObject,
    mut v_snd_1444_: *mut LeanObject,
    mut v_as_1445_: *mut LeanObject,
    mut v_i_1446_: usize,
    mut v_stop_1447_: usize,
    mut v_b_1448_: *mut LeanObject,
    mut v___y_1449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: usize = 0;
    let mut v___x_1454_: usize = 0;
    let mut v___x_1456_: u8 = 0;
    let mut v___x_1833__overap_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1456_ = lean_usize_dec_eq(v_i_1446_, v_stop_1447_);
                if v___x_1456_ == 0 {
                    v___x_1833__overap_1457_ = lean_array_uget_borrowed(v_as_1445_, v_i_1446_);
                    lean_inc(v___x_1833__overap_1457_);
                    lean_inc_ref(v___y_1449_);
                    lean_inc_ref(v_snd_1444_);
                    lean_inc_ref(v_fst_1443_);
                    lean_inc_ref(v_snap_1442_);
                    lean_inc_ref(v_params_1441_);
                    v___x_1458_ = lean_apply_6(
                        v___x_1833__overap_1457_,
                        v_params_1441_,
                        v_snap_1442_,
                        v_fst_1443_,
                        v_snd_1444_,
                        v___y_1449_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1458_) == 0 {
                        v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
                        lean_inc(v_a_1459_);
                        lean_dec_ref_known(v___x_1458_, 1);
                        v___x_1460_ = l_Array_append___redArg(v_b_1448_, v_a_1459_);
                        lean_dec(v_a_1459_);
                        v_a_1452_ = v___x_1460_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_b_1448_);
                        if lean_obj_tag(v___x_1458_) == 0 {
                            v_a_1461_ = lean_ctor_get(v___x_1458_, 0);
                            lean_inc(v_a_1461_);
                            lean_dec_ref_known(v___x_1458_, 1);
                            v_a_1452_ = v_a_1461_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_snd_1444_);
                            lean_dec_ref(v_fst_1443_);
                            lean_dec_ref(v_snap_1442_);
                            lean_dec_ref(v_params_1441_);
                            return v___x_1458_;
                        }
                    }
                } else {
                    lean_dec_ref(v_snd_1444_);
                    lean_dec_ref(v_fst_1443_);
                    lean_dec_ref(v_snap_1442_);
                    lean_dec_ref(v_params_1441_);
                    v___x_1462_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1462_, 0, v_b_1448_);
                    return v___x_1462_;
                }
            }
            1 => {
                v___x_1453_ = 1usize;
                v___x_1454_ = lean_usize_add(v_i_1446_, v___x_1453_);
                v_i_1446_ = v___x_1454_;
                v_b_1448_ = v_a_1452_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2___boxed(
    mut v_params_1463_: *mut LeanObject,
    mut v_snap_1464_: *mut LeanObject,
    mut v_fst_1465_: *mut LeanObject,
    mut v_snd_1466_: *mut LeanObject,
    mut v_as_1467_: *mut LeanObject,
    mut v_i_1468_: *mut LeanObject,
    mut v_stop_1469_: *mut LeanObject,
    mut v_b_1470_: *mut LeanObject,
    mut v___y_1471_: *mut LeanObject,
    mut v___y_1472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_1473_: usize = 0;
    let mut v_stop_boxed_1474_: usize = 0;
    let mut v_res_1475_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1473_ = lean_unbox_usize(v_i_1468_);
    lean_dec(v_i_1468_);
    v_stop_boxed_1474_ = lean_unbox_usize(v_stop_1469_);
    lean_dec(v_stop_1469_);
    v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_1463_, v_snap_1464_, v_fst_1465_, v_snd_1466_, v_as_1467_, v_i_boxed_1473_, v_stop_boxed_1474_, v_b_1470_, v___y_1471_);
    lean_dec_ref(v___y_1471_);
    lean_dec_ref(v_as_1467_);
    return v_res_1475_;
}
pub unsafe fn _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1() -> *mut LeanObject {
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    v___x_1478_ = l_Array_instInhabited(lean_box(0));
    return v___x_1478_;
}
pub unsafe fn _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2() -> *mut LeanObject {
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    v___x_1479_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CodeAction_holeCodeActionProvider___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CodeAction_holeCodeActionProvider___closed__1_once),
        _init_l_Lean_CodeAction_holeCodeActionProvider___closed__1,
    );
    v___x_1480_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1480_, 0, v___x_1479_);
    lean_ctor_set(v___x_1480_, 1, v___x_1479_);
    return v___x_1480_;
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider(
    mut v_params_1483_: *mut LeanObject,
    mut v_snap_1484_: *mut LeanObject,
    mut v_a_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1491_: u8 = 0;
    let mut v_toEditableDocumentCore_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_meta_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_end_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: u8 = 0;
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: u8 = 0;
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: usize = 0;
    let mut v___x_1533_: usize = 0;
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: usize = 0;
    let mut v___x_1536_: usize = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1487_ = l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(v_a_1485_);
                v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
                v_isSharedCheck_1538_ = (!lean_is_exclusive(v___x_1487_)) as u8;
                if v_isSharedCheck_1538_ == 0 {
                    v___x_1490_ = v___x_1487_;
                    v_isShared_1491_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1488_);
                    lean_dec(v___x_1487_);
                    v___x_1490_ = lean_box(0);
                    v_isShared_1491_ = v_isSharedCheck_1538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toEditableDocumentCore_1492_ = lean_ctor_get(v_a_1488_, 0);
                lean_inc_ref(v_toEditableDocumentCore_1492_);
                lean_dec(v_a_1488_);
                v_meta_1493_ = lean_ctor_get(v_toEditableDocumentCore_1492_, 0);
                lean_inc_ref(v_meta_1493_);
                lean_dec_ref(v_toEditableDocumentCore_1492_);
                v_range_1494_ = lean_ctor_get(v_params_1483_, 3);
                v_text_1495_ = lean_ctor_get(v_meta_1493_, 3);
                lean_inc_ref(v_text_1495_);
                lean_dec_ref(v_meta_1493_);
                v_start_1496_ = lean_ctor_get(v_range_1494_, 0);
                v_end_1497_ = lean_ctor_get(v_range_1494_, 1);
                lean_inc_ref(v_start_1496_);
                v___x_1498_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1495_, v_start_1496_);
                lean_inc_ref(v_end_1497_);
                v___x_1499_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_1495_, v_end_1497_);
                lean_dec_ref(v_text_1495_);
                v___f_1500_ = lean_alloc_closure(
                    l_Lean_CodeAction_holeCodeActionProvider___lam__0___boxed
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                lean_closure_set(v___f_1500_, 0, v___x_1499_);
                lean_closure_set(v___f_1500_, 1, v___x_1498_);
                v___x_1501_ = lean_unsigned_to_nat(0);
                v___x_1502_ = l_Lean_CodeAction_holeCodeActionProvider___closed__0;
                lean_inc_ref(v_snap_1484_);
                v___x_1503_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_1484_);
                v___x_1504_ =
                    l_Lean_Elab_InfoTree_foldInfo___redArg(v___f_1500_, v___x_1502_, v___x_1503_);
                v___x_1505_ = lean_array_get_size(v___x_1504_);
                v___x_1506_ = lean_unsigned_to_nat(1);
                v___x_1507_ = lean_nat_dec_eq(v___x_1505_, v___x_1506_);
                if v___x_1507_ == 0 {
                    lean_dec(v___x_1504_);
                    lean_dec_ref(v_snap_1484_);
                    lean_dec_ref(v_params_1483_);
                    if v_isShared_1491_ == 0 {
                        lean_ctor_set(v___x_1490_, 0, v___x_1502_);
                        v___x_1509_ = v___x_1490_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1502_);
                        v___x_1509_ = v_reuseFailAlloc_1510_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1511_ = lean_array_fget(v___x_1504_, v___x_1501_);
                    lean_dec(v___x_1504_);
                    v_fst_1512_ = lean_ctor_get(v___x_1511_, 0);
                    lean_inc(v_fst_1512_);
                    v_snd_1513_ = lean_ctor_get(v___x_1511_, 1);
                    lean_inc(v_snd_1513_);
                    lean_dec(v___x_1511_);
                    v___x_1514_ = l_Lean_CodeAction_holeCodeActionExt;
                    v_toEnvExtension_1515_ = lean_ctor_get(v___x_1514_, 0);
                    v_asyncMode_1516_ = lean_ctor_get(v_toEnvExtension_1515_, 2);
                    v___x_1517_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_CodeAction_holeCodeActionProvider___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_CodeAction_holeCodeActionProvider___closed__2_once
                        ),
                        _init_l_Lean_CodeAction_holeCodeActionProvider___closed__2,
                    );
                    v___x_1518_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_1484_);
                    v___x_1519_ = lean_box(0);
                    v___x_1520_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_1517_,
                        v___x_1514_,
                        v___x_1518_,
                        v_asyncMode_1516_,
                        v___x_1519_,
                    );
                    v_snd_1521_ = lean_ctor_get(v___x_1520_, 1);
                    lean_inc(v_snd_1521_);
                    lean_dec(v___x_1520_);
                    v___x_1522_ = l_Lean_CodeAction_holeCodeActionProvider___closed__3;
                    v___x_1523_ = lean_array_get_size(v_snd_1521_);
                    v___x_1524_ = lean_nat_dec_lt(v___x_1501_, v___x_1523_);
                    if v___x_1524_ == 0 {
                        lean_dec(v_snd_1521_);
                        lean_dec(v_snd_1513_);
                        lean_dec(v_fst_1512_);
                        lean_dec_ref(v_snap_1484_);
                        lean_dec_ref(v_params_1483_);
                        if v_isShared_1491_ == 0 {
                            lean_ctor_set(v___x_1490_, 0, v___x_1522_);
                            v___x_1526_ = v___x_1490_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1527_, 0, v___x_1522_);
                            v___x_1526_ = v_reuseFailAlloc_1527_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1528_ = lean_nat_dec_le(v___x_1523_, v___x_1523_);
                        if v___x_1528_ == 0 {
                            if v___x_1524_ == 0 {
                                lean_dec(v_snd_1521_);
                                lean_dec(v_snd_1513_);
                                lean_dec(v_fst_1512_);
                                lean_dec_ref(v_snap_1484_);
                                lean_dec_ref(v_params_1483_);
                                if v_isShared_1491_ == 0 {
                                    lean_ctor_set(v___x_1490_, 0, v___x_1522_);
                                    v___x_1530_ = v___x_1490_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1522_);
                                    v___x_1530_ = v_reuseFailAlloc_1531_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_1490_);
                                v___x_1532_ = 0usize;
                                v___x_1533_ = lean_usize_of_nat(v___x_1523_);
                                v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_1483_, v_snap_1484_, v_fst_1512_, v_snd_1513_, v_snd_1521_, v___x_1532_, v___x_1533_, v___x_1522_, v_a_1485_);
                                lean_dec(v_snd_1521_);
                                return v___x_1534_;
                            }
                        } else {
                            lean_del_object(v___x_1490_);
                            v___x_1535_ = 0usize;
                            v___x_1536_ = lean_usize_of_nat(v___x_1523_);
                            v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_CodeAction_holeCodeActionProvider_spec__2(v_params_1483_, v_snap_1484_, v_fst_1512_, v_snd_1513_, v_snd_1521_, v___x_1535_, v___x_1536_, v___x_1522_, v_a_1485_);
                            lean_dec(v_snd_1521_);
                            return v___x_1537_;
                        }
                    }
                }
            }
            2 => {
                return v___x_1509_;
            }
            3 => {
                return v___x_1526_;
            }
            4 => {
                return v___x_1530_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_holeCodeActionProvider___boxed(
    mut v_params_1539_: *mut LeanObject,
    mut v_snap_1540_: *mut LeanObject,
    mut v_a_1541_: *mut LeanObject,
    mut v_a_1542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1543_: *mut LeanObject = core::ptr::null_mut();
    v_res_1543_ = l_Lean_CodeAction_holeCodeActionProvider(v_params_1539_, v_snap_1540_, v_a_1541_);
    lean_dec_ref(v_a_1541_);
    return v_res_1543_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1()
-> *mut LeanObject {
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    v___x_1551_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___closed__2;
    v___x_1552_ = lean_alloc_closure(
        l_Lean_CodeAction_holeCodeActionProvider___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_1553_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_1551_, v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1___boxed(
    mut v_a_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1555_: *mut LeanObject = core::ptr::null_mut();
    v_res_1555_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
    return v_res_1555_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorIdx(
    mut v_x_1556_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1556_) == 0 {
        let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
        v___x_1557_ = lean_unsigned_to_nat(0);
        return v___x_1557_;
    } else {
        let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
        v___x_1558_ = lean_unsigned_to_nat(1);
        return v___x_1558_;
    }
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorIdx___boxed(
    mut v_x_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1560_: *mut LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Lean_CodeAction_FindTacticResult_ctorIdx(v_x_1559_);
    lean_dec_ref(v_x_1559_);
    return v_res_1560_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(
    mut v_t_1561_: *mut LeanObject,
    mut v_k_1562_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1561_) == 0 {
        let mut v_a_1563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
        v_a_1563_ = lean_ctor_get(v_t_1561_, 0);
        lean_inc(v_a_1563_);
        lean_dec_ref_known(v_t_1561_, 1);
        v___x_1564_ = lean_apply_1(v_k_1562_, v_a_1563_);
        return v___x_1564_;
    } else {
        let mut v_preferred_1565_: u8 = 0;
        let mut v_insertIdx_1566_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
        v_preferred_1565_ = lean_ctor_get_uint8(
            v_t_1561_,
            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
        );
        v_insertIdx_1566_ = lean_ctor_get(v_t_1561_, 0);
        lean_inc(v_insertIdx_1566_);
        v_a_1567_ = lean_ctor_get(v_t_1561_, 1);
        lean_inc(v_a_1567_);
        lean_dec_ref_known(v_t_1561_, 2);
        v___x_1568_ = lean_box((v_preferred_1565_) as usize);
        v___x_1569_ = lean_apply_3(v_k_1562_, v___x_1568_, v_insertIdx_1566_, v_a_1567_);
        return v___x_1569_;
    }
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorElim(
    mut v_motive_1570_: *mut LeanObject,
    mut v_ctorIdx_1571_: *mut LeanObject,
    mut v_t_1572_: *mut LeanObject,
    mut v_h_1573_: *mut LeanObject,
    mut v_k_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1575_: *mut LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1572_, v_k_1574_);
    return v___x_1575_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_ctorElim___boxed(
    mut v_motive_1576_: *mut LeanObject,
    mut v_ctorIdx_1577_: *mut LeanObject,
    mut v_t_1578_: *mut LeanObject,
    mut v_h_1579_: *mut LeanObject,
    mut v_k_1580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1581_: *mut LeanObject = core::ptr::null_mut();
    v_res_1581_ = l_Lean_CodeAction_FindTacticResult_ctorElim(
        v_motive_1576_,
        v_ctorIdx_1577_,
        v_t_1578_,
        v_h_1579_,
        v_k_1580_,
    );
    lean_dec(v_ctorIdx_1577_);
    return v_res_1581_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tactic_elim___redArg(
    mut v_t_1582_: *mut LeanObject,
    mut v_tactic_1583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1582_, v_tactic_1583_);
    return v___x_1584_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tactic_elim(
    mut v_motive_1585_: *mut LeanObject,
    mut v_t_1586_: *mut LeanObject,
    mut v_h_1587_: *mut LeanObject,
    mut v_tactic_1588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    v___x_1589_ = l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1586_, v_tactic_1588_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tacticSeq_elim___redArg(
    mut v_t_1590_: *mut LeanObject,
    mut v_tacticSeq_1591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    v___x_1592_ =
        l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1590_, v_tacticSeq_1591_);
    return v___x_1592_;
}
pub unsafe fn l_Lean_CodeAction_FindTacticResult_tacticSeq_elim(
    mut v_motive_1593_: *mut LeanObject,
    mut v_t_1594_: *mut LeanObject,
    mut v_h_1595_: *mut LeanObject,
    mut v_tacticSeq_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    v___x_1597_ =
        l_Lean_CodeAction_FindTacticResult_ctorElim___redArg(v_t_1594_, v_tacticSeq_1596_);
    return v___x_1597_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(
    mut v_range_1598_: *mut LeanObject,
    mut v_stx_1599_: *mut LeanObject,
    mut v_prev_x3f_1600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1601_: u8 = 0;
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1607_: u8 = 0;
    let mut v___y_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: u8 = 0;
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trailing_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endPos_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startPos_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stopPos_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: u8 = 0;
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1601_ = 1;
                v___x_1602_ = l_Lean_Syntax_getPos_x3f(v_stx_1599_, v___x_1601_);
                if lean_obj_tag(v___x_1602_) == 0 {
                    lean_dec(v_prev_x3f_1600_);
                    v___x_1603_ = lean_box(0);
                    return v___x_1603_;
                } else {
                    v_val_1604_ = lean_ctor_get(v___x_1602_, 0);
                    v_isSharedCheck_1635_ = (!lean_is_exclusive(v___x_1602_)) as u8;
                    if v_isSharedCheck_1635_ == 0 {
                        v___x_1606_ = v___x_1602_;
                        v_isShared_1607_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1604_);
                        lean_dec(v___x_1602_);
                        v___x_1606_ = lean_box(0);
                        v_isShared_1607_ = v_isSharedCheck_1635_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_prev_x3f_1600_) == 0 {
                    lean_inc(v_val_1604_);
                    v___y_1609_ = v_val_1604_;
                    state = 2;
                    continue;
                } else {
                    v_val_1634_ = lean_ctor_get(v_prev_x3f_1600_, 0);
                    lean_inc(v_val_1634_);
                    lean_dec_ref_known(v_prev_x3f_1600_, 1);
                    v___y_1609_ = v_val_1634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_start_1610_ = lean_ctor_get(v_range_1598_, 0);
                v_stop_1611_ = lean_ctor_get(v_range_1598_, 1);
                v___x_1612_ = lean_nat_dec_le(v___y_1609_, v_start_1610_);
                lean_dec(v___y_1609_);
                if v___x_1612_ == 0 {
                    lean_del_object(v___x_1606_);
                    lean_dec(v_val_1604_);
                    v___x_1613_ = lean_box(0);
                    return v___x_1613_;
                } else {
                    v___x_1614_ = l_Lean_Syntax_getTailInfo(v_stx_1599_);
                    if lean_obj_tag(v___x_1614_) == 0 {
                        v_trailing_1615_ = lean_ctor_get(v___x_1614_, 2);
                        lean_inc_ref(v_trailing_1615_);
                        v_endPos_1616_ = lean_ctor_get(v___x_1614_, 3);
                        lean_inc(v_endPos_1616_);
                        lean_dec_ref_known(v___x_1614_, 4);
                        v_startPos_1617_ = lean_ctor_get(v_trailing_1615_, 1);
                        lean_inc(v_startPos_1617_);
                        v_stopPos_1618_ = lean_ctor_get(v_trailing_1615_, 2);
                        lean_inc(v_stopPos_1618_);
                        lean_dec_ref(v_trailing_1615_);
                        v___x_1619_ = lean_nat_sub(v_stopPos_1618_, v_startPos_1617_);
                        lean_dec(v_startPos_1617_);
                        lean_dec(v_stopPos_1618_);
                        v___x_1620_ = lean_nat_add(v_endPos_1616_, v___x_1619_);
                        lean_dec(v___x_1619_);
                        v___x_1621_ = lean_nat_dec_le(v_stop_1611_, v___x_1620_);
                        lean_dec(v___x_1620_);
                        if v___x_1621_ == 0 {
                            lean_dec(v_endPos_1616_);
                            lean_del_object(v___x_1606_);
                            lean_dec(v_val_1604_);
                            v___x_1622_ = lean_box(0);
                            return v___x_1622_;
                        } else {
                            v___x_1623_ = lean_nat_dec_le(v_val_1604_, v_start_1610_);
                            lean_dec(v_val_1604_);
                            if v___x_1623_ == 0 {
                                lean_dec(v_endPos_1616_);
                                v___x_1624_ = lean_box((v___x_1623_) as usize);
                                if v_isShared_1607_ == 0 {
                                    lean_ctor_set(v___x_1606_, 0, v___x_1624_);
                                    v___x_1626_ = v___x_1606_;
                                    state = 3;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1627_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1624_);
                                    v___x_1626_ = v_reuseFailAlloc_1627_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v___x_1628_ = lean_nat_dec_le(v_stop_1611_, v_endPos_1616_);
                                lean_dec(v_endPos_1616_);
                                v___x_1629_ = lean_box((v___x_1628_) as usize);
                                if v_isShared_1607_ == 0 {
                                    lean_ctor_set(v___x_1606_, 0, v___x_1629_);
                                    v___x_1631_ = v___x_1606_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1632_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
                                    v___x_1631_ = v_reuseFailAlloc_1632_;
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v___x_1614_);
                        lean_del_object(v___x_1606_);
                        lean_dec(v_val_1604_);
                        v___x_1633_ = lean_box(0);
                        return v___x_1633_;
                    }
                }
            }
            3 => {
                return v___x_1626_;
            }
            4 => {
                return v___x_1631_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit___boxed(
    mut v_range_1636_: *mut LeanObject,
    mut v_stx_1637_: *mut LeanObject,
    mut v_prev_x3f_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1639_: *mut LeanObject = core::ptr::null_mut();
    v_res_1639_ =
        l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(
            v_range_1636_,
            v_stx_1637_,
            v_prev_x3f_1638_,
        );
    lean_dec(v_stx_1637_);
    lean_dec_ref(v_range_1636_);
    return v_res_1639_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(
    mut v_r_u2081_1640_: *mut LeanObject,
    mut v_r_u2082_1641_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_u2081_1640_) == 1 {
        let mut v_val_1642_: *mut LeanObject = core::ptr::null_mut();
        v_val_1642_ = lean_ctor_get(v_r_u2081_1640_, 0);
        if lean_obj_tag(v_val_1642_) == 1 {
            let mut v_preferred_1643_: u8 = 0;
            v_preferred_1643_ = lean_ctor_get_uint8(
                v_val_1642_,
                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            );
            if v_preferred_1643_ == 1 {
                if lean_obj_tag(v_r_u2082_1641_) == 1 {
                    let mut v_preferred_1644_: u8 = 0;
                    v_preferred_1644_ = lean_ctor_get_uint8(
                        v_r_u2082_1641_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    );
                    if v_preferred_1644_ == 0 {
                        lean_inc_ref(v_val_1642_);
                        return v_val_1642_;
                    } else {
                        lean_inc_ref(v_r_u2082_1641_);
                        return v_r_u2082_1641_;
                    }
                } else {
                    lean_inc_ref(v_r_u2082_1641_);
                    return v_r_u2082_1641_;
                }
            } else {
                lean_inc_ref(v_r_u2082_1641_);
                return v_r_u2082_1641_;
            }
        } else {
            lean_inc_ref(v_r_u2082_1641_);
            return v_r_u2082_1641_;
        }
    } else {
        lean_inc_ref(v_r_u2082_1641_);
        return v_r_u2082_1641_;
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge___boxed(
    mut v_r_u2081_1645_: *mut LeanObject,
    mut v_r_u2082_1646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1647_: *mut LeanObject = core::ptr::null_mut();
    v_res_1647_ =
        l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(
            v_r_u2081_1645_,
            v_r_u2082_1646_,
        );
    lean_dec_ref(v_r_u2082_1646_);
    lean_dec(v_r_u2081_1645_);
    return v_res_1647_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(
    mut v_upperBound_1651_: *mut LeanObject,
    mut v___x_1652_: *mut LeanObject,
    mut v_range_1653_: *mut LeanObject,
    mut v_a_1654_: *mut LeanObject,
    mut v_b_1655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: u8 = 0;
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: u8 = 0;
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1672_: u8 = 0;
    let mut v_stop_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1677_: u8 = 0;
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1684_: u8 = 0;
    let mut v_unused_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1661_ = lean_nat_dec_lt(v_a_1654_, v_upperBound_1651_);
                if v___x_1661_ == 0 {
                    lean_dec(v_a_1654_);
                    lean_dec_ref(v_range_1653_);
                    lean_inc_ref(v_b_1655_);
                    return v_b_1655_;
                } else {
                    v___x_1662_ = lean_box(0);
                    v___x_1663_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0;
                    v___x_1664_ = lean_unsigned_to_nat(2);
                    v___x_1665_ = lean_nat_mul(v___x_1664_, v_a_1654_);
                    v___x_1666_ = l_Lean_Syntax_getArg(v___x_1652_, v___x_1665_);
                    lean_dec(v___x_1665_);
                    v___x_1667_ = 0;
                    v___x_1668_ = l_Lean_Syntax_getPos_x3f(v___x_1666_, v___x_1667_);
                    lean_dec(v___x_1666_);
                    if lean_obj_tag(v___x_1668_) == 1 {
                        v_val_1669_ = lean_ctor_get(v___x_1668_, 0);
                        v_isSharedCheck_1687_ = (!lean_is_exclusive(v___x_1668_)) as u8;
                        if v_isSharedCheck_1687_ == 0 {
                            v___x_1671_ = v___x_1668_;
                            v_isShared_1672_ = v_isSharedCheck_1687_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_val_1669_);
                            lean_dec(v___x_1668_);
                            v___x_1671_ = lean_box(0);
                            v_isShared_1672_ = v_isSharedCheck_1687_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_1668_);
                        v_a_1657_ = v___x_1663_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1658_ = lean_unsigned_to_nat(1);
                v___x_1659_ = lean_nat_add(v_a_1654_, v___x_1658_);
                lean_dec(v_a_1654_);
                v_a_1654_ = v___x_1659_;
                v_b_1655_ = v_a_1657_;
                state = 0;
                continue;
            }
            2 => {
                v_stop_1673_ = lean_ctor_get(v_range_1653_, 1);
                v___x_1674_ = lean_nat_dec_lt(v_stop_1673_, v_val_1669_);
                lean_dec(v_val_1669_);
                if v___x_1674_ == 0 {
                    lean_del_object(v___x_1671_);
                    v_a_1657_ = v___x_1663_;
                    state = 1;
                    continue;
                } else {
                    v_isSharedCheck_1684_ = (!lean_is_exclusive(v_range_1653_)) as u8;
                    if v_isSharedCheck_1684_ == 0 {
                        v_unused_1685_ = lean_ctor_get(v_range_1653_, 1);
                        lean_dec(v_unused_1685_);
                        v_unused_1686_ = lean_ctor_get(v_range_1653_, 0);
                        lean_dec(v_unused_1686_);
                        v___x_1676_ = v_range_1653_;
                        v_isShared_1677_ = v_isSharedCheck_1684_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_range_1653_);
                        v___x_1676_ = lean_box(0);
                        v_isShared_1677_ = v_isSharedCheck_1684_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1672_ == 0 {
                    lean_ctor_set(v___x_1671_, 0, v_a_1654_);
                    v___x_1679_ = v___x_1671_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1683_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1683_, 0, v_a_1654_);
                    v___x_1679_ = v_reuseFailAlloc_1683_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1677_ == 0 {
                    lean_ctor_set(v___x_1676_, 1, v___x_1662_);
                    lean_ctor_set(v___x_1676_, 0, v___x_1679_);
                    v___x_1681_ = v___x_1676_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1679_);
                    lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1662_);
                    v___x_1681_ = v_reuseFailAlloc_1682_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___boxed(
    mut v_upperBound_1688_: *mut LeanObject,
    mut v___x_1689_: *mut LeanObject,
    mut v_range_1690_: *mut LeanObject,
    mut v_a_1691_: *mut LeanObject,
    mut v_b_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_1688_, v___x_1689_, v_range_1690_, v_a_1691_, v_b_1692_);
    lean_dec_ref(v_b_1692_);
    lean_dec(v___x_1689_);
    lean_dec(v_upperBound_1688_);
    return v_res_1693_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(
    mut v_stx_1694_: *mut LeanObject,
    mut v_a_1695_: *mut LeanObject,
    mut v___x_1696_: u8,
    mut v_snd_1697_: *mut LeanObject,
    mut v_____r_1698_: *mut LeanObject,
    mut v_childRes_1699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1705_ = l_Lean_Syntax_getArg(v_stx_1694_, v_a_1695_);
                v___x_1706_ = l_Lean_Syntax_getTailPos_x3f(v___x_1705_, v___x_1696_);
                lean_dec(v___x_1705_);
                if lean_obj_tag(v___x_1706_) == 0 {
                    v___y_1701_ = v_snd_1697_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_snd_1697_);
                    v___y_1701_ = v___x_1706_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1702_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1702_, 0, v_childRes_1699_);
                lean_ctor_set(v___x_1702_, 1, v___y_1701_);
                v___x_1703_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1703_, 0, v___x_1702_);
                v___x_1704_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1704_, 0, v___x_1703_);
                return v___x_1704_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0___boxed(
    mut v_stx_1707_: *mut LeanObject,
    mut v_a_1708_: *mut LeanObject,
    mut v___x_1709_: *mut LeanObject,
    mut v_snd_1710_: *mut LeanObject,
    mut v_____r_1711_: *mut LeanObject,
    mut v_childRes_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4623__boxed_1713_: u8 = 0;
    let mut v_res_1714_: *mut LeanObject = core::ptr::null_mut();
    v___x_4623__boxed_1713_ = (lean_unbox(v___x_1709_) as u8);
    v_res_1714_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1707_, v_a_1708_, v___x_4623__boxed_1713_, v_snd_1710_, v_____r_1711_, v_childRes_1712_);
    lean_dec(v_a_1708_);
    lean_dec(v_stx_1707_);
    return v_res_1714_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(
    mut v___y_1725_: *mut LeanObject,
    mut v___x_1726_: u8,
    mut v___x_1727_: *mut LeanObject,
    mut v_range_1728_: *mut LeanObject,
    mut v___x_1729_: *mut LeanObject,
    mut v_preferred_1730_: *mut LeanObject,
    mut v_a_1731_: *mut LeanObject,
    mut v_b_1732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inner_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_next_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_upperBound_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v_val_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1748_: u8 = 0;
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: u8 = 0;
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1790_: u8 = 0;
    let mut v_reuseFailAlloc_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut v_unused_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1798_: u8 = 0;
    let mut v_unused_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_inner_1733_ = lean_ctor_get(v_a_1731_, 2);
                lean_inc(v_inner_1733_);
                v_next_1734_ = lean_ctor_get(v_inner_1733_, 0);
                lean_inc(v_next_1734_);
                if lean_obj_tag(v_next_1734_) == 0 {
                    lean_dec(v_inner_1733_);
                    lean_dec_ref(v_a_1731_);
                    lean_dec_ref(v_preferred_1730_);
                    lean_dec(v___x_1729_);
                    lean_dec_ref(v_range_1728_);
                    lean_dec(v___x_1727_);
                    v___x_1735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1735_, 0, v_b_1732_);
                    return v___x_1735_;
                } else {
                    v_nextIdx_1736_ = lean_ctor_get(v_a_1731_, 0);
                    v_n_1737_ = lean_ctor_get(v_a_1731_, 1);
                    v_isSharedCheck_1798_ = (!lean_is_exclusive(v_a_1731_)) as u8;
                    if v_isSharedCheck_1798_ == 0 {
                        v_unused_1799_ = lean_ctor_get(v_a_1731_, 2);
                        lean_dec(v_unused_1799_);
                        v___x_1739_ = v_a_1731_;
                        v_isShared_1740_ = v_isSharedCheck_1798_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_n_1737_);
                        lean_inc(v_nextIdx_1736_);
                        lean_dec(v_a_1731_);
                        v___x_1739_ = lean_box(0);
                        v_isShared_1740_ = v_isSharedCheck_1798_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_upperBound_1741_ = lean_ctor_get(v_inner_1733_, 1);
                v_isSharedCheck_1796_ = (!lean_is_exclusive(v_inner_1733_)) as u8;
                if v_isSharedCheck_1796_ == 0 {
                    v_unused_1797_ = lean_ctor_get(v_inner_1733_, 0);
                    lean_dec(v_unused_1797_);
                    v___x_1743_ = v_inner_1733_;
                    v_isShared_1744_ = v_isSharedCheck_1796_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_upperBound_1741_);
                    lean_dec(v_inner_1733_);
                    v___x_1743_ = lean_box(0);
                    v_isShared_1744_ = v_isSharedCheck_1796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_val_1745_ = lean_ctor_get(v_next_1734_, 0);
                v_isSharedCheck_1795_ = (!lean_is_exclusive(v_next_1734_)) as u8;
                if v_isSharedCheck_1795_ == 0 {
                    v___x_1747_ = v_next_1734_;
                    v_isShared_1748_ = v_isSharedCheck_1795_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_val_1745_);
                    lean_dec(v_next_1734_);
                    v___x_1747_ = lean_box(0);
                    v_isShared_1748_ = v_isSharedCheck_1795_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1749_ = lean_nat_add(v_val_1745_, v_nextIdx_1736_);
                lean_dec(v_nextIdx_1736_);
                lean_dec(v_val_1745_);
                v___x_1750_ = lean_nat_dec_lt(v___x_1749_, v_upperBound_1741_);
                if v___x_1750_ == 0 {
                    lean_dec(v___x_1749_);
                    lean_del_object(v___x_1743_);
                    lean_dec(v_upperBound_1741_);
                    lean_del_object(v___x_1739_);
                    lean_dec(v_n_1737_);
                    lean_dec_ref(v_preferred_1730_);
                    lean_dec(v___x_1729_);
                    lean_dec_ref(v_range_1728_);
                    lean_dec(v___x_1727_);
                    if v_isShared_1748_ == 0 {
                        lean_ctor_set(v___x_1747_, 0, v_b_1732_);
                        v___x_1752_ = v___x_1747_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_b_1732_);
                        v___x_1752_ = v_reuseFailAlloc_1753_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_1754_ = lean_unsigned_to_nat(1);
                    v___x_1755_ = lean_nat_add(v___x_1749_, v___x_1754_);
                    if v_isShared_1748_ == 0 {
                        lean_ctor_set(v___x_1747_, 0, v___x_1755_);
                        v___x_1757_ = v___x_1747_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1755_);
                        v___x_1757_ = v_reuseFailAlloc_1794_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1752_;
            }
            5 => {
                if v_isShared_1744_ == 0 {
                    lean_ctor_set(v___x_1743_, 0, v___x_1757_);
                    v___x_1759_ = v___x_1743_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1757_);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_upperBound_1741_);
                    v___x_1759_ = v_reuseFailAlloc_1793_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc(v_n_1737_);
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 2, v___x_1759_);
                    lean_ctor_set(v___x_1739_, 0, v_n_1737_);
                    v___x_1761_ = v___x_1739_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1792_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_n_1737_);
                    lean_ctor_set(v_reuseFailAlloc_1792_, 1, v_n_1737_);
                    lean_ctor_set(v_reuseFailAlloc_1792_, 2, v___x_1759_);
                    v___x_1761_ = v_reuseFailAlloc_1792_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1770_ = l_Lean_Syntax_getArg(v___x_1727_, v___x_1749_);
                v___x_1771_ = lean_box(0);
                v___x_1772_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_1728_, v___x_1770_, v___x_1771_);
                if lean_obj_tag(v___x_1772_) == 1 {
                    v_val_1773_ = lean_ctor_get(v___x_1772_, 0);
                    lean_inc(v_val_1773_);
                    lean_dec_ref_known(v___x_1772_, 1);
                    lean_inc(v___x_1727_);
                    v___x_1774_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1774_, 0, v___x_1727_);
                    lean_ctor_set(v___x_1774_, 1, v___x_1749_);
                    lean_inc(v___x_1729_);
                    v___x_1775_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1775_, 0, v___x_1774_);
                    lean_ctor_set(v___x_1775_, 1, v___x_1729_);
                    lean_inc(v___x_1770_);
                    lean_inc_ref(v___x_1775_);
                    lean_inc_ref(v_range_1728_);
                    lean_inc_ref(v_preferred_1730_);
                    v___x_1776_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_1730_, v_range_1728_, v___x_1775_, v___x_1770_, v___x_1771_);
                    if lean_obj_tag(v___x_1776_) == 0 {
                        lean_dec_ref_known(v___x_1775_, 2);
                        lean_dec(v_val_1773_);
                        lean_dec(v___x_1770_);
                        lean_dec_ref(v___x_1761_);
                        lean_dec(v_b_1732_);
                        lean_dec_ref(v_preferred_1730_);
                        lean_dec(v___x_1729_);
                        lean_dec_ref(v_range_1728_);
                        lean_dec(v___x_1727_);
                        return v___x_1776_;
                    } else {
                        v_val_1777_ = lean_ctor_get(v___x_1776_, 0);
                        v_isSharedCheck_1790_ = (!lean_is_exclusive(v___x_1776_)) as u8;
                        if v_isSharedCheck_1790_ == 0 {
                            v___x_1779_ = v___x_1776_;
                            v_isShared_1780_ = v_isSharedCheck_1790_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_val_1777_);
                            lean_dec(v___x_1776_);
                            v___x_1779_ = lean_box(0);
                            v_isShared_1780_ = v_isSharedCheck_1790_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1772_);
                    lean_dec(v___x_1770_);
                    lean_dec(v___x_1749_);
                    v_a_1731_ = v___x_1761_;
                    state = 0;
                    continue;
                }
            }
            8 => {
                v___x_1764_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_merge(v___y_1725_, v___y_1763_);
                lean_dec_ref(v___y_1763_);
                v___x_1765_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1765_, 0, v___x_1764_);
                v_a_1731_ = v___x_1761_;
                v_b_1732_ = v___x_1765_;
                state = 0;
                continue;
            }
            9 => {
                if lean_obj_tag(v_b_1732_) == 0 {
                    v___y_1763_ = v_val_1768_;
                    state = 8;
                    continue;
                } else {
                    lean_dec_ref_known(v_b_1732_, 1);
                    if v___x_1726_ == 0 {
                        v___y_1763_ = v_val_1768_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec_ref(v_val_1768_);
                        lean_dec_ref(v___x_1761_);
                        lean_dec_ref(v_preferred_1730_);
                        lean_dec(v___x_1729_);
                        lean_dec_ref(v_range_1728_);
                        lean_dec(v___x_1727_);
                        v___x_1769_ = lean_box(0);
                        return v___x_1769_;
                    }
                }
            }
            10 => {
                if lean_obj_tag(v_val_1777_) == 0 {
                    v___x_1781_ = (lean_unbox(v_val_1773_) as u8);
                    lean_dec(v_val_1773_);
                    if v___x_1781_ == 0 {
                        lean_del_object(v___x_1779_);
                        lean_dec_ref_known(v___x_1775_, 2);
                        lean_dec(v___x_1770_);
                        v_a_1731_ = v___x_1761_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1783_ = lean_unsigned_to_nat(0);
                        v___x_1784_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1784_, 0, v___x_1770_);
                        lean_ctor_set(v___x_1784_, 1, v___x_1783_);
                        v___x_1785_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_1785_, 0, v___x_1784_);
                        lean_ctor_set(v___x_1785_, 1, v___x_1775_);
                        if v_isShared_1780_ == 0 {
                            lean_ctor_set_tag(v___x_1779_, 0);
                            lean_ctor_set(v___x_1779_, 0, v___x_1785_);
                            v___x_1787_ = v___x_1779_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1785_);
                            v___x_1787_ = v_reuseFailAlloc_1788_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1779_);
                    lean_dec_ref_known(v___x_1775_, 2);
                    lean_dec(v_val_1773_);
                    lean_dec(v___x_1770_);
                    v_val_1789_ = lean_ctor_get(v_val_1777_, 0);
                    lean_inc(v_val_1789_);
                    lean_dec_ref_known(v_val_1777_, 1);
                    v_val_1768_ = v_val_1789_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_val_1768_ = v___x_1787_;
                state = 9;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(
    mut v_preferred_1806_: *mut LeanObject,
    mut v_range_1807_: *mut LeanObject,
    mut v_stack_1808_: *mut LeanObject,
    mut v_stx_1809_: *mut LeanObject,
    mut v_prev_x3f_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: u8 = 0;
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_childRes_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1822_: u8 = 0;
    let mut v_fst_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_childRes_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v___x_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1847_: u8 = 0;
    let mut v_unused_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bracket_1861_: u8 = 0;
    let mut v___y_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: u8 = 0;
    let mut v___y_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_stx_1809_);
                v___x_1811_ = l_Lean_Syntax_getKind(v_stx_1809_);
                v___x_1812_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__3;
                v___x_1813_ = lean_name_eq(v___x_1811_, v___x_1812_);
                lean_dec(v___x_1811_);
                if v___x_1813_ == 0 {
                    v___x_1814_ = l_Lean_Syntax_getNumArgs(v_stx_1809_);
                    v___x_1815_ = lean_unsigned_to_nat(0);
                    v_childRes_1816_ = lean_box(0);
                    v___x_1817_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1817_, 0, v_childRes_1816_);
                    lean_ctor_set(v___x_1817_, 1, v_prev_x3f_1810_);
                    v___x_1818_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v___x_1814_, v_stx_1809_, v_range_1807_, v_stack_1808_, v_preferred_1806_, v___x_1813_, v___x_1815_, v___x_1817_);
                    lean_dec(v___x_1814_);
                    if lean_obj_tag(v___x_1818_) == 0 {
                        return v_childRes_1816_;
                    } else {
                        v_val_1819_ = lean_ctor_get(v___x_1818_, 0);
                        v_isSharedCheck_1827_ = (!lean_is_exclusive(v___x_1818_)) as u8;
                        if v_isSharedCheck_1827_ == 0 {
                            v___x_1821_ = v___x_1818_;
                            v_isShared_1822_ = v_isSharedCheck_1827_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_1819_);
                            lean_dec(v___x_1818_);
                            v___x_1821_ = lean_box(0);
                            v_isShared_1822_ = v_isSharedCheck_1827_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_prev_x3f_1810_);
                    v___x_1828_ = lean_unsigned_to_nat(0);
                    v___x_1858_ = l_Lean_Syntax_getArg(v_stx_1809_, v___x_1828_);
                    lean_inc(v___x_1858_);
                    v___x_1859_ = l_Lean_Syntax_getKind(v___x_1858_);
                    v___x_1860_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__6;
                    v_bracket_1861_ = lean_name_eq(v___x_1859_, v___x_1860_);
                    lean_dec(v___x_1859_);
                    if v_bracket_1861_ == 0 {
                        v___y_1870_ = v___x_1828_;
                        state = 8;
                        continue;
                    } else {
                        v___x_1889_ = lean_unsigned_to_nat(1);
                        v___y_1870_ = v___x_1889_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1823_ = lean_ctor_get(v_val_1819_, 0);
                lean_inc(v_fst_1823_);
                lean_dec(v_val_1819_);
                if v_isShared_1822_ == 0 {
                    lean_ctor_set(v___x_1821_, 0, v_fst_1823_);
                    v___x_1825_ = v___x_1821_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_fst_1823_);
                    v___x_1825_ = v_reuseFailAlloc_1826_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1825_;
            }
            3 => {
                v_childRes_1833_ = lean_box(0);
                v___x_1834_ = l_Lean_Syntax_getNumArgs(v___y_1830_);
                v___x_1835_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go___closed__4;
                v___x_1836_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1836_, 0, v___x_1835_);
                lean_ctor_set(v___x_1836_, 1, v___x_1834_);
                v___x_1837_ = lean_unsigned_to_nat(1);
                v___x_1838_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1838_, 0, v___x_1828_);
                lean_ctor_set(v___x_1838_, 1, v___x_1837_);
                lean_ctor_set(v___x_1838_, 2, v___x_1836_);
                v___x_1839_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_1832_, v___x_1813_, v___y_1830_, v_range_1807_, v___y_1831_, v_preferred_1806_, v___x_1838_, v_childRes_1833_);
                if lean_obj_tag(v___x_1839_) == 0 {
                    lean_dec(v___y_1832_);
                    return v___x_1839_;
                } else {
                    v_val_1840_ = lean_ctor_get(v___x_1839_, 0);
                    lean_inc(v_val_1840_);
                    if lean_obj_tag(v_val_1840_) == 0 {
                        v_isSharedCheck_1847_ = (!lean_is_exclusive(v___x_1839_)) as u8;
                        if v_isSharedCheck_1847_ == 0 {
                            v_unused_1848_ = lean_ctor_get(v___x_1839_, 0);
                            lean_dec(v_unused_1848_);
                            v___x_1842_ = v___x_1839_;
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 4;
                            continue;
                        } else {
                            lean_dec(v___x_1839_);
                            v___x_1842_ = lean_box(0);
                            v_isShared_1843_ = v_isSharedCheck_1847_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_val_1840_, 1);
                        lean_dec(v___y_1832_);
                        return v___x_1839_;
                    }
                }
            }
            4 => {
                if v_isShared_1843_ == 0 {
                    lean_ctor_set(v___x_1842_, 0, v___y_1832_);
                    v___x_1845_ = v___x_1842_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___y_1832_);
                    v___x_1845_ = v_reuseFailAlloc_1846_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1845_;
            }
            6 => {
                lean_inc(v___y_1850_);
                v___x_1854_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1854_, 0, v___y_1850_);
                lean_ctor_set(v___x_1854_, 1, v___x_1828_);
                lean_inc(v___y_1852_);
                v___x_1855_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1855_, 0, v___x_1854_);
                lean_ctor_set(v___x_1855_, 1, v___y_1852_);
                v___x_1856_ = lean_alloc_ctor(1, 2, (1) as u32);
                lean_ctor_set(v___x_1856_, 0, v___y_1851_);
                lean_ctor_set(v___x_1856_, 1, v___x_1855_);
                lean_ctor_set_uint8(
                    v___x_1856_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_1853_,
                );
                v___x_1857_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1857_, 0, v___x_1856_);
                v___y_1830_ = v___y_1850_;
                v___y_1831_ = v___y_1852_;
                v___y_1832_ = v___x_1857_;
                state = 3;
                continue;
            }
            7 => {
                if v_bracket_1861_ == 0 {
                    lean_inc_ref(v_preferred_1806_);
                    v___x_1867_ = lean_apply_1(v_preferred_1806_, v___y_1864_);
                    v___x_1868_ = (lean_unbox(v___x_1867_) as u8);
                    v___y_1850_ = v___y_1863_;
                    v___y_1851_ = v___y_1866_;
                    v___y_1852_ = v___y_1865_;
                    v___y_1853_ = v___x_1868_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v___y_1864_);
                    v___y_1850_ = v___y_1863_;
                    v___y_1851_ = v___y_1866_;
                    v___y_1852_ = v___y_1865_;
                    v___y_1853_ = v___x_1813_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                lean_inc(v___y_1870_);
                lean_inc(v___x_1858_);
                v___x_1871_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1871_, 0, v___x_1858_);
                lean_ctor_set(v___x_1871_, 1, v___y_1870_);
                v___x_1872_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1872_, 0, v_stx_1809_);
                lean_ctor_set(v___x_1872_, 1, v___x_1828_);
                v___x_1873_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1873_, 0, v___x_1872_);
                lean_ctor_set(v___x_1873_, 1, v_stack_1808_);
                v___x_1874_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1874_, 0, v___x_1871_);
                lean_ctor_set(v___x_1874_, 1, v___x_1873_);
                v___x_1875_ = l_Lean_Syntax_getArg(v___x_1858_, v___y_1870_);
                lean_dec(v___y_1870_);
                lean_dec(v___x_1858_);
                v___x_1876_ = l_Lean_Syntax_getArg(v___x_1875_, v___x_1828_);
                v___x_1877_ = 0;
                v___x_1878_ = l_Lean_Syntax_getPos_x3f(v___x_1876_, v___x_1877_);
                lean_dec(v___x_1876_);
                if lean_obj_tag(v___x_1878_) == 0 {
                    v___x_1879_ = lean_box(0);
                    v___y_1830_ = v___x_1875_;
                    v___y_1831_ = v___x_1874_;
                    v___y_1832_ = v___x_1879_;
                    state = 3;
                    continue;
                } else {
                    v_val_1880_ = lean_ctor_get(v___x_1878_, 0);
                    lean_inc(v_val_1880_);
                    lean_dec_ref_known(v___x_1878_, 1);
                    v___x_1881_ = l_Lean_Syntax_getNumArgs(v___x_1875_);
                    v___x_1882_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg___closed__0;
                    lean_inc_ref(v_range_1807_);
                    v___x_1883_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v___x_1881_, v___x_1875_, v_range_1807_, v___x_1828_, v___x_1882_);
                    v_fst_1884_ = lean_ctor_get(v___x_1883_, 0);
                    lean_inc(v_fst_1884_);
                    lean_dec_ref(v___x_1883_);
                    if lean_obj_tag(v_fst_1884_) == 0 {
                        v___x_1885_ = lean_unsigned_to_nat(1);
                        v___x_1886_ = lean_nat_add(v___x_1881_, v___x_1885_);
                        lean_dec(v___x_1881_);
                        v___x_1887_ = lean_nat_shiftr(v___x_1886_, v___x_1885_);
                        lean_dec(v___x_1886_);
                        v___y_1863_ = v___x_1875_;
                        v___y_1864_ = v_val_1880_;
                        v___y_1865_ = v___x_1874_;
                        v___y_1866_ = v___x_1887_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_1881_);
                        v_val_1888_ = lean_ctor_get(v_fst_1884_, 0);
                        lean_inc(v_val_1888_);
                        lean_dec_ref_known(v_fst_1884_, 1);
                        v___y_1863_ = v___x_1875_;
                        v___y_1864_ = v_val_1880_;
                        v___y_1865_ = v___x_1874_;
                        v___y_1866_ = v_val_1888_;
                        state = 7;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(
    mut v_upperBound_1890_: *mut LeanObject,
    mut v_stx_1891_: *mut LeanObject,
    mut v_range_1892_: *mut LeanObject,
    mut v_stack_1893_: *mut LeanObject,
    mut v_preferred_1894_: *mut LeanObject,
    mut v___x_1895_: u8,
    mut v_a_1896_: *mut LeanObject,
    mut v_b_1897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v_a_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1913_: u8 = 0;
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1920_: u8 = 0;
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1914_ = lean_nat_dec_lt(v_a_1896_, v_upperBound_1890_);
                if v___x_1914_ == 0 {
                    lean_dec(v_a_1896_);
                    lean_dec_ref(v_preferred_1894_);
                    lean_dec(v_stack_1893_);
                    lean_dec_ref(v_range_1892_);
                    lean_dec(v_stx_1891_);
                    v___x_1915_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1915_, 0, v_b_1897_);
                    return v___x_1915_;
                } else {
                    v_fst_1916_ = lean_ctor_get(v_b_1897_, 0);
                    v_snd_1917_ = lean_ctor_get(v_b_1897_, 1);
                    v_isSharedCheck_1938_ = (!lean_is_exclusive(v_b_1897_)) as u8;
                    if v_isSharedCheck_1938_ == 0 {
                        v___x_1919_ = v_b_1897_;
                        v_isShared_1920_ = v_isSharedCheck_1938_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_snd_1917_);
                        lean_inc(v_fst_1916_);
                        lean_dec(v_b_1897_);
                        v___x_1919_ = lean_box(0);
                        v_isShared_1920_ = v_isSharedCheck_1938_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_1899_) == 0 {
                    lean_dec(v_a_1896_);
                    lean_dec_ref(v_preferred_1894_);
                    lean_dec(v_stack_1893_);
                    lean_dec_ref(v_range_1892_);
                    lean_dec(v_stx_1891_);
                    v___x_1900_ = lean_box(0);
                    return v___x_1900_;
                } else {
                    v_val_1901_ = lean_ctor_get(v___y_1899_, 0);
                    v_isSharedCheck_1913_ = (!lean_is_exclusive(v___y_1899_)) as u8;
                    if v_isSharedCheck_1913_ == 0 {
                        v___x_1903_ = v___y_1899_;
                        v_isShared_1904_ = v_isSharedCheck_1913_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1901_);
                        lean_dec(v___y_1899_);
                        v___x_1903_ = lean_box(0);
                        v_isShared_1904_ = v_isSharedCheck_1913_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_val_1901_) == 0 {
                    lean_dec(v_a_1896_);
                    lean_dec_ref(v_preferred_1894_);
                    lean_dec(v_stack_1893_);
                    lean_dec_ref(v_range_1892_);
                    lean_dec(v_stx_1891_);
                    v_a_1905_ = lean_ctor_get(v_val_1901_, 0);
                    lean_inc(v_a_1905_);
                    lean_dec_ref_known(v_val_1901_, 1);
                    if v_isShared_1904_ == 0 {
                        lean_ctor_set(v___x_1903_, 0, v_a_1905_);
                        v___x_1907_ = v___x_1903_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1905_);
                        v___x_1907_ = v_reuseFailAlloc_1908_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1903_);
                    v_a_1909_ = lean_ctor_get(v_val_1901_, 0);
                    lean_inc(v_a_1909_);
                    lean_dec_ref_known(v_val_1901_, 1);
                    v___x_1910_ = lean_unsigned_to_nat(1);
                    v___x_1911_ = lean_nat_add(v_a_1896_, v___x_1910_);
                    lean_dec(v_a_1896_);
                    v_a_1896_ = v___x_1911_;
                    v_b_1897_ = v_a_1909_;
                    state = 0;
                    continue;
                }
            }
            3 => {
                return v___x_1907_;
            }
            4 => {
                v___x_1921_ = l_Lean_Syntax_getArg(v_stx_1891_, v_a_1896_);
                lean_inc(v_snd_1917_);
                v___x_1922_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(v_range_1892_, v___x_1921_, v_snd_1917_);
                if lean_obj_tag(v___x_1922_) == 1 {
                    lean_dec_ref_known(v___x_1922_, 1);
                    lean_inc(v_a_1896_);
                    lean_inc(v_stx_1891_);
                    if v_isShared_1920_ == 0 {
                        lean_ctor_set(v___x_1919_, 1, v_a_1896_);
                        lean_ctor_set(v___x_1919_, 0, v_stx_1891_);
                        v___x_1924_ = v___x_1919_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_stx_1891_);
                        lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_a_1896_);
                        v___x_1924_ = v_reuseFailAlloc_1935_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1922_);
                    lean_dec(v___x_1921_);
                    lean_del_object(v___x_1919_);
                    v___x_1936_ = lean_box(0);
                    v___x_1937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1891_, v_a_1896_, v___x_1914_, v_snd_1917_, v___x_1936_, v_fst_1916_);
                    v___y_1899_ = v___x_1937_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                lean_inc(v_stack_1893_);
                v___x_1925_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1925_, 0, v___x_1924_);
                lean_ctor_set(v___x_1925_, 1, v_stack_1893_);
                lean_inc(v_snd_1917_);
                lean_inc_ref(v_range_1892_);
                lean_inc_ref(v_preferred_1894_);
                v___x_1926_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(v_preferred_1894_, v_range_1892_, v___x_1925_, v___x_1921_, v_snd_1917_);
                if lean_obj_tag(v___x_1926_) == 0 {
                    lean_dec(v_snd_1917_);
                    lean_dec(v_fst_1916_);
                    lean_dec(v_a_1896_);
                    lean_dec_ref(v_preferred_1894_);
                    lean_dec(v_stack_1893_);
                    lean_dec_ref(v_range_1892_);
                    lean_dec(v_stx_1891_);
                    v___x_1927_ = lean_box(0);
                    return v___x_1927_;
                } else {
                    v_val_1928_ = lean_ctor_get(v___x_1926_, 0);
                    lean_inc(v_val_1928_);
                    lean_dec_ref_known(v___x_1926_, 1);
                    if lean_obj_tag(v_val_1928_) == 1 {
                        if lean_obj_tag(v_fst_1916_) == 0 {
                            if v___x_1895_ == 0 {
                                v___x_1929_ = lean_box(0);
                                v___x_1930_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1891_, v_a_1896_, v___x_1914_, v_snd_1917_, v___x_1929_, v_val_1928_);
                                v___y_1899_ = v___x_1930_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref_known(v_val_1928_, 1);
                                lean_dec(v_snd_1917_);
                                lean_dec(v_a_1896_);
                                lean_dec_ref(v_preferred_1894_);
                                lean_dec(v_stack_1893_);
                                lean_dec_ref(v_range_1892_);
                                lean_dec(v_stx_1891_);
                                v___x_1931_ = lean_box(0);
                                return v___x_1931_;
                            }
                        } else {
                            lean_dec_ref_known(v_fst_1916_, 1);
                            lean_dec_ref_known(v_val_1928_, 1);
                            lean_dec(v_snd_1917_);
                            lean_dec(v_a_1896_);
                            lean_dec_ref(v_preferred_1894_);
                            lean_dec(v_stack_1893_);
                            lean_dec_ref(v_range_1892_);
                            lean_dec(v_stx_1891_);
                            v___x_1932_ = lean_box(0);
                            return v___x_1932_;
                        }
                    } else {
                        lean_dec(v_val_1928_);
                        v___x_1933_ = lean_box(0);
                        v___x_1934_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___lam__0(v_stx_1891_, v_a_1896_, v___x_1914_, v_snd_1917_, v___x_1933_, v_fst_1916_);
                        v___y_1899_ = v___x_1934_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg___boxed(
    mut v_upperBound_1939_: *mut LeanObject,
    mut v_stx_1940_: *mut LeanObject,
    mut v_range_1941_: *mut LeanObject,
    mut v_stack_1942_: *mut LeanObject,
    mut v_preferred_1943_: *mut LeanObject,
    mut v___x_1944_: *mut LeanObject,
    mut v_a_1945_: *mut LeanObject,
    mut v_b_1946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4665__boxed_1947_: u8 = 0;
    let mut v_res_1948_: *mut LeanObject = core::ptr::null_mut();
    v___x_4665__boxed_1947_ = (lean_unbox(v___x_1944_) as u8);
    v_res_1948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_1939_, v_stx_1940_, v_range_1941_, v_stack_1942_, v_preferred_1943_, v___x_4665__boxed_1947_, v_a_1945_, v_b_1946_);
    lean_dec(v_upperBound_1939_);
    return v_res_1948_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg___boxed(
    mut v___y_1949_: *mut LeanObject,
    mut v___x_1950_: *mut LeanObject,
    mut v___x_1951_: *mut LeanObject,
    mut v_range_1952_: *mut LeanObject,
    mut v___x_1953_: *mut LeanObject,
    mut v_preferred_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
    mut v_b_1956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4696__boxed_1957_: u8 = 0;
    let mut v_res_1958_: *mut LeanObject = core::ptr::null_mut();
    v___x_4696__boxed_1957_ = (lean_unbox(v___x_1950_) as u8);
    v_res_1958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_1949_, v___x_4696__boxed_1957_, v___x_1951_, v_range_1952_, v___x_1953_, v_preferred_1954_, v_a_1955_, v_b_1956_);
    lean_dec(v___y_1949_);
    return v_res_1958_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(
    mut v_upperBound_1959_: *mut LeanObject,
    mut v_stx_1960_: *mut LeanObject,
    mut v_range_1961_: *mut LeanObject,
    mut v_stack_1962_: *mut LeanObject,
    mut v_preferred_1963_: *mut LeanObject,
    mut v___x_1964_: u8,
    mut v_inst_1965_: *mut LeanObject,
    mut v_R_1966_: *mut LeanObject,
    mut v_a_1967_: *mut LeanObject,
    mut v_b_1968_: *mut LeanObject,
    mut v_c_1969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    v___x_1970_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___redArg(v_upperBound_1959_, v_stx_1960_, v_range_1961_, v_stack_1962_, v_preferred_1963_, v___x_1964_, v_a_1967_, v_b_1968_);
    return v___x_1970_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0___boxed(
    mut v_upperBound_1971_: *mut LeanObject,
    mut v_stx_1972_: *mut LeanObject,
    mut v_range_1973_: *mut LeanObject,
    mut v_stack_1974_: *mut LeanObject,
    mut v_preferred_1975_: *mut LeanObject,
    mut v___x_1976_: *mut LeanObject,
    mut v_inst_1977_: *mut LeanObject,
    mut v_R_1978_: *mut LeanObject,
    mut v_a_1979_: *mut LeanObject,
    mut v_b_1980_: *mut LeanObject,
    mut v_c_1981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5068__boxed_1982_: u8 = 0;
    let mut v_res_1983_: *mut LeanObject = core::ptr::null_mut();
    v___x_5068__boxed_1982_ = (lean_unbox(v___x_1976_) as u8);
    v_res_1983_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__0(v_upperBound_1971_, v_stx_1972_, v_range_1973_, v_stack_1974_, v_preferred_1975_, v___x_5068__boxed_1982_, v_inst_1977_, v_R_1978_, v_a_1979_, v_b_1980_, v_c_1981_);
    lean_dec(v_upperBound_1971_);
    return v_res_1983_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(
    mut v___y_1984_: *mut LeanObject,
    mut v___x_1985_: u8,
    mut v___x_1986_: *mut LeanObject,
    mut v_range_1987_: *mut LeanObject,
    mut v___x_1988_: *mut LeanObject,
    mut v_preferred_1989_: *mut LeanObject,
    mut v_inst_1990_: *mut LeanObject,
    mut v_R_1991_: *mut LeanObject,
    mut v_a_1992_: *mut LeanObject,
    mut v_b_1993_: *mut LeanObject,
    mut v_c_1994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    v___x_1995_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___redArg(v___y_1984_, v___x_1985_, v___x_1986_, v_range_1987_, v___x_1988_, v_preferred_1989_, v_a_1992_, v_b_1993_);
    return v___x_1995_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1___boxed(
    mut v___y_1996_: *mut LeanObject,
    mut v___x_1997_: *mut LeanObject,
    mut v___x_1998_: *mut LeanObject,
    mut v_range_1999_: *mut LeanObject,
    mut v___x_2000_: *mut LeanObject,
    mut v_preferred_2001_: *mut LeanObject,
    mut v_inst_2002_: *mut LeanObject,
    mut v_R_2003_: *mut LeanObject,
    mut v_a_2004_: *mut LeanObject,
    mut v_b_2005_: *mut LeanObject,
    mut v_c_2006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5079__boxed_2007_: u8 = 0;
    let mut v_res_2008_: *mut LeanObject = core::ptr::null_mut();
    v___x_5079__boxed_2007_ = (lean_unbox(v___x_1997_) as u8);
    v_res_2008_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__1(v___y_1996_, v___x_5079__boxed_2007_, v___x_1998_, v_range_1999_, v___x_2000_, v_preferred_2001_, v_inst_2002_, v_R_2003_, v_a_2004_, v_b_2005_, v_c_2006_);
    lean_dec(v___y_1996_);
    return v_res_2008_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(
    mut v_upperBound_2009_: *mut LeanObject,
    mut v___x_2010_: *mut LeanObject,
    mut v_range_2011_: *mut LeanObject,
    mut v_inst_2012_: *mut LeanObject,
    mut v_R_2013_: *mut LeanObject,
    mut v_a_2014_: *mut LeanObject,
    mut v_b_2015_: *mut LeanObject,
    mut v_c_2016_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    v___x_2017_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___redArg(v_upperBound_2009_, v___x_2010_, v_range_2011_, v_a_2014_, v_b_2015_);
    return v___x_2017_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2___boxed(
    mut v_upperBound_2018_: *mut LeanObject,
    mut v___x_2019_: *mut LeanObject,
    mut v_range_2020_: *mut LeanObject,
    mut v_inst_2021_: *mut LeanObject,
    mut v_R_2022_: *mut LeanObject,
    mut v_a_2023_: *mut LeanObject,
    mut v_b_2024_: *mut LeanObject,
    mut v_c_2025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2026_: *mut LeanObject = core::ptr::null_mut();
    v_res_2026_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go_spec__2(v_upperBound_2018_, v___x_2019_, v_range_2020_, v_inst_2021_, v_R_2022_, v_a_2023_, v_b_2024_, v_c_2025_);
    lean_dec_ref(v_b_2024_);
    lean_dec(v___x_2019_);
    lean_dec(v_upperBound_2018_);
    return v_res_2026_;
}
pub unsafe fn l_Lean_CodeAction_findTactic_x3f(
    mut v_preferred_2027_: *mut LeanObject,
    mut v_range_2028_: *mut LeanObject,
    mut v_root_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    v___x_2030_ = lean_box(0);
    v___x_2031_ =
        l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_visit(
            v_range_2028_,
            v_root_2029_,
            v___x_2030_,
        );
    if lean_obj_tag(v___x_2031_) == 0 {
        lean_dec(v_root_2029_);
        lean_dec_ref(v_range_2028_);
        lean_dec_ref(v_preferred_2027_);
        return v___x_2030_;
    } else {
        let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_2031_, 1);
        v___x_2032_ = lean_box(0);
        v___x_2033_ =
            l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_findTactic_x3f_go(
                v_preferred_2027_,
                v_range_2028_,
                v___x_2032_,
                v_root_2029_,
                v___x_2030_,
            );
        if lean_obj_tag(v___x_2033_) == 0 {
            return v___x_2030_;
        } else {
            let mut v_val_2034_: *mut LeanObject = core::ptr::null_mut();
            v_val_2034_ = lean_ctor_get(v___x_2033_, 0);
            lean_inc(v_val_2034_);
            lean_dec_ref_known(v___x_2033_, 1);
            return v_val_2034_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(
    mut v_ctx_x3f_2047_: *mut LeanObject,
    mut v_i_2048_: *mut LeanObject,
    mut v_kind_2049_: *mut LeanObject,
    mut v_tgtRange_2050_: *mut LeanObject,
    mut v_f_2051_: *mut LeanObject,
    mut v_canonicalOnly_2052_: u8,
    mut v_as_2053_: *mut LeanObject,
    mut v_sz_2054_: usize,
    mut v_i_2055_: usize,
    mut v_b_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2071_: u8 = 0;
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2077_: u8 = 0;
    let mut v_unused_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: usize = 0;
    let mut v___x_2082_: usize = 0;
    let mut v_isSharedCheck_2084_: u8 = 0;
    let mut v_unused_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2057_ = lean_usize_dec_lt(v_i_2055_, v_sz_2054_);
                if v___x_2057_ == 0 {
                    lean_dec_ref(v_f_2051_);
                    lean_dec(v_ctx_x3f_2047_);
                    v___x_2058_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2058_, 0, v_b_2056_);
                    return v___x_2058_;
                } else {
                    v_snd_2059_ = lean_ctor_get(v_b_2056_, 1);
                    v_isSharedCheck_2084_ = (!lean_is_exclusive(v_b_2056_)) as u8;
                    if v_isSharedCheck_2084_ == 0 {
                        v_unused_2085_ = lean_ctor_get(v_b_2056_, 0);
                        lean_dec(v_unused_2085_);
                        v___x_2061_ = v_b_2056_;
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2059_);
                        lean_dec(v_b_2056_);
                        v___x_2061_ = lean_box(0);
                        v_isShared_2062_ = v_isSharedCheck_2084_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2063_ = lean_box(0);
                v_a_2064_ = lean_array_uget_borrowed(v_as_2053_, v_i_2055_);
                lean_inc(v_ctx_x3f_2047_);
                v___x_2065_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2047_, v_i_2048_);
                lean_inc_ref(v_f_2051_);
                lean_inc(v_a_2064_);
                v___x_2066_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2049_,
                    v_tgtRange_2050_,
                    v___x_2065_,
                    v_a_2064_,
                    v_f_2051_,
                    v_canonicalOnly_2052_,
                );
                if lean_obj_tag(v___x_2066_) == 1 {
                    lean_dec_ref(v_f_2051_);
                    lean_dec(v_ctx_x3f_2047_);
                    lean_inc_ref(v___x_2066_);
                    if v_isShared_2062_ == 0 {
                        lean_ctor_set(v___x_2061_, 1, v___x_2063_);
                        lean_ctor_set(v___x_2061_, 0, v___x_2066_);
                        v___x_2068_ = v___x_2061_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2066_);
                        lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2063_);
                        v___x_2068_ = v_reuseFailAlloc_2079_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2066_);
                    lean_del_object(v___x_2061_);
                    lean_dec(v_snd_2059_);
                    v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___closed__1;
                    v___x_2081_ = 1usize;
                    v___x_2082_ = lean_usize_add(v_i_2055_, v___x_2081_);
                    v_i_2055_ = v___x_2082_;
                    v_b_2056_ = v___x_2080_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_isSharedCheck_2077_ = (!lean_is_exclusive(v___x_2066_)) as u8;
                if v_isSharedCheck_2077_ == 0 {
                    v_unused_2078_ = lean_ctor_get(v___x_2066_, 0);
                    lean_dec(v_unused_2078_);
                    v___x_2070_ = v___x_2066_;
                    v_isShared_2071_ = v_isSharedCheck_2077_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_2066_);
                    v___x_2070_ = lean_box(0);
                    v_isShared_2071_ = v_isSharedCheck_2077_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2071_ == 0 {
                    lean_ctor_set(v___x_2070_, 0, v___x_2068_);
                    v___x_2073_ = v___x_2070_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2068_);
                    v___x_2073_ = v_reuseFailAlloc_2076_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2074_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2074_, 0, v___x_2073_);
                lean_ctor_set(v___x_2074_, 1, v_snd_2059_);
                v___x_2075_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2075_, 0, v___x_2074_);
                return v___x_2075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(
    mut v_ctx_x3f_2086_: *mut LeanObject,
    mut v_i_2087_: *mut LeanObject,
    mut v_kind_2088_: *mut LeanObject,
    mut v_tgtRange_2089_: *mut LeanObject,
    mut v_f_2090_: *mut LeanObject,
    mut v_canonicalOnly_2091_: u8,
    mut v_as_2092_: *mut LeanObject,
    mut v_sz_2093_: usize,
    mut v_i_2094_: usize,
    mut v_b_2095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2096_: u8 = 0;
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2101_: u8 = 0;
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2110_: u8 = 0;
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2116_: u8 = 0;
    let mut v_unused_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: usize = 0;
    let mut v___x_2121_: usize = 0;
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2123_: u8 = 0;
    let mut v_unused_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2096_ = lean_usize_dec_lt(v_i_2094_, v_sz_2093_);
                if v___x_2096_ == 0 {
                    lean_dec_ref(v_f_2090_);
                    lean_dec(v_ctx_x3f_2086_);
                    v___x_2097_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2097_, 0, v_b_2095_);
                    return v___x_2097_;
                } else {
                    v_snd_2098_ = lean_ctor_get(v_b_2095_, 1);
                    v_isSharedCheck_2123_ = (!lean_is_exclusive(v_b_2095_)) as u8;
                    if v_isSharedCheck_2123_ == 0 {
                        v_unused_2124_ = lean_ctor_get(v_b_2095_, 0);
                        lean_dec(v_unused_2124_);
                        v___x_2100_ = v_b_2095_;
                        v_isShared_2101_ = v_isSharedCheck_2123_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2098_);
                        lean_dec(v_b_2095_);
                        v___x_2100_ = lean_box(0);
                        v_isShared_2101_ = v_isSharedCheck_2123_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2102_ = lean_box(0);
                v_a_2103_ = lean_array_uget_borrowed(v_as_2092_, v_i_2094_);
                lean_inc(v_ctx_x3f_2086_);
                v___x_2104_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2086_, v_i_2087_);
                lean_inc_ref(v_f_2090_);
                lean_inc(v_a_2103_);
                v___x_2105_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2088_,
                    v_tgtRange_2089_,
                    v___x_2104_,
                    v_a_2103_,
                    v_f_2090_,
                    v_canonicalOnly_2091_,
                );
                if lean_obj_tag(v___x_2105_) == 1 {
                    lean_dec_ref(v_f_2090_);
                    lean_dec(v_ctx_x3f_2086_);
                    lean_inc_ref(v___x_2105_);
                    if v_isShared_2101_ == 0 {
                        lean_ctor_set(v___x_2100_, 1, v___x_2102_);
                        lean_ctor_set(v___x_2100_, 0, v___x_2105_);
                        v___x_2107_ = v___x_2100_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2105_);
                        lean_ctor_set(v_reuseFailAlloc_2118_, 1, v___x_2102_);
                        v___x_2107_ = v_reuseFailAlloc_2118_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2105_);
                    lean_del_object(v___x_2100_);
                    lean_dec(v_snd_2098_);
                    v___x_2119_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__1;
                    v___x_2120_ = 1usize;
                    v___x_2121_ = lean_usize_add(v_i_2094_, v___x_2120_);
                    v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_2086_, v_i_2087_, v_kind_2088_, v_tgtRange_2089_, v_f_2090_, v_canonicalOnly_2091_, v_as_2092_, v_sz_2093_, v___x_2121_, v___x_2119_);
                    return v___x_2122_;
                }
            }
            2 => {
                v_isSharedCheck_2116_ = (!lean_is_exclusive(v___x_2105_)) as u8;
                if v_isSharedCheck_2116_ == 0 {
                    v_unused_2117_ = lean_ctor_get(v___x_2105_, 0);
                    lean_dec(v_unused_2117_);
                    v___x_2109_ = v___x_2105_;
                    v_isShared_2110_ = v_isSharedCheck_2116_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_2105_);
                    v___x_2109_ = lean_box(0);
                    v_isShared_2110_ = v_isSharedCheck_2116_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2110_ == 0 {
                    lean_ctor_set(v___x_2109_, 0, v___x_2107_);
                    v___x_2112_ = v___x_2109_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2107_);
                    v___x_2112_ = v_reuseFailAlloc_2115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2113_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2113_, 0, v___x_2112_);
                lean_ctor_set(v___x_2113_, 1, v_snd_2098_);
                v___x_2114_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2114_, 0, v___x_2113_);
                return v___x_2114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(
    mut v_ctx_x3f_2125_: *mut LeanObject,
    mut v_i_2126_: *mut LeanObject,
    mut v_kind_2127_: *mut LeanObject,
    mut v_tgtRange_2128_: *mut LeanObject,
    mut v_f_2129_: *mut LeanObject,
    mut v_canonicalOnly_2130_: u8,
    mut v_t_2131_: *mut LeanObject,
    mut v_init_2132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2140_: u8 = 0;
    let mut v_a_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2148_: usize = 0;
    let mut v___x_2149_: usize = 0;
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v_fst_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2133_ = lean_ctor_get(v_t_2131_, 0);
                v_tail_2134_ = lean_ctor_get(v_t_2131_, 1);
                lean_inc_ref(v_f_2129_);
                lean_inc(v_ctx_x3f_2125_);
                lean_inc_ref(v_init_2132_);
                v___x_2135_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_2132_, v_ctx_x3f_2125_, v_i_2126_, v_kind_2127_, v_tgtRange_2128_, v_f_2129_, v_canonicalOnly_2130_, v_root_2133_, v_init_2132_);
                lean_dec_ref(v_init_2132_);
                if lean_obj_tag(v___x_2135_) == 0 {
                    lean_dec_ref(v_f_2129_);
                    lean_dec(v_ctx_x3f_2125_);
                    v___x_2136_ = lean_box(0);
                    return v___x_2136_;
                } else {
                    v_val_2137_ = lean_ctor_get(v___x_2135_, 0);
                    v_isSharedCheck_2161_ = (!lean_is_exclusive(v___x_2135_)) as u8;
                    if v_isSharedCheck_2161_ == 0 {
                        v___x_2139_ = v___x_2135_;
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2137_);
                        lean_dec(v___x_2135_);
                        v___x_2139_ = lean_box(0);
                        v_isShared_2140_ = v_isSharedCheck_2161_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_val_2137_) == 0 {
                    lean_dec_ref(v_f_2129_);
                    lean_dec(v_ctx_x3f_2125_);
                    v_a_2141_ = lean_ctor_get(v_val_2137_, 0);
                    lean_inc(v_a_2141_);
                    lean_dec_ref_known(v_val_2137_, 1);
                    if v_isShared_2140_ == 0 {
                        lean_ctor_set(v___x_2139_, 0, v_a_2141_);
                        v___x_2143_ = v___x_2139_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2141_);
                        v___x_2143_ = v_reuseFailAlloc_2144_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2139_);
                    v_a_2145_ = lean_ctor_get(v_val_2137_, 0);
                    lean_inc(v_a_2145_);
                    lean_dec_ref_known(v_val_2137_, 1);
                    v___x_2146_ = lean_box(0);
                    v___x_2147_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2147_, 0, v___x_2146_);
                    lean_ctor_set(v___x_2147_, 1, v_a_2145_);
                    v_sz_2148_ = lean_array_size(v_tail_2134_);
                    v___x_2149_ = 0usize;
                    v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_2125_, v_i_2126_, v_kind_2127_, v_tgtRange_2128_, v_f_2129_, v_canonicalOnly_2130_, v_tail_2134_, v_sz_2148_, v___x_2149_, v___x_2147_);
                    if lean_obj_tag(v___x_2150_) == 0 {
                        return v___x_2146_;
                    } else {
                        v_val_2151_ = lean_ctor_get(v___x_2150_, 0);
                        v_isSharedCheck_2160_ = (!lean_is_exclusive(v___x_2150_)) as u8;
                        if v_isSharedCheck_2160_ == 0 {
                            v___x_2153_ = v___x_2150_;
                            v_isShared_2154_ = v_isSharedCheck_2160_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2151_);
                            lean_dec(v___x_2150_);
                            v___x_2153_ = lean_box(0);
                            v_isShared_2154_ = v_isSharedCheck_2160_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2143_;
            }
            3 => {
                v_fst_2155_ = lean_ctor_get(v_val_2151_, 0);
                if lean_obj_tag(v_fst_2155_) == 0 {
                    v_snd_2156_ = lean_ctor_get(v_val_2151_, 1);
                    lean_inc(v_snd_2156_);
                    lean_dec(v_val_2151_);
                    if v_isShared_2154_ == 0 {
                        lean_ctor_set(v___x_2153_, 0, v_snd_2156_);
                        v___x_2158_ = v___x_2153_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_snd_2156_);
                        v___x_2158_ = v_reuseFailAlloc_2159_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2155_);
                    lean_del_object(v___x_2153_);
                    lean_dec(v_val_2151_);
                    return v_fst_2155_;
                }
            }
            4 => {
                return v___x_2158_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_findInfoTree_x3f(
    mut v_kind_2162_: *mut LeanObject,
    mut v_tgtRange_2163_: *mut LeanObject,
    mut v_ctx_x3f_2164_: *mut LeanObject,
    mut v_t_2165_: *mut LeanObject,
    mut v_f_2166_: *mut LeanObject,
    mut v_canonicalOnly_2167_: u8,
) -> *mut LeanObject {
    let mut v_i_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_children_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: u8 = 0;
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: u8 = 0;
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2187_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v_unused_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: u8 = 0;
    let mut v___x_2199_: u8 = 0;
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_t_2165_) {
                0 => {
                    v_i_2168_ = lean_ctor_get(v_t_2165_, 0);
                    lean_inc_ref(v_i_2168_);
                    v_t_2169_ = lean_ctor_get(v_t_2165_, 1);
                    lean_inc_ref(v_t_2169_);
                    lean_dec_ref_known(v_t_2165_, 2);
                    v___x_2170_ = l_Lean_Elab_PartialContextInfo_mergeIntoOuter_x3f(
                        v_i_2168_,
                        v_ctx_x3f_2164_,
                    );
                    v_ctx_x3f_2164_ = v___x_2170_;
                    v_t_2165_ = v_t_2169_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_i_2172_ = lean_ctor_get(v_t_2165_, 0);
                    v_children_2173_ = lean_ctor_get(v_t_2165_, 1);
                    if lean_obj_tag(v_ctx_x3f_2164_) == 1 {
                        v_val_2180_ = lean_ctor_get(v_ctx_x3f_2164_, 0);
                        v___x_2194_ = l_Lean_Elab_Info_stx(v_i_2172_);
                        v___x_2195_ =
                            l_Lean_Syntax_getRange_x3f(v___x_2194_, v_canonicalOnly_2167_);
                        if lean_obj_tag(v___x_2195_) == 1 {
                            v_val_2196_ = lean_ctor_get(v___x_2195_, 0);
                            lean_inc(v_val_2196_);
                            lean_dec_ref_known(v___x_2195_, 1);
                            v___x_2197_ = l_Lean_Syntax_getKind(v___x_2194_);
                            v___x_2198_ = lean_name_eq(v___x_2197_, v_kind_2162_);
                            lean_dec(v___x_2197_);
                            if v___x_2198_ == 0 {
                                lean_dec(v_val_2196_);
                                v___y_2182_ = v___x_2198_;
                                state = 2;
                                continue;
                            } else {
                                v___x_2199_ =
                                    l_Lean_Syntax_instBEqRange_beq(v_val_2196_, v_tgtRange_2163_);
                                lean_dec(v_val_2196_);
                                v___y_2182_ = v___x_2199_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_inc_ref(v_children_2173_);
                            lean_inc_ref(v_i_2172_);
                            lean_dec(v___x_2195_);
                            lean_dec(v___x_2194_);
                            lean_dec_ref_known(v_t_2165_, 2);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_inc_ref(v_children_2173_);
                        lean_inc_ref(v_i_2172_);
                        lean_dec_ref_known(v_t_2165_, 2);
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    lean_dec_ref(v_f_2166_);
                    lean_dec_ref(v_t_2165_);
                    lean_dec(v_ctx_x3f_2164_);
                    v___x_2200_ = lean_box(0);
                    return v___x_2200_;
                }
            },
            1 => {
                v___x_2175_ = lean_box(0);
                v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___closed__0;
                v___x_2177_ =
                    l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(
                        v_ctx_x3f_2164_,
                        v_i_2172_,
                        v_kind_2162_,
                        v_tgtRange_2163_,
                        v_f_2166_,
                        v_canonicalOnly_2167_,
                        v_children_2173_,
                        v___x_2176_,
                    );
                lean_dec_ref(v_children_2173_);
                lean_dec_ref(v_i_2172_);
                if lean_obj_tag(v___x_2177_) == 0 {
                    return v___x_2175_;
                } else {
                    v_val_2178_ = lean_ctor_get(v___x_2177_, 0);
                    lean_inc(v_val_2178_);
                    lean_dec_ref_known(v___x_2177_, 1);
                    v_fst_2179_ = lean_ctor_get(v_val_2178_, 0);
                    lean_inc(v_fst_2179_);
                    lean_dec(v_val_2178_);
                    if lean_obj_tag(v_fst_2179_) == 0 {
                        return v___x_2175_;
                    } else {
                        return v_fst_2179_;
                    }
                }
            }
            2 => {
                if v___y_2182_ == 0 {
                    lean_inc_ref(v_children_2173_);
                    lean_inc_ref(v_i_2172_);
                    lean_dec_ref_known(v_t_2165_, 2);
                    state = 1;
                    continue;
                } else {
                    lean_inc_ref(v_f_2166_);
                    lean_inc_ref(v_i_2172_);
                    lean_inc(v_val_2180_);
                    v___x_2183_ = lean_apply_2(v_f_2166_, v_val_2180_, v_i_2172_);
                    v___x_2184_ = (lean_unbox(v___x_2183_) as u8);
                    if v___x_2184_ == 0 {
                        lean_inc_ref(v_children_2173_);
                        lean_inc_ref(v_i_2172_);
                        lean_dec_ref_known(v_t_2165_, 2);
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_2180_);
                        lean_dec_ref(v_f_2166_);
                        v_isSharedCheck_2192_ = (!lean_is_exclusive(v_ctx_x3f_2164_)) as u8;
                        if v_isSharedCheck_2192_ == 0 {
                            v_unused_2193_ = lean_ctor_get(v_ctx_x3f_2164_, 0);
                            lean_dec(v_unused_2193_);
                            v___x_2186_ = v_ctx_x3f_2164_;
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_ctx_x3f_2164_);
                            v___x_2186_ = lean_box(0);
                            v_isShared_2187_ = v_isSharedCheck_2192_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_2188_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2188_, 0, v_val_2180_);
                lean_ctor_set(v___x_2188_, 1, v_t_2165_);
                if v_isShared_2187_ == 0 {
                    lean_ctor_set(v___x_2186_, 0, v___x_2188_);
                    v___x_2190_ = v___x_2186_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 0, v___x_2188_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2190_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(
    mut v_ctx_x3f_2210_: *mut LeanObject,
    mut v_i_2211_: *mut LeanObject,
    mut v_kind_2212_: *mut LeanObject,
    mut v_tgtRange_2213_: *mut LeanObject,
    mut v_f_2214_: *mut LeanObject,
    mut v_canonicalOnly_2215_: u8,
    mut v_as_2216_: *mut LeanObject,
    mut v_sz_2217_: usize,
    mut v_i_2218_: usize,
    mut v_b_2219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2225_: u8 = 0;
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2241_: u8 = 0;
    let mut v_unused_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: usize = 0;
    let mut v___x_2246_: usize = 0;
    let mut v_isSharedCheck_2248_: u8 = 0;
    let mut v_unused_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2220_ = lean_usize_dec_lt(v_i_2218_, v_sz_2217_);
                if v___x_2220_ == 0 {
                    lean_dec_ref(v_f_2214_);
                    lean_dec(v_ctx_x3f_2210_);
                    v___x_2221_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2221_, 0, v_b_2219_);
                    return v___x_2221_;
                } else {
                    v_snd_2222_ = lean_ctor_get(v_b_2219_, 1);
                    v_isSharedCheck_2248_ = (!lean_is_exclusive(v_b_2219_)) as u8;
                    if v_isSharedCheck_2248_ == 0 {
                        v_unused_2249_ = lean_ctor_get(v_b_2219_, 0);
                        lean_dec(v_unused_2249_);
                        v___x_2224_ = v_b_2219_;
                        v_isShared_2225_ = v_isSharedCheck_2248_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2222_);
                        lean_dec(v_b_2219_);
                        v___x_2224_ = lean_box(0);
                        v_isShared_2225_ = v_isSharedCheck_2248_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2226_ = lean_box(0);
                v_a_2227_ = lean_array_uget_borrowed(v_as_2216_, v_i_2218_);
                lean_inc(v_ctx_x3f_2210_);
                v___x_2228_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2210_, v_i_2211_);
                lean_inc_ref(v_f_2214_);
                lean_inc(v_a_2227_);
                v___x_2229_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2212_,
                    v_tgtRange_2213_,
                    v___x_2228_,
                    v_a_2227_,
                    v_f_2214_,
                    v_canonicalOnly_2215_,
                );
                if lean_obj_tag(v___x_2229_) == 1 {
                    lean_dec_ref(v_f_2214_);
                    lean_dec(v_ctx_x3f_2210_);
                    lean_inc_ref(v___x_2229_);
                    if v_isShared_2225_ == 0 {
                        lean_ctor_set(v___x_2224_, 1, v___x_2226_);
                        lean_ctor_set(v___x_2224_, 0, v___x_2229_);
                        v___x_2231_ = v___x_2224_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2243_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2243_, 0, v___x_2229_);
                        lean_ctor_set(v_reuseFailAlloc_2243_, 1, v___x_2226_);
                        v___x_2231_ = v_reuseFailAlloc_2243_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2229_);
                    lean_del_object(v___x_2224_);
                    lean_dec(v_snd_2222_);
                    v___x_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___closed__1;
                    v___x_2245_ = 1usize;
                    v___x_2246_ = lean_usize_add(v_i_2218_, v___x_2245_);
                    v_i_2218_ = v___x_2246_;
                    v_b_2219_ = v___x_2244_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v_isSharedCheck_2241_ = (!lean_is_exclusive(v___x_2229_)) as u8;
                if v_isSharedCheck_2241_ == 0 {
                    v_unused_2242_ = lean_ctor_get(v___x_2229_, 0);
                    lean_dec(v_unused_2242_);
                    v___x_2233_ = v___x_2229_;
                    v_isShared_2234_ = v_isSharedCheck_2241_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_2229_);
                    v___x_2233_ = lean_box(0);
                    v_isShared_2234_ = v_isSharedCheck_2241_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2234_ == 0 {
                    lean_ctor_set_tag(v___x_2233_, 0);
                    lean_ctor_set(v___x_2233_, 0, v___x_2231_);
                    v___x_2236_ = v___x_2233_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2231_);
                    v___x_2236_ = v_reuseFailAlloc_2240_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2237_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2237_, 0, v___x_2236_);
                v___x_2238_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2238_, 0, v___x_2237_);
                lean_ctor_set(v___x_2238_, 1, v_snd_2222_);
                v___x_2239_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2239_, 0, v___x_2238_);
                return v___x_2239_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(
    mut v_ctx_x3f_2250_: *mut LeanObject,
    mut v_i_2251_: *mut LeanObject,
    mut v_kind_2252_: *mut LeanObject,
    mut v_tgtRange_2253_: *mut LeanObject,
    mut v_f_2254_: *mut LeanObject,
    mut v_canonicalOnly_2255_: u8,
    mut v_as_2256_: *mut LeanObject,
    mut v_sz_2257_: usize,
    mut v_i_2258_: usize,
    mut v_b_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2260_: u8 = 0;
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2281_: u8 = 0;
    let mut v_unused_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: usize = 0;
    let mut v___x_2286_: usize = 0;
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut v_unused_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2260_ = lean_usize_dec_lt(v_i_2258_, v_sz_2257_);
                if v___x_2260_ == 0 {
                    lean_dec_ref(v_f_2254_);
                    lean_dec(v_ctx_x3f_2250_);
                    v___x_2261_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2261_, 0, v_b_2259_);
                    return v___x_2261_;
                } else {
                    v_snd_2262_ = lean_ctor_get(v_b_2259_, 1);
                    v_isSharedCheck_2288_ = (!lean_is_exclusive(v_b_2259_)) as u8;
                    if v_isSharedCheck_2288_ == 0 {
                        v_unused_2289_ = lean_ctor_get(v_b_2259_, 0);
                        lean_dec(v_unused_2289_);
                        v___x_2264_ = v_b_2259_;
                        v_isShared_2265_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2262_);
                        lean_dec(v_b_2259_);
                        v___x_2264_ = lean_box(0);
                        v_isShared_2265_ = v_isSharedCheck_2288_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2266_ = lean_box(0);
                v_a_2267_ = lean_array_uget_borrowed(v_as_2256_, v_i_2258_);
                lean_inc(v_ctx_x3f_2250_);
                v___x_2268_ = l_Lean_Elab_Info_updateContext_x3f(v_ctx_x3f_2250_, v_i_2251_);
                lean_inc_ref(v_f_2254_);
                lean_inc(v_a_2267_);
                v___x_2269_ = l_Lean_CodeAction_findInfoTree_x3f(
                    v_kind_2252_,
                    v_tgtRange_2253_,
                    v___x_2268_,
                    v_a_2267_,
                    v_f_2254_,
                    v_canonicalOnly_2255_,
                );
                if lean_obj_tag(v___x_2269_) == 1 {
                    lean_dec_ref(v_f_2254_);
                    lean_dec(v_ctx_x3f_2250_);
                    lean_inc_ref(v___x_2269_);
                    if v_isShared_2265_ == 0 {
                        lean_ctor_set(v___x_2264_, 1, v___x_2266_);
                        lean_ctor_set(v___x_2264_, 0, v___x_2269_);
                        v___x_2271_ = v___x_2264_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___x_2269_);
                        lean_ctor_set(v_reuseFailAlloc_2283_, 1, v___x_2266_);
                        v___x_2271_ = v_reuseFailAlloc_2283_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2269_);
                    lean_del_object(v___x_2264_);
                    lean_dec(v_snd_2262_);
                    v___x_2284_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___closed__0;
                    v___x_2285_ = 1usize;
                    v___x_2286_ = lean_usize_add(v_i_2258_, v___x_2285_);
                    v___x_2287_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_2250_, v_i_2251_, v_kind_2252_, v_tgtRange_2253_, v_f_2254_, v_canonicalOnly_2255_, v_as_2256_, v_sz_2257_, v___x_2286_, v___x_2284_);
                    return v___x_2287_;
                }
            }
            2 => {
                v_isSharedCheck_2281_ = (!lean_is_exclusive(v___x_2269_)) as u8;
                if v_isSharedCheck_2281_ == 0 {
                    v_unused_2282_ = lean_ctor_get(v___x_2269_, 0);
                    lean_dec(v_unused_2282_);
                    v___x_2273_ = v___x_2269_;
                    v_isShared_2274_ = v_isSharedCheck_2281_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_2269_);
                    v___x_2273_ = lean_box(0);
                    v_isShared_2274_ = v_isSharedCheck_2281_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2274_ == 0 {
                    lean_ctor_set_tag(v___x_2273_, 0);
                    lean_ctor_set(v___x_2273_, 0, v___x_2271_);
                    v___x_2276_ = v___x_2273_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2280_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2277_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2277_, 0, v___x_2276_);
                v___x_2278_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2278_, 0, v___x_2277_);
                lean_ctor_set(v___x_2278_, 1, v_snd_2262_);
                v___x_2279_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2279_, 0, v___x_2278_);
                return v___x_2279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(
    mut v_init_2290_: *mut LeanObject,
    mut v_ctx_x3f_2291_: *mut LeanObject,
    mut v_i_2292_: *mut LeanObject,
    mut v_kind_2293_: *mut LeanObject,
    mut v_tgtRange_2294_: *mut LeanObject,
    mut v_f_2295_: *mut LeanObject,
    mut v_canonicalOnly_2296_: u8,
    mut v_n_2297_: *mut LeanObject,
    mut v_b_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2302_: usize = 0;
    let mut v___x_2303_: usize = 0;
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2308_: u8 = 0;
    let mut v_fst_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2315_: u8 = 0;
    let mut v_vs_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2319_: usize = 0;
    let mut v___x_2320_: usize = 0;
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2325_: u8 = 0;
    let mut v_fst_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2332_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_2297_) == 0 {
                    v_cs_2299_ = lean_ctor_get(v_n_2297_, 0);
                    v___x_2300_ = lean_box(0);
                    v___x_2301_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2301_, 0, v___x_2300_);
                    lean_ctor_set(v___x_2301_, 1, v_b_2298_);
                    v_sz_2302_ = lean_array_size(v_cs_2299_);
                    v___x_2303_ = 0usize;
                    v___x_2304_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_2290_, v_ctx_x3f_2291_, v_i_2292_, v_kind_2293_, v_tgtRange_2294_, v_f_2295_, v_canonicalOnly_2296_, v_cs_2299_, v_sz_2302_, v___x_2303_, v___x_2301_);
                    if lean_obj_tag(v___x_2304_) == 0 {
                        return v___x_2300_;
                    } else {
                        v_val_2305_ = lean_ctor_get(v___x_2304_, 0);
                        v_isSharedCheck_2315_ = (!lean_is_exclusive(v___x_2304_)) as u8;
                        if v_isSharedCheck_2315_ == 0 {
                            v___x_2307_ = v___x_2304_;
                            v_isShared_2308_ = v_isSharedCheck_2315_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_2305_);
                            lean_dec(v___x_2304_);
                            v___x_2307_ = lean_box(0);
                            v_isShared_2308_ = v_isSharedCheck_2315_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_vs_2316_ = lean_ctor_get(v_n_2297_, 0);
                    v___x_2317_ = lean_box(0);
                    v___x_2318_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2318_, 0, v___x_2317_);
                    lean_ctor_set(v___x_2318_, 1, v_b_2298_);
                    v_sz_2319_ = lean_array_size(v_vs_2316_);
                    v___x_2320_ = 0usize;
                    v___x_2321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_2291_, v_i_2292_, v_kind_2293_, v_tgtRange_2294_, v_f_2295_, v_canonicalOnly_2296_, v_vs_2316_, v_sz_2319_, v___x_2320_, v___x_2318_);
                    if lean_obj_tag(v___x_2321_) == 0 {
                        return v___x_2317_;
                    } else {
                        v_val_2322_ = lean_ctor_get(v___x_2321_, 0);
                        v_isSharedCheck_2332_ = (!lean_is_exclusive(v___x_2321_)) as u8;
                        if v_isSharedCheck_2332_ == 0 {
                            v___x_2324_ = v___x_2321_;
                            v_isShared_2325_ = v_isSharedCheck_2332_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_2322_);
                            lean_dec(v___x_2321_);
                            v___x_2324_ = lean_box(0);
                            v_isShared_2325_ = v_isSharedCheck_2332_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2309_ = lean_ctor_get(v_val_2305_, 0);
                if lean_obj_tag(v_fst_2309_) == 0 {
                    v_snd_2310_ = lean_ctor_get(v_val_2305_, 1);
                    lean_inc(v_snd_2310_);
                    lean_dec(v_val_2305_);
                    v___x_2311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2311_, 0, v_snd_2310_);
                    if v_isShared_2308_ == 0 {
                        lean_ctor_set(v___x_2307_, 0, v___x_2311_);
                        v___x_2313_ = v___x_2307_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2314_, 0, v___x_2311_);
                        v___x_2313_ = v_reuseFailAlloc_2314_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2309_);
                    lean_del_object(v___x_2307_);
                    lean_dec(v_val_2305_);
                    return v_fst_2309_;
                }
            }
            2 => {
                return v___x_2313_;
            }
            3 => {
                v_fst_2326_ = lean_ctor_get(v_val_2322_, 0);
                if lean_obj_tag(v_fst_2326_) == 0 {
                    v_snd_2327_ = lean_ctor_get(v_val_2322_, 1);
                    lean_inc(v_snd_2327_);
                    lean_dec(v_val_2322_);
                    v___x_2328_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2328_, 0, v_snd_2327_);
                    if v_isShared_2325_ == 0 {
                        lean_ctor_set(v___x_2324_, 0, v___x_2328_);
                        v___x_2330_ = v___x_2324_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
                        v___x_2330_ = v_reuseFailAlloc_2331_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2326_);
                    lean_del_object(v___x_2324_);
                    lean_dec(v_val_2322_);
                    return v_fst_2326_;
                }
            }
            4 => {
                return v___x_2330_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(
    mut v_init_2333_: *mut LeanObject,
    mut v_ctx_x3f_2334_: *mut LeanObject,
    mut v_i_2335_: *mut LeanObject,
    mut v_kind_2336_: *mut LeanObject,
    mut v_tgtRange_2337_: *mut LeanObject,
    mut v_f_2338_: *mut LeanObject,
    mut v_canonicalOnly_2339_: u8,
    mut v_as_2340_: *mut LeanObject,
    mut v_sz_2341_: usize,
    mut v_i_2342_: usize,
    mut v_b_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v_a_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2363_: u8 = 0;
    let mut v_unused_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: usize = 0;
    let mut v___x_2370_: usize = 0;
    let mut v_reuseFailAlloc_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2373_: u8 = 0;
    let mut v_unused_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2344_ = lean_usize_dec_lt(v_i_2342_, v_sz_2341_);
                if v___x_2344_ == 0 {
                    lean_dec_ref(v_f_2338_);
                    lean_dec(v_ctx_x3f_2334_);
                    v___x_2345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2345_, 0, v_b_2343_);
                    return v___x_2345_;
                } else {
                    v_snd_2346_ = lean_ctor_get(v_b_2343_, 1);
                    v_isSharedCheck_2373_ = (!lean_is_exclusive(v_b_2343_)) as u8;
                    if v_isSharedCheck_2373_ == 0 {
                        v_unused_2374_ = lean_ctor_get(v_b_2343_, 0);
                        lean_dec(v_unused_2374_);
                        v___x_2348_ = v_b_2343_;
                        v_isShared_2349_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2346_);
                        lean_dec(v_b_2343_);
                        v___x_2348_ = lean_box(0);
                        v_isShared_2349_ = v_isSharedCheck_2373_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2350_ = lean_array_uget_borrowed(v_as_2340_, v_i_2342_);
                lean_inc(v_snd_2346_);
                lean_inc_ref(v_f_2338_);
                lean_inc(v_ctx_x3f_2334_);
                v___x_2351_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_2333_, v_ctx_x3f_2334_, v_i_2335_, v_kind_2336_, v_tgtRange_2337_, v_f_2338_, v_canonicalOnly_2339_, v_a_2350_, v_snd_2346_);
                if lean_obj_tag(v___x_2351_) == 0 {
                    lean_del_object(v___x_2348_);
                    lean_dec(v_snd_2346_);
                    lean_dec_ref(v_f_2338_);
                    lean_dec(v_ctx_x3f_2334_);
                    v___x_2352_ = lean_box(0);
                    return v___x_2352_;
                } else {
                    v_val_2353_ = lean_ctor_get(v___x_2351_, 0);
                    lean_inc(v_val_2353_);
                    if lean_obj_tag(v_val_2353_) == 0 {
                        lean_dec_ref(v_f_2338_);
                        lean_dec(v_ctx_x3f_2334_);
                        v_isSharedCheck_2363_ = (!lean_is_exclusive(v_val_2353_)) as u8;
                        if v_isSharedCheck_2363_ == 0 {
                            v_unused_2364_ = lean_ctor_get(v_val_2353_, 0);
                            lean_dec(v_unused_2364_);
                            v___x_2355_ = v_val_2353_;
                            v_isShared_2356_ = v_isSharedCheck_2363_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v_val_2353_);
                            v___x_2355_ = lean_box(0);
                            v_isShared_2356_ = v_isSharedCheck_2363_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2351_, 1);
                        lean_dec(v_snd_2346_);
                        v_a_2365_ = lean_ctor_get(v_val_2353_, 0);
                        lean_inc(v_a_2365_);
                        lean_dec_ref_known(v_val_2353_, 1);
                        v___x_2366_ = lean_box(0);
                        if v_isShared_2349_ == 0 {
                            lean_ctor_set(v___x_2348_, 1, v_a_2365_);
                            lean_ctor_set(v___x_2348_, 0, v___x_2366_);
                            v___x_2368_ = v___x_2348_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2366_);
                            lean_ctor_set(v_reuseFailAlloc_2372_, 1, v_a_2365_);
                            v___x_2368_ = v_reuseFailAlloc_2372_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2349_ == 0 {
                    lean_ctor_set(v___x_2348_, 0, v___x_2351_);
                    v___x_2358_ = v___x_2348_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2351_);
                    lean_ctor_set(v_reuseFailAlloc_2362_, 1, v_snd_2346_);
                    v___x_2358_ = v_reuseFailAlloc_2362_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2356_ == 0 {
                    lean_ctor_set_tag(v___x_2355_, 1);
                    lean_ctor_set(v___x_2355_, 0, v___x_2358_);
                    v___x_2360_ = v___x_2355_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
                    v___x_2360_ = v_reuseFailAlloc_2361_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2360_;
            }
            5 => {
                v___x_2369_ = 1usize;
                v___x_2370_ = lean_usize_add(v_i_2342_, v___x_2369_);
                v_i_2342_ = v___x_2370_;
                v_b_2343_ = v___x_2368_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_init_2375_: *mut LeanObject,
    mut v_ctx_x3f_2376_: *mut LeanObject,
    mut v_i_2377_: *mut LeanObject,
    mut v_kind_2378_: *mut LeanObject,
    mut v_tgtRange_2379_: *mut LeanObject,
    mut v_f_2380_: *mut LeanObject,
    mut v_canonicalOnly_2381_: *mut LeanObject,
    mut v_as_2382_: *mut LeanObject,
    mut v_sz_2383_: *mut LeanObject,
    mut v_i_2384_: *mut LeanObject,
    mut v_b_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_2386_: u8 = 0;
    let mut v_sz_boxed_2387_: usize = 0;
    let mut v_i_boxed_2388_: usize = 0;
    let mut v_res_2389_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2386_ = (lean_unbox(v_canonicalOnly_2381_) as u8);
    v_sz_boxed_2387_ = lean_unbox_usize(v_sz_2383_);
    lean_dec(v_sz_2383_);
    v_i_boxed_2388_ = lean_unbox_usize(v_i_2384_);
    lean_dec(v_i_2384_);
    v_res_2389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__1(v_init_2375_, v_ctx_x3f_2376_, v_i_2377_, v_kind_2378_, v_tgtRange_2379_, v_f_2380_, v_canonicalOnly_boxed_2386_, v_as_2382_, v_sz_boxed_2387_, v_i_boxed_2388_, v_b_2385_);
    lean_dec_ref(v_as_2382_);
    lean_dec_ref(v_tgtRange_2379_);
    lean_dec(v_kind_2378_);
    lean_dec_ref(v_i_2377_);
    lean_dec_ref(v_init_2375_);
    return v_res_2389_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0___boxed(
    mut v_ctx_x3f_2390_: *mut LeanObject,
    mut v_i_2391_: *mut LeanObject,
    mut v_kind_2392_: *mut LeanObject,
    mut v_tgtRange_2393_: *mut LeanObject,
    mut v_f_2394_: *mut LeanObject,
    mut v_canonicalOnly_2395_: *mut LeanObject,
    mut v_t_2396_: *mut LeanObject,
    mut v_init_2397_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_2398_: u8 = 0;
    let mut v_res_2399_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2398_ = (lean_unbox(v_canonicalOnly_2395_) as u8);
    v_res_2399_ = l_Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0(
        v_ctx_x3f_2390_,
        v_i_2391_,
        v_kind_2392_,
        v_tgtRange_2393_,
        v_f_2394_,
        v_canonicalOnly_boxed_2398_,
        v_t_2396_,
        v_init_2397_,
    );
    lean_dec_ref(v_t_2396_);
    lean_dec_ref(v_tgtRange_2393_);
    lean_dec(v_kind_2392_);
    lean_dec_ref(v_i_2391_);
    return v_res_2399_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1___boxed(
    mut v_ctx_x3f_2400_: *mut LeanObject,
    mut v_i_2401_: *mut LeanObject,
    mut v_kind_2402_: *mut LeanObject,
    mut v_tgtRange_2403_: *mut LeanObject,
    mut v_f_2404_: *mut LeanObject,
    mut v_canonicalOnly_2405_: *mut LeanObject,
    mut v_as_2406_: *mut LeanObject,
    mut v_sz_2407_: *mut LeanObject,
    mut v_i_2408_: *mut LeanObject,
    mut v_b_2409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_2410_: u8 = 0;
    let mut v_sz_boxed_2411_: usize = 0;
    let mut v_i_boxed_2412_: usize = 0;
    let mut v_res_2413_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2410_ = (lean_unbox(v_canonicalOnly_2405_) as u8);
    v_sz_boxed_2411_ = lean_unbox_usize(v_sz_2407_);
    lean_dec(v_sz_2407_);
    v_i_boxed_2412_ = lean_unbox_usize(v_i_2408_);
    lean_dec(v_i_2408_);
    v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1(v_ctx_x3f_2400_, v_i_2401_, v_kind_2402_, v_tgtRange_2403_, v_f_2404_, v_canonicalOnly_boxed_2410_, v_as_2406_, v_sz_boxed_2411_, v_i_boxed_2412_, v_b_2409_);
    lean_dec_ref(v_as_2406_);
    lean_dec_ref(v_tgtRange_2403_);
    lean_dec(v_kind_2402_);
    lean_dec_ref(v_i_2401_);
    return v_res_2413_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4___boxed(
    mut v_ctx_x3f_2414_: *mut LeanObject,
    mut v_i_2415_: *mut LeanObject,
    mut v_kind_2416_: *mut LeanObject,
    mut v_tgtRange_2417_: *mut LeanObject,
    mut v_f_2418_: *mut LeanObject,
    mut v_canonicalOnly_2419_: *mut LeanObject,
    mut v_as_2420_: *mut LeanObject,
    mut v_sz_2421_: *mut LeanObject,
    mut v_i_2422_: *mut LeanObject,
    mut v_b_2423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_2424_: u8 = 0;
    let mut v_sz_boxed_2425_: usize = 0;
    let mut v_i_boxed_2426_: usize = 0;
    let mut v_res_2427_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2424_ = (lean_unbox(v_canonicalOnly_2419_) as u8);
    v_sz_boxed_2425_ = lean_unbox_usize(v_sz_2421_);
    lean_dec(v_sz_2421_);
    v_i_boxed_2426_ = lean_unbox_usize(v_i_2422_);
    lean_dec(v_i_2422_);
    v_res_2427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__1_spec__4(v_ctx_x3f_2414_, v_i_2415_, v_kind_2416_, v_tgtRange_2417_, v_f_2418_, v_canonicalOnly_boxed_2424_, v_as_2420_, v_sz_boxed_2425_, v_i_boxed_2426_, v_b_2423_);
    lean_dec_ref(v_as_2420_);
    lean_dec_ref(v_tgtRange_2417_);
    lean_dec(v_kind_2416_);
    lean_dec_ref(v_i_2415_);
    return v_res_2427_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_ctx_x3f_2428_: *mut LeanObject,
    mut v_i_2429_: *mut LeanObject,
    mut v_kind_2430_: *mut LeanObject,
    mut v_tgtRange_2431_: *mut LeanObject,
    mut v_f_2432_: *mut LeanObject,
    mut v_canonicalOnly_2433_: *mut LeanObject,
    mut v_as_2434_: *mut LeanObject,
    mut v_sz_2435_: *mut LeanObject,
    mut v_i_2436_: *mut LeanObject,
    mut v_b_2437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_2438_: u8 = 0;
    let mut v_sz_boxed_2439_: usize = 0;
    let mut v_i_boxed_2440_: usize = 0;
    let mut v_res_2441_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2438_ = (lean_unbox(v_canonicalOnly_2433_) as u8);
    v_sz_boxed_2439_ = lean_unbox_usize(v_sz_2435_);
    lean_dec(v_sz_2435_);
    v_i_boxed_2440_ = lean_unbox_usize(v_i_2436_);
    lean_dec(v_i_2436_);
    v_res_2441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2(v_ctx_x3f_2428_, v_i_2429_, v_kind_2430_, v_tgtRange_2431_, v_f_2432_, v_canonicalOnly_boxed_2438_, v_as_2434_, v_sz_boxed_2439_, v_i_boxed_2440_, v_b_2437_);
    lean_dec_ref(v_as_2434_);
    lean_dec_ref(v_tgtRange_2431_);
    lean_dec(v_kind_2430_);
    lean_dec_ref(v_i_2429_);
    return v_res_2441_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_ctx_x3f_2442_: *mut LeanObject,
    mut v_i_2443_: *mut LeanObject,
    mut v_kind_2444_: *mut LeanObject,
    mut v_tgtRange_2445_: *mut LeanObject,
    mut v_f_2446_: *mut LeanObject,
    mut v_canonicalOnly_2447_: *mut LeanObject,
    mut v_as_2448_: *mut LeanObject,
    mut v_sz_2449_: *mut LeanObject,
    mut v_i_2450_: *mut LeanObject,
    mut v_b_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_2452_: u8 = 0;
    let mut v_sz_boxed_2453_: usize = 0;
    let mut v_i_boxed_2454_: usize = 0;
    let mut v_res_2455_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2452_ = (lean_unbox(v_canonicalOnly_2447_) as u8);
    v_sz_boxed_2453_ = lean_unbox_usize(v_sz_2449_);
    lean_dec(v_sz_2449_);
    v_i_boxed_2454_ = lean_unbox_usize(v_i_2450_);
    lean_dec(v_i_2450_);
    v_res_2455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0_spec__2_spec__3(v_ctx_x3f_2442_, v_i_2443_, v_kind_2444_, v_tgtRange_2445_, v_f_2446_, v_canonicalOnly_boxed_2452_, v_as_2448_, v_sz_boxed_2453_, v_i_boxed_2454_, v_b_2451_);
    lean_dec_ref(v_as_2448_);
    lean_dec_ref(v_tgtRange_2445_);
    lean_dec(v_kind_2444_);
    lean_dec_ref(v_i_2443_);
    return v_res_2455_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0___boxed(
    mut v_init_2456_: *mut LeanObject,
    mut v_ctx_x3f_2457_: *mut LeanObject,
    mut v_i_2458_: *mut LeanObject,
    mut v_kind_2459_: *mut LeanObject,
    mut v_tgtRange_2460_: *mut LeanObject,
    mut v_f_2461_: *mut LeanObject,
    mut v_canonicalOnly_2462_: *mut LeanObject,
    mut v_n_2463_: *mut LeanObject,
    mut v_b_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_2465_: u8 = 0;
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2465_ = (lean_unbox(v_canonicalOnly_2462_) as u8);
    v_res_2466_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_CodeAction_findInfoTree_x3f_spec__0_spec__0(v_init_2456_, v_ctx_x3f_2457_, v_i_2458_, v_kind_2459_, v_tgtRange_2460_, v_f_2461_, v_canonicalOnly_boxed_2465_, v_n_2463_, v_b_2464_);
    lean_dec_ref(v_n_2463_);
    lean_dec_ref(v_tgtRange_2460_);
    lean_dec(v_kind_2459_);
    lean_dec_ref(v_i_2458_);
    lean_dec_ref(v_init_2456_);
    return v_res_2466_;
}
pub unsafe fn l_Lean_CodeAction_findInfoTree_x3f___boxed(
    mut v_kind_2467_: *mut LeanObject,
    mut v_tgtRange_2468_: *mut LeanObject,
    mut v_ctx_x3f_2469_: *mut LeanObject,
    mut v_t_2470_: *mut LeanObject,
    mut v_f_2471_: *mut LeanObject,
    mut v_canonicalOnly_2472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_canonicalOnly_boxed_2473_: u8 = 0;
    let mut v_res_2474_: *mut LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_2473_ = (lean_unbox(v_canonicalOnly_2472_) as u8);
    v_res_2474_ = l_Lean_CodeAction_findInfoTree_x3f(
        v_kind_2467_,
        v_tgtRange_2468_,
        v_ctx_x3f_2469_,
        v_t_2470_,
        v_f_2471_,
        v_canonicalOnly_boxed_2473_,
    );
    lean_dec_ref(v_tgtRange_2468_);
    lean_dec(v_kind_2467_);
    return v_res_2474_;
}
pub unsafe fn _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    v___x_2475_ = l_Lean_Server_instInhabitedRequestError_default;
    v___x_2476_ = lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___x_2476_, 0, lean_box(0));
    lean_closure_set(v___x_2476_, 1, lean_box(0));
    lean_closure_set(v___x_2476_, 2, v___x_2475_);
    return v___x_2476_;
}
pub unsafe fn l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(
    mut v_msg_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028__overap_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    v___x_2480_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___closed__0,
    );
    v___f_2481_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2481_, 0, v___x_2480_);
    v___x_4028__overap_2482_ = lean_panic_fn_borrowed(v___f_2481_, v_msg_2477_);
    lean_dec_ref(v___f_2481_);
    lean_inc_ref(v___y_2478_);
    v___x_2483_ = lean_apply_2(v___x_4028__overap_2482_, v___y_2478_, lean_box(0));
    return v___x_2483_;
}
pub unsafe fn l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0___boxed(
    mut v_msg_2484_: *mut LeanObject,
    mut v___y_2485_: *mut LeanObject,
    mut v___y_2486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2487_: *mut LeanObject = core::ptr::null_mut();
    v_res_2487_ =
        l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(v_msg_2484_, v___y_2485_);
    lean_dec_ref(v___y_2485_);
    return v_res_2487_;
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider___lam__0(
    mut v___x_2488_: *mut LeanObject,
    mut v___x_2489_: *mut LeanObject,
    mut v_ctx_2490_: *mut LeanObject,
    mut v_node_2491_: *mut LeanObject,
    mut v_result_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2494_: u8 = 0;
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: u8 = 0;
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_node_2491_) == 1 {
                    v_i_2497_ = lean_ctor_get(v_node_2491_, 0);
                    if lean_obj_tag(v_i_2497_) == 3 {
                        v_i_2498_ = lean_ctor_get(v_i_2497_, 0);
                        v_stx_2499_ = lean_ctor_get(v_i_2498_, 1);
                        v___x_2500_ = 1;
                        v___x_2501_ = l_Lean_Syntax_getPos_x3f(v_stx_2499_, v___x_2500_);
                        if lean_obj_tag(v___x_2501_) == 1 {
                            v_val_2502_ = lean_ctor_get(v___x_2501_, 0);
                            lean_inc(v_val_2502_);
                            lean_dec_ref_known(v___x_2501_, 1);
                            v___x_2503_ = l_Lean_Syntax_getTailPos_x3f(v_stx_2499_, v___x_2500_);
                            if lean_obj_tag(v___x_2503_) == 1 {
                                v_val_2504_ = lean_ctor_get(v___x_2503_, 0);
                                lean_inc(v_val_2504_);
                                lean_dec_ref_known(v___x_2503_, 1);
                                v___x_2505_ = lean_nat_dec_le(v_val_2502_, v___x_2488_);
                                lean_dec(v_val_2502_);
                                if v___x_2505_ == 0 {
                                    lean_dec(v_val_2504_);
                                    v___y_2494_ = v___x_2505_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2506_ = lean_nat_dec_le(v___x_2489_, v_val_2504_);
                                    lean_dec(v_val_2504_);
                                    v___y_2494_ = v___x_2506_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_2503_);
                                lean_dec(v_val_2502_);
                                lean_dec_ref_known(v_node_2491_, 2);
                                lean_dec_ref(v_ctx_2490_);
                                return v_result_2492_;
                            }
                        } else {
                            lean_dec(v___x_2501_);
                            lean_dec_ref_known(v_node_2491_, 2);
                            lean_dec_ref(v_ctx_2490_);
                            return v_result_2492_;
                        }
                    } else {
                        lean_dec_ref_known(v_node_2491_, 2);
                        lean_dec_ref(v_ctx_2490_);
                        return v_result_2492_;
                    }
                } else {
                    lean_dec_ref(v_node_2491_);
                    lean_dec_ref(v_ctx_2490_);
                    return v_result_2492_;
                }
            }
            1 => {
                if v___y_2494_ == 0 {
                    lean_dec_ref(v_node_2491_);
                    lean_dec_ref(v_ctx_2490_);
                    return v_result_2492_;
                } else {
                    v___x_2495_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2495_, 0, v_ctx_2490_);
                    lean_ctor_set(v___x_2495_, 1, v_node_2491_);
                    v___x_2496_ = lean_array_push(v_result_2492_, v___x_2495_);
                    return v___x_2496_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed(
    mut v___x_2507_: *mut LeanObject,
    mut v___x_2508_: *mut LeanObject,
    mut v_ctx_2509_: *mut LeanObject,
    mut v_node_2510_: *mut LeanObject,
    mut v_result_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2512_: *mut LeanObject = core::ptr::null_mut();
    v_res_2512_ = l_Lean_CodeAction_cmdCodeActionProvider___lam__0(
        v___x_2507_,
        v___x_2508_,
        v_ctx_2509_,
        v_node_2510_,
        v_result_2511_,
    );
    lean_dec(v___x_2508_);
    lean_dec(v___x_2507_);
    return v_res_2512_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(
    mut v_params_2513_: *mut LeanObject,
    mut v_snap_2514_: *mut LeanObject,
    mut v_fst_2515_: *mut LeanObject,
    mut v_snd_2516_: *mut LeanObject,
    mut v_as_2517_: *mut LeanObject,
    mut v_sz_2518_: usize,
    mut v_i_2519_: usize,
    mut v_b_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: usize = 0;
    let mut v___x_2526_: usize = 0;
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662__overap_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2528_ = lean_usize_dec_lt(v_i_2519_, v_sz_2518_);
                if v___x_2528_ == 0 {
                    lean_dec_ref(v_snd_2516_);
                    lean_dec_ref(v_fst_2515_);
                    lean_dec_ref(v_snap_2514_);
                    lean_dec_ref(v_params_2513_);
                    v___x_2529_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2529_, 0, v_b_2520_);
                    return v___x_2529_;
                } else {
                    v___x_4662__overap_2530_ = lean_array_uget_borrowed(v_as_2517_, v_i_2519_);
                    lean_inc(v___x_4662__overap_2530_);
                    lean_inc_ref(v___y_2521_);
                    lean_inc_ref(v_snd_2516_);
                    lean_inc_ref(v_fst_2515_);
                    lean_inc_ref(v_snap_2514_);
                    lean_inc_ref(v_params_2513_);
                    v___x_2531_ = lean_apply_6(
                        v___x_4662__overap_2530_,
                        v_params_2513_,
                        v_snap_2514_,
                        v_fst_2515_,
                        v_snd_2516_,
                        v___y_2521_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2531_) == 0 {
                        v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
                        lean_inc(v_a_2532_);
                        lean_dec_ref_known(v___x_2531_, 1);
                        v___x_2533_ = l_Array_append___redArg(v_b_2520_, v_a_2532_);
                        lean_dec(v_a_2532_);
                        v_snd_2524_ = v___x_2533_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref_known(v___x_2531_, 1);
                        v_snd_2524_ = v_b_2520_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2525_ = 1usize;
                v___x_2526_ = lean_usize_add(v_i_2519_, v___x_2525_);
                v_i_2519_ = v___x_2526_;
                v_b_2520_ = v_snd_2524_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1___boxed(
    mut v_params_2534_: *mut LeanObject,
    mut v_snap_2535_: *mut LeanObject,
    mut v_fst_2536_: *mut LeanObject,
    mut v_snd_2537_: *mut LeanObject,
    mut v_as_2538_: *mut LeanObject,
    mut v_sz_2539_: *mut LeanObject,
    mut v_i_2540_: *mut LeanObject,
    mut v_b_2541_: *mut LeanObject,
    mut v___y_2542_: *mut LeanObject,
    mut v___y_2543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2544_: usize = 0;
    let mut v_i_boxed_2545_: usize = 0;
    let mut v_res_2546_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2544_ = lean_unbox_usize(v_sz_2539_);
    lean_dec(v_sz_2539_);
    v_i_boxed_2545_ = lean_unbox_usize(v_i_2540_);
    lean_dec(v_i_2540_);
    v_res_2546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2534_, v_snap_2535_, v_fst_2536_, v_snd_2537_, v_as_2538_, v_sz_boxed_2544_, v_i_boxed_2545_, v_b_2541_, v___y_2542_);
    lean_dec_ref(v___y_2542_);
    lean_dec_ref(v_as_2538_);
    return v_res_2546_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    v___x_2550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__2;
    v___x_2551_ = lean_unsigned_to_nat(48);
    v___x_2552_ = lean_unsigned_to_nat(185);
    v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__1;
    v___x_2554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__0;
    v___x_2555_ = l_mkPanicMessageWithDecl(
        v___x_2554_,
        v___x_2553_,
        v___x_2552_,
        v___x_2551_,
        v___x_2550_,
    );
    return v___x_2555_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(
    mut v___x_2556_: *mut LeanObject,
    mut v_params_2557_: *mut LeanObject,
    mut v_snap_2558_: *mut LeanObject,
    mut v_as_2559_: *mut LeanObject,
    mut v_sz_2560_: usize,
    mut v_i_2561_: usize,
    mut v_b_2562_: *mut LeanObject,
    mut v___y_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: usize = 0;
    let mut v___x_2568_: usize = 0;
    let mut v___y_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2581_: u8 = 0;
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onAnyCmd_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2594_: usize = 0;
    let mut v___x_2595_: usize = 0;
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2602_: usize = 0;
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2582_ = lean_usize_dec_lt(v_i_2561_, v_sz_2560_);
                if v___x_2582_ == 0 {
                    lean_dec_ref(v_snap_2558_);
                    lean_dec_ref(v_params_2557_);
                    v___x_2583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2583_, 0, v_b_2562_);
                    return v___x_2583_;
                } else {
                    v_a_2584_ = lean_array_uget_borrowed(v_as_2559_, v_i_2561_);
                    v_snd_2585_ = lean_ctor_get(v_a_2584_, 1);
                    if lean_obj_tag(v_snd_2585_) == 1 {
                        v_i_2586_ = lean_ctor_get(v_snd_2585_, 0);
                        if lean_obj_tag(v_i_2586_) == 3 {
                            v_fst_2587_ = lean_ctor_get(v_a_2584_, 0);
                            v_i_2588_ = lean_ctor_get(v_i_2586_, 0);
                            v_onAnyCmd_2589_ = lean_ctor_get(v___x_2556_, 0);
                            v_onCmd_2590_ = lean_ctor_get(v___x_2556_, 1);
                            v_stx_2598_ = lean_ctor_get(v_i_2588_, 1);
                            lean_inc(v_stx_2598_);
                            v___x_2599_ = l_Lean_Syntax_getKind(v_stx_2598_);
                            v___x_2600_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_2590_, v___x_2599_);
                            lean_dec(v___x_2599_);
                            if lean_obj_tag(v___x_2600_) == 1 {
                                v_val_2601_ = lean_ctor_get(v___x_2600_, 0);
                                lean_inc(v_val_2601_);
                                lean_dec_ref_known(v___x_2600_, 1);
                                v_sz_2602_ = lean_array_size(v_val_2601_);
                                v___x_2603_ = 0usize;
                                lean_inc_ref(v_snd_2585_);
                                lean_inc(v_fst_2587_);
                                lean_inc_ref(v_snap_2558_);
                                lean_inc_ref(v_params_2557_);
                                v___x_2604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2557_, v_snap_2558_, v_fst_2587_, v_snd_2585_, v_val_2601_, v_sz_2602_, v___x_2603_, v_b_2562_, v___y_2563_);
                                lean_dec(v_val_2601_);
                                if lean_obj_tag(v___x_2604_) == 0 {
                                    v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
                                    lean_inc(v_a_2605_);
                                    lean_dec_ref_known(v___x_2604_, 1);
                                    v_out_2592_ = v_a_2605_;
                                    v___y_2593_ = v___y_2563_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec_ref(v_snap_2558_);
                                    lean_dec_ref(v_params_2557_);
                                    return v___x_2604_;
                                }
                            } else {
                                lean_dec(v___x_2600_);
                                v_out_2592_ = v_b_2562_;
                                v___y_2593_ = v___y_2563_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___y_2571_ = v___y_2563_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_2571_ = v___y_2563_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2567_ = 1usize;
                v___x_2568_ = lean_usize_add(v_i_2561_, v___x_2567_);
                v_i_2561_ = v___x_2568_;
                v_b_2562_ = v_a_2566_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2572_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
                v___x_2573_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(
                    v___x_2572_,
                    v___y_2571_,
                );
                if lean_obj_tag(v___x_2573_) == 0 {
                    lean_dec_ref_known(v___x_2573_, 1);
                    v_a_2566_ = v_b_2562_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_b_2562_);
                    lean_dec_ref(v_snap_2558_);
                    lean_dec_ref(v_params_2557_);
                    v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
                    v_isSharedCheck_2581_ = (!lean_is_exclusive(v___x_2573_)) as u8;
                    if v_isSharedCheck_2581_ == 0 {
                        v___x_2576_ = v___x_2573_;
                        v_isShared_2577_ = v_isSharedCheck_2581_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2574_);
                        lean_dec(v___x_2573_);
                        v___x_2576_ = lean_box(0);
                        v_isShared_2577_ = v_isSharedCheck_2581_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2577_ == 0 {
                    v___x_2579_ = v___x_2576_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
                    v___x_2579_ = v_reuseFailAlloc_2580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2579_;
            }
            5 => {
                v_sz_2594_ = lean_array_size(v_onAnyCmd_2589_);
                v___x_2595_ = 0usize;
                lean_inc_ref(v_snd_2585_);
                lean_inc(v_fst_2587_);
                lean_inc_ref(v_snap_2558_);
                lean_inc_ref(v_params_2557_);
                v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2557_, v_snap_2558_, v_fst_2587_, v_snd_2585_, v_onAnyCmd_2589_, v_sz_2594_, v___x_2595_, v_out_2592_, v___y_2593_);
                if lean_obj_tag(v___x_2596_) == 0 {
                    v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
                    lean_inc(v_a_2597_);
                    lean_dec_ref_known(v___x_2596_, 1);
                    v_a_2566_ = v_a_2597_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_snap_2558_);
                    lean_dec_ref(v_params_2557_);
                    return v___x_2596_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___boxed(
    mut v___x_2606_: *mut LeanObject,
    mut v_params_2607_: *mut LeanObject,
    mut v_snap_2608_: *mut LeanObject,
    mut v_as_2609_: *mut LeanObject,
    mut v_sz_2610_: *mut LeanObject,
    mut v_i_2611_: *mut LeanObject,
    mut v_b_2612_: *mut LeanObject,
    mut v___y_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2615_: usize = 0;
    let mut v_i_boxed_2616_: usize = 0;
    let mut v_res_2617_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2615_ = lean_unbox_usize(v_sz_2610_);
    lean_dec(v_sz_2610_);
    v_i_boxed_2616_ = lean_unbox_usize(v_i_2611_);
    lean_dec(v_i_2611_);
    v_res_2617_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_2606_, v_params_2607_, v_snap_2608_, v_as_2609_, v_sz_boxed_2615_, v_i_boxed_2616_, v_b_2612_, v___y_2613_);
    lean_dec_ref(v___y_2613_);
    lean_dec_ref(v_as_2609_);
    lean_dec_ref(v___x_2606_);
    return v_res_2617_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(
    mut v_params_2618_: *mut LeanObject,
    mut v_snap_2619_: *mut LeanObject,
    mut v___x_2620_: *mut LeanObject,
    mut v_as_2621_: *mut LeanObject,
    mut v_sz_2622_: usize,
    mut v_i_2623_: usize,
    mut v_b_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: usize = 0;
    let mut v___x_2630_: usize = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut v___x_2644_: u8 = 0;
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onAnyCmd_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_onCmd_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_out_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2656_: usize = 0;
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stx_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2664_: usize = 0;
    let mut v___x_2665_: usize = 0;
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2644_ = lean_usize_dec_lt(v_i_2623_, v_sz_2622_);
                if v___x_2644_ == 0 {
                    lean_dec_ref(v_snap_2619_);
                    lean_dec_ref(v_params_2618_);
                    v___x_2645_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2645_, 0, v_b_2624_);
                    return v___x_2645_;
                } else {
                    v_a_2646_ = lean_array_uget_borrowed(v_as_2621_, v_i_2623_);
                    v_snd_2647_ = lean_ctor_get(v_a_2646_, 1);
                    if lean_obj_tag(v_snd_2647_) == 1 {
                        v_i_2648_ = lean_ctor_get(v_snd_2647_, 0);
                        if lean_obj_tag(v_i_2648_) == 3 {
                            v_fst_2649_ = lean_ctor_get(v_a_2646_, 0);
                            v_i_2650_ = lean_ctor_get(v_i_2648_, 0);
                            v_onAnyCmd_2651_ = lean_ctor_get(v___x_2620_, 0);
                            v_onCmd_2652_ = lean_ctor_get(v___x_2620_, 1);
                            v_stx_2660_ = lean_ctor_get(v_i_2650_, 1);
                            lean_inc(v_stx_2660_);
                            v___x_2661_ = l_Lean_Syntax_getKind(v_stx_2660_);
                            v___x_2662_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_onCmd_2652_, v___x_2661_);
                            lean_dec(v___x_2661_);
                            if lean_obj_tag(v___x_2662_) == 1 {
                                v_val_2663_ = lean_ctor_get(v___x_2662_, 0);
                                lean_inc(v_val_2663_);
                                lean_dec_ref_known(v___x_2662_, 1);
                                v_sz_2664_ = lean_array_size(v_val_2663_);
                                v___x_2665_ = 0usize;
                                lean_inc_ref(v_snd_2647_);
                                lean_inc(v_fst_2649_);
                                lean_inc_ref(v_snap_2619_);
                                lean_inc_ref(v_params_2618_);
                                v___x_2666_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2618_, v_snap_2619_, v_fst_2649_, v_snd_2647_, v_val_2663_, v_sz_2664_, v___x_2665_, v_b_2624_, v___y_2625_);
                                lean_dec(v_val_2663_);
                                if lean_obj_tag(v___x_2666_) == 0 {
                                    v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
                                    lean_inc(v_a_2667_);
                                    lean_dec_ref_known(v___x_2666_, 1);
                                    v_out_2654_ = v_a_2667_;
                                    v___y_2655_ = v___y_2625_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec_ref(v_snap_2619_);
                                    lean_dec_ref(v_params_2618_);
                                    return v___x_2666_;
                                }
                            } else {
                                lean_dec(v___x_2662_);
                                v_out_2654_ = v_b_2624_;
                                v___y_2655_ = v___y_2625_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v___y_2633_ = v___y_2625_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_2633_ = v___y_2625_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2629_ = 1usize;
                v___x_2630_ = lean_usize_add(v_i_2623_, v___x_2629_);
                v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2(v___x_2620_, v_params_2618_, v_snap_2619_, v_as_2621_, v_sz_2622_, v___x_2630_, v_a_2628_, v___y_2625_);
                return v___x_2631_;
            }
            2 => {
                v___x_2634_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2_spec__2___closed__3);
                v___x_2635_ = l_panic___at___00Lean_CodeAction_cmdCodeActionProvider_spec__0(
                    v___x_2634_,
                    v___y_2633_,
                );
                if lean_obj_tag(v___x_2635_) == 0 {
                    lean_dec_ref_known(v___x_2635_, 1);
                    v_a_2628_ = v_b_2624_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_b_2624_);
                    lean_dec_ref(v_snap_2619_);
                    lean_dec_ref(v_params_2618_);
                    v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
                    v_isSharedCheck_2643_ = (!lean_is_exclusive(v___x_2635_)) as u8;
                    if v_isSharedCheck_2643_ == 0 {
                        v___x_2638_ = v___x_2635_;
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2636_);
                        lean_dec(v___x_2635_);
                        v___x_2638_ = lean_box(0);
                        v_isShared_2639_ = v_isSharedCheck_2643_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2639_ == 0 {
                    v___x_2641_ = v___x_2638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
                    v___x_2641_ = v_reuseFailAlloc_2642_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2641_;
            }
            5 => {
                v_sz_2656_ = lean_array_size(v_onAnyCmd_2651_);
                v___x_2657_ = 0usize;
                lean_inc_ref(v_snd_2647_);
                lean_inc(v_fst_2649_);
                lean_inc_ref(v_snap_2619_);
                lean_inc_ref(v_params_2618_);
                v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__1(v_params_2618_, v_snap_2619_, v_fst_2649_, v_snd_2647_, v_onAnyCmd_2651_, v_sz_2656_, v___x_2657_, v_out_2654_, v___y_2655_);
                if lean_obj_tag(v___x_2658_) == 0 {
                    v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
                    lean_inc(v_a_2659_);
                    lean_dec_ref_known(v___x_2658_, 1);
                    v_a_2628_ = v_a_2659_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_snap_2619_);
                    lean_dec_ref(v_params_2618_);
                    return v___x_2658_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2___boxed(
    mut v_params_2668_: *mut LeanObject,
    mut v_snap_2669_: *mut LeanObject,
    mut v___x_2670_: *mut LeanObject,
    mut v_as_2671_: *mut LeanObject,
    mut v_sz_2672_: *mut LeanObject,
    mut v_i_2673_: *mut LeanObject,
    mut v_b_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2677_: usize = 0;
    let mut v_i_boxed_2678_: usize = 0;
    let mut v_res_2679_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2677_ = lean_unbox_usize(v_sz_2672_);
    lean_dec(v_sz_2672_);
    v_i_boxed_2678_ = lean_unbox_usize(v_i_2673_);
    lean_dec(v_i_2673_);
    v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_2668_, v_snap_2669_, v___x_2670_, v_as_2671_, v_sz_boxed_2677_, v_i_boxed_2678_, v_b_2674_, v___y_2675_);
    lean_dec_ref(v___y_2675_);
    lean_dec_ref(v_as_2671_);
    lean_dec_ref(v___x_2670_);
    return v_res_2679_;
}
pub unsafe fn _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0() -> *mut LeanObject {
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    v___x_2680_ = l_Array_instInhabited(lean_box(0));
    return v___x_2680_;
}
pub unsafe fn _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1() -> *mut LeanObject {
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    v___x_2681_ = l_Lean_CodeAction_instInhabitedCommandCodeActions_default;
    v___x_2682_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__0),
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__0_once),
        _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__0,
    );
    v___x_2683_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2683_, 0, v___x_2682_);
    lean_ctor_set(v___x_2683_, 1, v___x_2681_);
    return v___x_2683_;
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider(
    mut v_params_2686_: *mut LeanObject,
    mut v_snap_2687_: *mut LeanObject,
    mut v_a_2688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEditableDocumentCore_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_meta_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_range_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_text_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_end_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2712_: usize = 0;
    let mut v___x_2713_: usize = 0;
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    v___x_2690_ =
        l_Lean_Server_RequestM_readDoc___at___00Lean_CodeAction_holeCodeActionProvider_spec__0(
            v_a_2688_,
        );
    v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
    lean_inc(v_a_2691_);
    lean_dec_ref(v___x_2690_);
    v_toEditableDocumentCore_2692_ = lean_ctor_get(v_a_2691_, 0);
    lean_inc_ref(v_toEditableDocumentCore_2692_);
    lean_dec(v_a_2691_);
    v_meta_2693_ = lean_ctor_get(v_toEditableDocumentCore_2692_, 0);
    lean_inc_ref(v_meta_2693_);
    lean_dec_ref(v_toEditableDocumentCore_2692_);
    v_range_2694_ = lean_ctor_get(v_params_2686_, 3);
    v_text_2695_ = lean_ctor_get(v_meta_2693_, 3);
    lean_inc_ref(v_text_2695_);
    lean_dec_ref(v_meta_2693_);
    v_start_2696_ = lean_ctor_get(v_range_2694_, 0);
    v_end_2697_ = lean_ctor_get(v_range_2694_, 1);
    v___x_2698_ = l_Lean_CodeAction_cmdCodeActionExt;
    v_toEnvExtension_2699_ = lean_ctor_get(v___x_2698_, 0);
    v_asyncMode_2700_ = lean_ctor_get(v_toEnvExtension_2699_, 2);
    v___x_2701_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__1),
        core::ptr::addr_of_mut!(l_Lean_CodeAction_cmdCodeActionProvider___closed__1_once),
        _init_l_Lean_CodeAction_cmdCodeActionProvider___closed__1,
    );
    v___x_2702_ = l_Lean_Server_Snapshots_Snapshot_env(v_snap_2687_);
    v___x_2703_ = lean_box(0);
    v___x_2704_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_2701_,
        v___x_2698_,
        v___x_2702_,
        v_asyncMode_2700_,
        v___x_2703_,
    );
    v_snd_2705_ = lean_ctor_get(v___x_2704_, 1);
    lean_inc(v_snd_2705_);
    lean_dec(v___x_2704_);
    lean_inc_ref(v_start_2696_);
    v___x_2706_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2695_, v_start_2696_);
    lean_inc_ref(v_end_2697_);
    v___x_2707_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_2695_, v_end_2697_);
    lean_dec_ref(v_text_2695_);
    v___f_2708_ = lean_alloc_closure(
        l_Lean_CodeAction_cmdCodeActionProvider___lam__0___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2708_, 0, v___x_2707_);
    lean_closure_set(v___f_2708_, 1, v___x_2706_);
    v___x_2709_ = l_Lean_CodeAction_cmdCodeActionProvider___closed__2;
    lean_inc_ref(v_snap_2687_);
    v___x_2710_ = l_Lean_Server_Snapshots_Snapshot_infoTree(v_snap_2687_);
    v___x_2711_ = l_Lean_Elab_InfoTree_foldInfoTree___redArg(v___x_2709_, v___f_2708_, v___x_2710_);
    v_sz_2712_ = lean_array_size(v___x_2711_);
    v___x_2713_ = 0usize;
    v___x_2714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_CodeAction_cmdCodeActionProvider_spec__2(v_params_2686_, v_snap_2687_, v_snd_2705_, v___x_2711_, v_sz_2712_, v___x_2713_, v___x_2709_, v_a_2688_);
    lean_dec(v___x_2711_);
    lean_dec(v_snd_2705_);
    return v___x_2714_;
}
pub unsafe fn l_Lean_CodeAction_cmdCodeActionProvider___boxed(
    mut v_params_2715_: *mut LeanObject,
    mut v_snap_2716_: *mut LeanObject,
    mut v_a_2717_: *mut LeanObject,
    mut v_a_2718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2719_: *mut LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Lean_CodeAction_cmdCodeActionProvider(v_params_2715_, v_snap_2716_, v_a_2717_);
    lean_dec_ref(v_a_2717_);
    return v_res_2719_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1()
-> *mut LeanObject {
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    v___x_2726_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___closed__1;
    v___x_2727_ = lean_alloc_closure(
        l_Lean_CodeAction_cmdCodeActionProvider___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2728_ = l_Lean_Server_addBuiltinCodeActionProvider(v___x_2726_, v___x_2727_);
    return v___x_2728_;
}
pub unsafe fn l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1___boxed(
    mut v_a_2729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2730_: *mut LeanObject = core::ptr::null_mut();
    v_res_2730_ = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
    return v_res_2730_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_CodeActions_Provider(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Iterators_Producers_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_holeCodeActionProvider___regBuiltin_Lean_CodeAction_holeCodeActionProvider__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Server_CodeActions_Provider_0__Lean_CodeAction_cmdCodeActionProvider___regBuiltin_Lean_CodeAction_cmdCodeActionProvider__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_CodeActions_Provider(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_CodeActions_Provider(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Iterators_Producers_Range(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinTerm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinNotation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Server_CodeActions_Attr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_CodeActions_Provider(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_CodeActions_Provider(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_CodeActions_Provider(builtin);
}
