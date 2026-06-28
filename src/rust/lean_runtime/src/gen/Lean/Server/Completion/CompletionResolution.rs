// Lean compiler output
// Module: Lean.Server.Completion.CompletionResolution
// Imports: Lean.Data.Lsp Lean.Server.Completion.CompletionInfoSelection Lean.Linter.Deprecated
use crate::r#gen::Init::Data::Format::Basic::{l_Std_Format_defWidth, l_Std_Format_pretty};
use crate::r#gen::Init::Data::ToString::Basic::l_addParenHeuristic;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Attributes::l_Lean_ParametricAttribute_getParam_x3f___redArg;
use crate::r#gen::Lean::Data::Lsp::{initialize_Lean_Data_Lsp, runtime_initialize_Lean_Data_Lsp};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::DocString::l_Lean_findDocString_x3f;
use crate::r#gen::Lean::Elab::InfoTree::Main::{
    l_Lean_Elab_CompletionInfo_lctx, l_Lean_Elab_ContextInfo_runMetaM___redArg,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Expr::l_Lean_instBEqBinderInfo_beq;
use crate::r#gen::Lean::Linter::Deprecated::{
    initialize_Lean_Linter_Deprecated, l_Lean_Linter_deprecatedAttr,
    l_Lean_Linter_instInhabitedDeprecationEntry_default, runtime_initialize_Lean_Linter_Deprecated,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_type, lean_local_ctx_find};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_ppExpr,
};
use crate::r#gen::Lean::Server::Completion::CompletionInfoSelection::{
    initialize_Lean_Server_Completion_CompletionInfoSelection,
    l_Lean_Server_Completion_findCompletionInfosAt,
    runtime_initialize_Lean_Server_Completion_CompletionInfoSelection,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate1;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_6, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Lsp_CompletionItem_resolve___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_CompletionItem_resolve___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_CompletionItem_resolve___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__0_value) as *mut LeanObject;
pub static l_Lean_Lsp_CompletionItem_resolve___closed__1_value: LeanStringObject<3> =
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
        m_data: [10, 10, 0],
    };
static mut l_Lean_Lsp_CompletionItem_resolve___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__1_value) as *mut LeanObject;
pub static l_Lean_Lsp_CompletionItem_resolve___closed__2_value: LeanStringObject<5> =
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
        m_data: [110, 111, 110, 101, 0],
    };
static mut l_Lean_Lsp_CompletionItem_resolve___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__2_value) as *mut LeanObject;
pub static l_Lean_Lsp_CompletionItem_resolve___closed__3_value: LeanStringObject<7> =
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
        m_data: [40, 115, 111, 109, 101, 32, 0],
    };
static mut l_Lean_Lsp_CompletionItem_resolve___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__3_value) as *mut LeanObject;
pub static l_Lean_Lsp_CompletionItem_resolve___closed__4_value: LeanStringObject<2> =
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
static mut l_Lean_Lsp_CompletionItem_resolve___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__4_value) as *mut LeanObject;
pub static l_Lean_Lsp_CompletionItem_resolve___closed__5_value: LeanStringObject<2> =
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
        m_data: [96, 0],
    };
static mut l_Lean_Lsp_CompletionItem_resolve___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__5_value) as *mut LeanObject;
pub static l_Lean_Lsp_CompletionItem_resolve___closed__6_value: LeanStringObject<29> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 29,
        m_capacity: 29,
        m_length: 28,
        m_data: [
            96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116,
            101, 100, 44, 32, 117, 115, 101, 32, 96, 0,
        ],
    };
static mut l_Lean_Lsp_CompletionItem_resolve___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__6_value) as *mut LeanObject;
pub static l_Lean_Lsp_CompletionItem_resolve___closed__7_value: LeanStringObject<11> =
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
        m_data: [96, 32, 105, 110, 115, 116, 101, 97, 100, 46, 0],
    };
static mut l_Lean_Lsp_CompletionItem_resolve___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__7_value) as *mut LeanObject;
pub static l_Lean_Lsp_CompletionItem_resolve___closed__8_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            96, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 100, 101, 112, 114, 101, 99, 97, 116,
            101, 100, 46, 0,
        ],
    };
static mut l_Lean_Lsp_CompletionItem_resolve___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__8_value) as *mut LeanObject;
pub static l_Lean_Lsp_CompletionItem_resolve___closed__9_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_CompletionItem_resolve___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_CompletionItem_resolve___closed__9_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(
    mut v_k_446_: *mut LeanObject,
    mut v_b_447_: *mut LeanObject,
    mut v___y_448_: *mut LeanObject,
    mut v___y_449_: *mut LeanObject,
    mut v___y_450_: *mut LeanObject,
    mut v___y_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_451_);
    lean_inc_ref(v___y_450_);
    lean_inc(v___y_449_);
    lean_inc_ref(v___y_448_);
    v___x_453_ = lean_apply_6(
        v_k_446_,
        v_b_447_,
        v___y_448_,
        v___y_449_,
        v___y_450_,
        v___y_451_,
        lean_box(0),
    );
    return v___x_453_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed(
    mut v_k_454_: *mut LeanObject,
    mut v_b_455_: *mut LeanObject,
    mut v___y_456_: *mut LeanObject,
    mut v___y_457_: *mut LeanObject,
    mut v___y_458_: *mut LeanObject,
    mut v___y_459_: *mut LeanObject,
    mut v___y_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_461_: *mut LeanObject = core::ptr::null_mut();
    v_res_461_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0(v_k_454_, v_b_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
    lean_dec(v___y_459_);
    lean_dec_ref(v___y_458_);
    lean_dec(v___y_457_);
    lean_dec_ref(v___y_456_);
    return v_res_461_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(
    mut v_name_462_: *mut LeanObject,
    mut v_bi_463_: u8,
    mut v_type_464_: *mut LeanObject,
    mut v_k_465_: *mut LeanObject,
    mut v_kind_466_: u8,
    mut v___y_467_: *mut LeanObject,
    mut v___y_468_: *mut LeanObject,
    mut v___y_469_: *mut LeanObject,
    mut v___y_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_477_: u8 = 0;
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_481_: u8 = 0;
    let mut v_a_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_485_: u8 = 0;
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_472_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                lean_closure_set(v___f_472_, 0, v_k_465_);
                v___x_473_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_462_,
                    v_bi_463_,
                    v_type_464_,
                    v___f_472_,
                    v_kind_466_,
                    v___y_467_,
                    v___y_468_,
                    v___y_469_,
                    v___y_470_,
                );
                if lean_obj_tag(v___x_473_) == 0 {
                    v_a_474_ = lean_ctor_get(v___x_473_, 0);
                    v_isSharedCheck_481_ = (!lean_is_exclusive(v___x_473_)) as u8;
                    if v_isSharedCheck_481_ == 0 {
                        v___x_476_ = v___x_473_;
                        v_isShared_477_ = v_isSharedCheck_481_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_474_);
                        lean_dec(v___x_473_);
                        v___x_476_ = lean_box(0);
                        v_isShared_477_ = v_isSharedCheck_481_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_482_ = lean_ctor_get(v___x_473_, 0);
                    v_isSharedCheck_489_ = (!lean_is_exclusive(v___x_473_)) as u8;
                    if v_isSharedCheck_489_ == 0 {
                        v___x_484_ = v___x_473_;
                        v_isShared_485_ = v_isSharedCheck_489_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_482_);
                        lean_dec(v___x_473_);
                        v___x_484_ = lean_box(0);
                        v_isShared_485_ = v_isSharedCheck_489_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_477_ == 0 {
                    v___x_479_ = v___x_476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
                    v___x_479_ = v_reuseFailAlloc_480_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_479_;
            }
            3 => {
                if v_isShared_485_ == 0 {
                    v___x_487_ = v___x_484_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
                    v___x_487_ = v_reuseFailAlloc_488_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg___boxed(
    mut v_name_490_: *mut LeanObject,
    mut v_bi_491_: *mut LeanObject,
    mut v_type_492_: *mut LeanObject,
    mut v_k_493_: *mut LeanObject,
    mut v_kind_494_: *mut LeanObject,
    mut v___y_495_: *mut LeanObject,
    mut v___y_496_: *mut LeanObject,
    mut v___y_497_: *mut LeanObject,
    mut v___y_498_: *mut LeanObject,
    mut v___y_499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_500_: u8 = 0;
    let mut v_kind_boxed_501_: u8 = 0;
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_500_ = (lean_unbox(v_bi_491_) as u8);
    v_kind_boxed_501_ = (lean_unbox(v_kind_494_) as u8);
    v_res_502_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_name_490_, v_bi_boxed_500_, v_type_492_, v_k_493_, v_kind_boxed_501_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
    lean_dec(v___y_498_);
    lean_dec_ref(v___y_497_);
    lean_dec(v___y_496_);
    lean_dec_ref(v___y_495_);
    return v_res_502_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(
    mut v_00_u03b1_503_: *mut LeanObject,
    mut v_name_504_: *mut LeanObject,
    mut v_bi_505_: u8,
    mut v_type_506_: *mut LeanObject,
    mut v_k_507_: *mut LeanObject,
    mut v_kind_508_: u8,
    mut v___y_509_: *mut LeanObject,
    mut v___y_510_: *mut LeanObject,
    mut v___y_511_: *mut LeanObject,
    mut v___y_512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    v___x_514_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_name_504_, v_bi_505_, v_type_506_, v_k_507_, v_kind_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_);
    return v___x_514_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___boxed(
    mut v_00_u03b1_515_: *mut LeanObject,
    mut v_name_516_: *mut LeanObject,
    mut v_bi_517_: *mut LeanObject,
    mut v_type_518_: *mut LeanObject,
    mut v_k_519_: *mut LeanObject,
    mut v_kind_520_: *mut LeanObject,
    mut v___y_521_: *mut LeanObject,
    mut v___y_522_: *mut LeanObject,
    mut v___y_523_: *mut LeanObject,
    mut v___y_524_: *mut LeanObject,
    mut v___y_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_526_: u8 = 0;
    let mut v_kind_boxed_527_: u8 = 0;
    let mut v_res_528_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_526_ = (lean_unbox(v_bi_517_) as u8);
    v_kind_boxed_527_ = (lean_unbox(v_kind_520_) as u8);
    v_res_528_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0(v_00_u03b1_515_, v_name_516_, v_bi_boxed_526_, v_type_518_, v_k_519_, v_kind_boxed_527_, v___y_521_, v___y_522_, v___y_523_, v___y_524_);
    lean_dec(v___y_524_);
    lean_dec_ref(v___y_523_);
    lean_dec(v___y_522_);
    lean_dec_ref(v___y_521_);
    return v_res_528_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed(
    mut v_body_529_: *mut LeanObject,
    mut v_k_530_: *mut LeanObject,
    mut v_arg_531_: *mut LeanObject,
    mut v___y_532_: *mut LeanObject,
    mut v___y_533_: *mut LeanObject,
    mut v___y_534_: *mut LeanObject,
    mut v___y_535_: *mut LeanObject,
    mut v___y_536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_537_: *mut LeanObject = core::ptr::null_mut();
    v_res_537_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(v_body_529_, v_k_530_, v_arg_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_);
    lean_dec(v___y_535_);
    lean_dec_ref(v___y_534_);
    lean_dec(v___y_533_);
    lean_dec_ref(v___y_532_);
    lean_dec_ref(v_arg_531_);
    lean_dec_ref(v_body_529_);
    return v_res_537_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(
    mut v_e_538_: *mut LeanObject,
    mut v_k_539_: *mut LeanObject,
    mut v_a_540_: *mut LeanObject,
    mut v_a_541_: *mut LeanObject,
    mut v_a_542_: *mut LeanObject,
    mut v_a_543_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_538_) == 7 {
        let mut v_binderName_545_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderType_546_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_547_: *mut LeanObject = core::ptr::null_mut();
        let mut v_binderInfo_548_: u8 = 0;
        let mut v___x_549_: u8 = 0;
        let mut v___x_550_: u8 = 0;
        v_binderName_545_ = lean_ctor_get(v_e_538_, 0);
        v_binderType_546_ = lean_ctor_get(v_e_538_, 1);
        v_body_547_ = lean_ctor_get(v_e_538_, 2);
        v_binderInfo_548_ = lean_ctor_get_uint8(
            v_e_538_,
            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
        );
        v___x_549_ = 1;
        v___x_550_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_548_, v___x_549_);
        if v___x_550_ == 0 {
            let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_a_543_);
            lean_inc_ref(v_a_542_);
            lean_inc(v_a_541_);
            lean_inc_ref(v_a_540_);
            v___x_551_ = lean_apply_6(
                v_k_539_,
                v_e_538_,
                v_a_540_,
                v_a_541_,
                v_a_542_,
                v_a_543_,
                lean_box(0),
            );
            return v___x_551_;
        } else {
            let mut v___f_552_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_553_: u8 = 0;
            let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
            lean_inc_ref(v_body_547_);
            lean_inc_ref(v_binderType_546_);
            lean_inc(v_binderName_545_);
            lean_dec_ref_known(v_e_538_, 3);
            v___f_552_ = lean_alloc_closure(l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
            lean_closure_set(v___f_552_, 0, v_body_547_);
            lean_closure_set(v___f_552_, 1, v_k_539_);
            v___x_553_ = 0;
            v___x_554_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix_spec__0___redArg(v_binderName_545_, v_binderInfo_548_, v_binderType_546_, v___f_552_, v___x_553_, v_a_540_, v_a_541_, v_a_542_, v_a_543_);
            return v___x_554_;
        }
    } else {
        let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_a_543_);
        lean_inc_ref(v_a_542_);
        lean_inc(v_a_541_);
        lean_inc_ref(v_a_540_);
        v___x_555_ = lean_apply_6(
            v_k_539_,
            v_e_538_,
            v_a_540_,
            v_a_541_,
            v_a_542_,
            v_a_543_,
            lean_box(0),
        );
        return v___x_555_;
    }
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___lam__0(
    mut v_body_556_: *mut LeanObject,
    mut v_k_557_: *mut LeanObject,
    mut v_arg_558_: *mut LeanObject,
    mut v___y_559_: *mut LeanObject,
    mut v___y_560_: *mut LeanObject,
    mut v___y_561_: *mut LeanObject,
    mut v___y_562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    v___x_564_ = lean_expr_instantiate1(v_body_556_, v_arg_558_);
    v___x_565_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v___x_564_, v_k_557_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
    return v___x_565_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg___boxed(
    mut v_e_566_: *mut LeanObject,
    mut v_k_567_: *mut LeanObject,
    mut v_a_568_: *mut LeanObject,
    mut v_a_569_: *mut LeanObject,
    mut v_a_570_: *mut LeanObject,
    mut v_a_571_: *mut LeanObject,
    mut v_a_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_573_: *mut LeanObject = core::ptr::null_mut();
    v_res_573_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_e_566_, v_k_567_, v_a_568_, v_a_569_, v_a_570_, v_a_571_);
    lean_dec(v_a_571_);
    lean_dec_ref(v_a_570_);
    lean_dec(v_a_569_);
    lean_dec_ref(v_a_568_);
    return v_res_573_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(
    mut v_00_u03b1_574_: *mut LeanObject,
    mut v_e_575_: *mut LeanObject,
    mut v_k_576_: *mut LeanObject,
    mut v_a_577_: *mut LeanObject,
    mut v_a_578_: *mut LeanObject,
    mut v_a_579_: *mut LeanObject,
    mut v_a_580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    v___x_582_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_e_575_, v_k_576_, v_a_577_, v_a_578_, v_a_579_, v_a_580_);
    return v___x_582_;
}
pub unsafe fn l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___boxed(
    mut v_00_u03b1_583_: *mut LeanObject,
    mut v_e_584_: *mut LeanObject,
    mut v_k_585_: *mut LeanObject,
    mut v_a_586_: *mut LeanObject,
    mut v_a_587_: *mut LeanObject,
    mut v_a_588_: *mut LeanObject,
    mut v_a_589_: *mut LeanObject,
    mut v_a_590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_591_: *mut LeanObject = core::ptr::null_mut();
    v_res_591_ =
        l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix(
            v_00_u03b1_583_,
            v_e_584_,
            v_k_585_,
            v_a_586_,
            v_a_587_,
            v_a_588_,
            v_a_589_,
        );
    lean_dec(v_a_589_);
    lean_dec_ref(v_a_588_);
    lean_dec(v_a_587_);
    lean_dec_ref(v_a_586_);
    return v_res_591_;
}
pub unsafe fn l_Lean_Lsp_CompletionItem_resolve___lam__0(
    mut v_docValue_592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_593_: u8 = 0;
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    v___x_593_ = 1;
    v___x_594_ = lean_alloc_ctor(0, 1, (1) as u32);
    lean_ctor_set(v___x_594_, 0, v_docValue_592_);
    lean_ctor_set_uint8(
        v___x_594_,
        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
        v___x_593_,
    );
    v___x_595_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_595_, 0, v___x_594_);
    return v___x_595_;
}
pub unsafe fn l_Lean_Lsp_CompletionItem_resolve___lam__1(
    mut v_documentation_x3f_596_: *mut LeanObject,
    mut v___f_597_: *mut LeanObject,
    mut v_docStringPrefix_598_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_docStringPrefix_598_) == 0 {
        lean_dec_ref(v___f_597_);
        lean_inc(v_documentation_x3f_596_);
        return v_documentation_x3f_596_;
    } else {
        let mut v_val_599_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
        v_val_599_ = lean_ctor_get(v_docStringPrefix_598_, 0);
        lean_inc(v_val_599_);
        lean_dec_ref_known(v_docStringPrefix_598_, 1);
        v___x_600_ = lean_apply_1(v___f_597_, v_val_599_);
        return v___x_600_;
    }
}
pub unsafe fn l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed(
    mut v_documentation_x3f_601_: *mut LeanObject,
    mut v___f_602_: *mut LeanObject,
    mut v_docStringPrefix_603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_604_: *mut LeanObject = core::ptr::null_mut();
    v_res_604_ = l_Lean_Lsp_CompletionItem_resolve___lam__1(
        v_documentation_x3f_601_,
        v___f_602_,
        v_docStringPrefix_603_,
    );
    lean_dec(v_documentation_x3f_601_);
    return v_res_604_;
}
pub unsafe fn l_Lean_Lsp_CompletionItem_resolve___lam__2(
    mut v_typeWithoutImplicits_605_: *mut LeanObject,
    mut v___y_606_: *mut LeanObject,
    mut v___y_607_: *mut LeanObject,
    mut v___y_608_: *mut LeanObject,
    mut v___y_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut v_a_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_626_: u8 = 0;
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_630_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_611_ = l_Lean_Meta_ppExpr(
                    v_typeWithoutImplicits_605_,
                    v___y_606_,
                    v___y_607_,
                    v___y_608_,
                    v___y_609_,
                );
                if lean_obj_tag(v___x_611_) == 0 {
                    v_a_612_ = lean_ctor_get(v___x_611_, 0);
                    v_isSharedCheck_622_ = (!lean_is_exclusive(v___x_611_)) as u8;
                    if v_isSharedCheck_622_ == 0 {
                        v___x_614_ = v___x_611_;
                        v_isShared_615_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_612_);
                        lean_dec(v___x_611_);
                        v___x_614_ = lean_box(0);
                        v_isShared_615_ = v_isSharedCheck_622_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_623_ = lean_ctor_get(v___x_611_, 0);
                    v_isSharedCheck_630_ = (!lean_is_exclusive(v___x_611_)) as u8;
                    if v_isSharedCheck_630_ == 0 {
                        v___x_625_ = v___x_611_;
                        v_isShared_626_ = v_isSharedCheck_630_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_623_);
                        lean_dec(v___x_611_);
                        v___x_625_ = lean_box(0);
                        v_isShared_626_ = v_isSharedCheck_630_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_616_ = l_Std_Format_defWidth;
                v___x_617_ = lean_unsigned_to_nat(0);
                v___x_618_ = l_Std_Format_pretty(v_a_612_, v___x_616_, v___x_617_, v___x_617_);
                if v_isShared_615_ == 0 {
                    lean_ctor_set(v___x_614_, 0, v___x_618_);
                    v___x_620_ = v___x_614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
                    v___x_620_ = v_reuseFailAlloc_621_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_620_;
            }
            3 => {
                if v_isShared_626_ == 0 {
                    v___x_628_ = v___x_625_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_629_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_629_, 0, v_a_623_);
                    v___x_628_ = v_reuseFailAlloc_629_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_628_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_CompletionItem_resolve___lam__2___boxed(
    mut v_typeWithoutImplicits_631_: *mut LeanObject,
    mut v___y_632_: *mut LeanObject,
    mut v___y_633_: *mut LeanObject,
    mut v___y_634_: *mut LeanObject,
    mut v___y_635_: *mut LeanObject,
    mut v___y_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_637_: *mut LeanObject = core::ptr::null_mut();
    v_res_637_ = l_Lean_Lsp_CompletionItem_resolve___lam__2(
        v_typeWithoutImplicits_631_,
        v___y_632_,
        v___y_633_,
        v___y_634_,
        v___y_635_,
    );
    lean_dec(v___y_635_);
    lean_dec_ref(v___y_634_);
    lean_dec(v___y_633_);
    lean_dec_ref(v___y_632_);
    return v_res_637_;
}
pub unsafe fn l_Lean_Lsp_CompletionItem_resolve(
    mut v_item_648_: *mut LeanObject,
    mut v_id_649_: *mut LeanObject,
    mut v_a_650_: *mut LeanObject,
    mut v_a_651_: *mut LeanObject,
    mut v_a_652_: *mut LeanObject,
    mut v_a_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_label_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_detail_x3f_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_documentation_x3f_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_textEdit_x3f_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sortText_x3f_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_docString_x3f_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_723_: u8 = 0;
    let mut v___y_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_732_: u8 = 0;
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_738_: u8 = 0;
    let mut v_ref_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_749_: u8 = 0;
    let mut v_isSharedCheck_750_: u8 = 0;
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_760_: u8 = 0;
    let mut v___y_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_item_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_label_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_detail_x3f_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_documentation_x3f_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_x3f_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_textEdit_x3f_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sortText_x3f_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_data_x3f_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tags_x3f_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: u8 = 0;
    let mut v_declName_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_786_: u8 = 0;
    let mut v_text_x3f_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newName_x3f_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_795_: u8 = 0;
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_808_: u8 = 0;
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_817_: u8 = 0;
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_826_: u8 = 0;
    let mut v_unused_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_840_: u8 = 0;
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_844_: u8 = 0;
    let mut v_declName_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: u8 = 0;
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_666_ = lean_st_ref_get(v_a_653_);
                v_env_667_ = lean_ctor_get(v___x_666_, 0);
                lean_inc_ref(v_env_667_);
                lean_dec(v___x_666_);
                v_label_668_ = lean_ctor_get(v_item_648_, 0);
                lean_inc_ref(v_label_668_);
                v_detail_x3f_669_ = lean_ctor_get(v_item_648_, 1);
                lean_inc(v_detail_x3f_669_);
                v_documentation_x3f_670_ = lean_ctor_get(v_item_648_, 2);
                lean_inc(v_documentation_x3f_670_);
                v_kind_x3f_671_ = lean_ctor_get(v_item_648_, 3);
                lean_inc(v_kind_x3f_671_);
                v_textEdit_x3f_672_ = lean_ctor_get(v_item_648_, 4);
                lean_inc(v_textEdit_x3f_672_);
                v_sortText_x3f_673_ = lean_ctor_get(v_item_648_, 5);
                lean_inc(v_sortText_x3f_673_);
                v_data_x3f_674_ = lean_ctor_get(v_item_648_, 6);
                lean_inc(v_data_x3f_674_);
                v_tags_x3f_675_ = lean_ctor_get(v_item_648_, 7);
                lean_inc(v_tags_x3f_675_);
                v___f_676_ = l_Lean_Lsp_CompletionItem_resolve___closed__0;
                if lean_obj_tag(v_detail_x3f_669_) == 0 {
                    lean_dec_ref(v_item_648_);
                    v___f_831_ = l_Lean_Lsp_CompletionItem_resolve___closed__9;
                    if lean_obj_tag(v_id_649_) == 0 {
                        v_declName_845_ = lean_ctor_get(v_id_649_, 0);
                        v___x_846_ = 0;
                        lean_inc(v_declName_845_);
                        lean_inc_ref(v_env_667_);
                        v___x_847_ =
                            l_Lean_Environment_find_x3f(v_env_667_, v_declName_845_, v___x_846_);
                        if lean_obj_tag(v___x_847_) == 0 {
                            v_a_829_ = v_detail_x3f_669_;
                            state = 18;
                            continue;
                        } else {
                            v_val_848_ = lean_ctor_get(v___x_847_, 0);
                            lean_inc(v_val_848_);
                            lean_dec_ref_known(v___x_847_, 1);
                            v___x_849_ = l_Lean_ConstantInfo_type(v_val_848_);
                            lean_dec(v_val_848_);
                            v_val_833_ = v___x_849_;
                            state = 19;
                            continue;
                        }
                    } else {
                        v_id_850_ = lean_ctor_get(v_id_649_, 0);
                        v_lctx_851_ = lean_ctor_get(v_a_650_, 2);
                        lean_inc(v_id_850_);
                        lean_inc_ref(v_lctx_851_);
                        v___x_852_ = lean_local_ctx_find(v_lctx_851_, v_id_850_);
                        if lean_obj_tag(v___x_852_) == 0 {
                            v_a_829_ = v_detail_x3f_669_;
                            state = 18;
                            continue;
                        } else {
                            v_val_853_ = lean_ctor_get(v___x_852_, 0);
                            lean_inc(v_val_853_);
                            lean_dec_ref_known(v___x_852_, 1);
                            v___x_854_ = l_Lean_LocalDecl_type(v_val_853_);
                            lean_dec(v_val_853_);
                            v_val_833_ = v___x_854_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    v_item_767_ = v_item_648_;
                    v_label_768_ = v_label_668_;
                    v_detail_x3f_769_ = v_detail_x3f_669_;
                    v_documentation_x3f_770_ = v_documentation_x3f_670_;
                    v_kind_x3f_771_ = v_kind_x3f_671_;
                    v_textEdit_x3f_772_ = v_textEdit_x3f_672_;
                    v_sortText_x3f_773_ = v_sortText_x3f_673_;
                    v_data_x3f_774_ = v_data_x3f_674_;
                    v_tags_x3f_775_ = v_tags_x3f_675_;
                    v___y_776_ = v_a_652_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_664_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_664_, 0, v___y_661_);
                lean_ctor_set(v___x_664_, 1, v___y_662_);
                lean_ctor_set(v___x_664_, 2, v___y_663_);
                lean_ctor_set(v___x_664_, 3, v___y_659_);
                lean_ctor_set(v___x_664_, 4, v___y_657_);
                lean_ctor_set(v___x_664_, 5, v___y_658_);
                lean_ctor_set(v___x_664_, 6, v___y_656_);
                lean_ctor_set(v___x_664_, 7, v___y_660_);
                v___x_665_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_665_, 0, v___x_664_);
                return v___x_665_;
            }
            2 => {
                v___x_687_ = l_Lean_Lsp_CompletionItem_resolve___closed__1;
                v___x_688_ = lean_string_append(v___y_686_, v___x_687_);
                v___x_689_ = lean_string_append(v___x_688_, v___y_684_);
                lean_dec_ref(v___y_684_);
                v___x_690_ = l_Lean_Lsp_CompletionItem_resolve___lam__0(v___x_689_);
                v___y_656_ = v___y_679_;
                v___y_657_ = v___y_678_;
                v___y_658_ = v___y_680_;
                v___y_659_ = v___y_681_;
                v___y_660_ = v___y_682_;
                v___y_661_ = v___y_683_;
                v___y_662_ = v___y_685_;
                v___y_663_ = v___x_690_;
                state = 1;
                continue;
            }
            3 => {
                if lean_obj_tag(v___y_696_) == 0 {
                    if lean_obj_tag(v_docString_x3f_702_) == 0 {
                        lean_dec_ref(v___y_695_);
                        v___y_656_ = v___y_693_;
                        v___y_657_ = v___y_692_;
                        v___y_658_ = v___y_694_;
                        v___y_659_ = v___y_697_;
                        v___y_660_ = v___y_698_;
                        v___y_661_ = v___y_699_;
                        v___y_662_ = v___y_700_;
                        v___y_663_ = v___y_701_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___y_701_);
                        v___x_703_ = lean_apply_1(v___y_695_, v_docString_x3f_702_);
                        v___y_656_ = v___y_693_;
                        v___y_657_ = v___y_692_;
                        v___y_658_ = v___y_694_;
                        v___y_659_ = v___y_697_;
                        v___y_660_ = v___y_698_;
                        v___y_661_ = v___y_699_;
                        v___y_662_ = v___y_700_;
                        v___y_663_ = v___x_703_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_701_);
                    if lean_obj_tag(v_docString_x3f_702_) == 0 {
                        v_val_704_ = lean_ctor_get(v___y_696_, 0);
                        lean_inc(v_val_704_);
                        lean_dec_ref_known(v___y_696_, 1);
                        v___x_705_ = lean_apply_1(v___y_695_, v_val_704_);
                        v___y_656_ = v___y_693_;
                        v___y_657_ = v___y_692_;
                        v___y_658_ = v___y_694_;
                        v___y_659_ = v___y_697_;
                        v___y_660_ = v___y_698_;
                        v___y_661_ = v___y_699_;
                        v___y_662_ = v___y_700_;
                        v___y_663_ = v___x_705_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v___y_695_);
                        v_val_706_ = lean_ctor_get(v___y_696_, 0);
                        lean_inc(v_val_706_);
                        lean_dec_ref_known(v___y_696_, 1);
                        if lean_obj_tag(v_val_706_) == 0 {
                            v_val_707_ = lean_ctor_get(v_docString_x3f_702_, 0);
                            lean_inc(v_val_707_);
                            lean_dec_ref_known(v_docString_x3f_702_, 1);
                            v___x_708_ = l_Lean_Lsp_CompletionItem_resolve___closed__2;
                            v___y_678_ = v___y_692_;
                            v___y_679_ = v___y_693_;
                            v___y_680_ = v___y_694_;
                            v___y_681_ = v___y_697_;
                            v___y_682_ = v___y_698_;
                            v___y_683_ = v___y_699_;
                            v___y_684_ = v_val_707_;
                            v___y_685_ = v___y_700_;
                            v___y_686_ = v___x_708_;
                            state = 2;
                            continue;
                        } else {
                            v_val_709_ = lean_ctor_get(v_docString_x3f_702_, 0);
                            lean_inc(v_val_709_);
                            lean_dec_ref_known(v_docString_x3f_702_, 1);
                            v_val_710_ = lean_ctor_get(v_val_706_, 0);
                            lean_inc(v_val_710_);
                            lean_dec_ref_known(v_val_706_, 1);
                            v___x_711_ = l_Lean_Lsp_CompletionItem_resolve___closed__3;
                            v___x_712_ = l_addParenHeuristic(v_val_710_);
                            v___x_713_ = lean_string_append(v___x_711_, v___x_712_);
                            lean_dec_ref(v___x_712_);
                            v___x_714_ = l_Lean_Lsp_CompletionItem_resolve___closed__4;
                            v___x_715_ = lean_string_append(v___x_713_, v___x_714_);
                            v___y_678_ = v___y_692_;
                            v___y_679_ = v___y_693_;
                            v___y_680_ = v___y_694_;
                            v___y_681_ = v___y_697_;
                            v___y_682_ = v___y_698_;
                            v___y_683_ = v___y_699_;
                            v___y_684_ = v_val_709_;
                            v___y_685_ = v___y_700_;
                            v___y_686_ = v___x_715_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if lean_obj_tag(v_id_649_) == 0 {
                    v_declName_729_ = lean_ctor_get(v_id_649_, 0);
                    v_isSharedCheck_750_ = (!lean_is_exclusive(v_id_649_)) as u8;
                    if v_isSharedCheck_750_ == 0 {
                        v___x_731_ = v_id_649_;
                        v_isShared_732_ = v_isSharedCheck_750_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_declName_729_);
                        lean_dec(v_id_649_);
                        v___x_731_ = lean_box(0);
                        v_isShared_732_ = v_isSharedCheck_750_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_667_);
                    lean_dec_ref(v_id_649_);
                    v___x_751_ = lean_box(0);
                    v___y_692_ = v___y_718_;
                    v___y_693_ = v___y_717_;
                    v___y_694_ = v___y_719_;
                    v___y_695_ = v___y_721_;
                    v___y_696_ = v___y_728_;
                    v___y_697_ = v___y_720_;
                    v___y_698_ = v___y_722_;
                    v___y_699_ = v___y_724_;
                    v___y_700_ = v___y_726_;
                    v___y_701_ = v___y_727_;
                    v_docString_x3f_702_ = v___x_751_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                v___x_733_ = l_Lean_findDocString_x3f(v_env_667_, v_declName_729_, v___y_723_);
                if lean_obj_tag(v___x_733_) == 0 {
                    lean_del_object(v___x_731_);
                    v_a_734_ = lean_ctor_get(v___x_733_, 0);
                    lean_inc(v_a_734_);
                    lean_dec_ref_known(v___x_733_, 1);
                    v___y_692_ = v___y_718_;
                    v___y_693_ = v___y_717_;
                    v___y_694_ = v___y_719_;
                    v___y_695_ = v___y_721_;
                    v___y_696_ = v___y_728_;
                    v___y_697_ = v___y_720_;
                    v___y_698_ = v___y_722_;
                    v___y_699_ = v___y_724_;
                    v___y_700_ = v___y_726_;
                    v___y_701_ = v___y_727_;
                    v_docString_x3f_702_ = v_a_734_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___y_728_);
                    lean_dec(v___y_727_);
                    lean_dec(v___y_726_);
                    lean_dec_ref(v___y_724_);
                    lean_dec(v___y_722_);
                    lean_dec_ref(v___y_721_);
                    lean_dec(v___y_720_);
                    lean_dec(v___y_719_);
                    lean_dec(v___y_718_);
                    lean_dec(v___y_717_);
                    v_a_735_ = lean_ctor_get(v___x_733_, 0);
                    v_isSharedCheck_749_ = (!lean_is_exclusive(v___x_733_)) as u8;
                    if v_isSharedCheck_749_ == 0 {
                        v___x_737_ = v___x_733_;
                        v_isShared_738_ = v_isSharedCheck_749_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_735_);
                        lean_dec(v___x_733_);
                        v___x_737_ = lean_box(0);
                        v_isShared_738_ = v_isSharedCheck_749_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v_ref_739_ = lean_ctor_get(v___y_725_, 5);
                v___x_740_ = lean_io_error_to_string(v_a_735_);
                if v_isShared_732_ == 0 {
                    lean_ctor_set_tag(v___x_731_, 3);
                    lean_ctor_set(v___x_731_, 0, v___x_740_);
                    v___x_742_ = v___x_731_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_748_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_740_);
                    v___x_742_ = v_reuseFailAlloc_748_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_743_ = l_Lean_MessageData_ofFormat(v___x_742_);
                lean_inc(v_ref_739_);
                v___x_744_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_744_, 0, v_ref_739_);
                lean_ctor_set(v___x_744_, 1, v___x_743_);
                if v_isShared_738_ == 0 {
                    lean_ctor_set(v___x_737_, 0, v___x_744_);
                    v___x_746_ = v___x_737_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_744_);
                    v___x_746_ = v_reuseFailAlloc_747_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_746_;
            }
            9 => {
                v___x_765_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_765_, 0, v___y_764_);
                v___y_717_ = v___y_754_;
                v___y_718_ = v___y_753_;
                v___y_719_ = v___y_755_;
                v___y_720_ = v___y_757_;
                v___y_721_ = v___y_756_;
                v___y_722_ = v___y_758_;
                v___y_723_ = v___y_760_;
                v___y_724_ = v___y_759_;
                v___y_725_ = v___y_761_;
                v___y_726_ = v___y_762_;
                v___y_727_ = v___y_763_;
                v___y_728_ = v___x_765_;
                state = 4;
                continue;
            }
            10 => {
                if lean_obj_tag(v_documentation_x3f_770_) == 0 {
                    lean_dec_ref(v_item_767_);
                    v___f_777_ = lean_alloc_closure(
                        l_Lean_Lsp_CompletionItem_resolve___lam__1___boxed
                            as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_777_, 0, v_documentation_x3f_770_);
                    lean_closure_set(v___f_777_, 1, v___f_676_);
                    v___x_778_ = 1;
                    if lean_obj_tag(v_id_649_) == 0 {
                        v_declName_779_ = lean_ctor_get(v_id_649_, 0);
                        v___x_780_ = l_Lean_Linter_instInhabitedDeprecationEntry_default;
                        v___x_781_ = l_Lean_Linter_deprecatedAttr;
                        lean_inc(v_declName_779_);
                        lean_inc_ref(v_env_667_);
                        v___x_782_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(
                            v___x_780_,
                            v___x_781_,
                            v_env_667_,
                            v_declName_779_,
                        );
                        if lean_obj_tag(v___x_782_) == 1 {
                            v_val_783_ = lean_ctor_get(v___x_782_, 0);
                            v_isSharedCheck_817_ = (!lean_is_exclusive(v___x_782_)) as u8;
                            if v_isSharedCheck_817_ == 0 {
                                v___x_785_ = v___x_782_;
                                v_isShared_786_ = v_isSharedCheck_817_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_val_783_);
                                lean_dec(v___x_782_);
                                v___x_785_ = lean_box(0);
                                v_isShared_786_ = v_isSharedCheck_817_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_782_);
                            v___x_818_ = lean_box(0);
                            v___y_717_ = v_data_x3f_774_;
                            v___y_718_ = v_textEdit_x3f_772_;
                            v___y_719_ = v_sortText_x3f_773_;
                            v___y_720_ = v_kind_x3f_771_;
                            v___y_721_ = v___f_777_;
                            v___y_722_ = v_tags_x3f_775_;
                            v___y_723_ = v___x_778_;
                            v___y_724_ = v_label_768_;
                            v___y_725_ = v___y_776_;
                            v___y_726_ = v_detail_x3f_769_;
                            v___y_727_ = v_documentation_x3f_770_;
                            v___y_728_ = v___x_818_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_819_ = lean_box(0);
                        v___y_717_ = v_data_x3f_774_;
                        v___y_718_ = v_textEdit_x3f_772_;
                        v___y_719_ = v_sortText_x3f_773_;
                        v___y_720_ = v_kind_x3f_771_;
                        v___y_721_ = v___f_777_;
                        v___y_722_ = v_tags_x3f_775_;
                        v___y_723_ = v___x_778_;
                        v___y_724_ = v_label_768_;
                        v___y_725_ = v___y_776_;
                        v___y_726_ = v_detail_x3f_769_;
                        v___y_727_ = v_documentation_x3f_770_;
                        v___y_728_ = v___x_819_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_tags_x3f_775_);
                    lean_dec(v_data_x3f_774_);
                    lean_dec(v_sortText_x3f_773_);
                    lean_dec(v_textEdit_x3f_772_);
                    lean_dec(v_kind_x3f_771_);
                    lean_dec(v_detail_x3f_769_);
                    lean_dec_ref(v_label_768_);
                    lean_dec_ref(v_env_667_);
                    lean_dec_ref(v_id_649_);
                    v_isSharedCheck_826_ = (!lean_is_exclusive(v_documentation_x3f_770_)) as u8;
                    if v_isSharedCheck_826_ == 0 {
                        v_unused_827_ = lean_ctor_get(v_documentation_x3f_770_, 0);
                        lean_dec(v_unused_827_);
                        v___x_821_ = v_documentation_x3f_770_;
                        v_isShared_822_ = v_isSharedCheck_826_;
                        state = 16;
                        continue;
                    } else {
                        lean_dec(v_documentation_x3f_770_);
                        v___x_821_ = lean_box(0);
                        v_isShared_822_ = v_isSharedCheck_826_;
                        state = 16;
                        continue;
                    }
                }
            }
            11 => {
                v_text_x3f_787_ = lean_ctor_get(v_val_783_, 1);
                if lean_obj_tag(v_text_x3f_787_) == 1 {
                    lean_inc_ref(v_text_x3f_787_);
                    lean_dec(v_val_783_);
                    if v_isShared_786_ == 0 {
                        lean_ctor_set(v___x_785_, 0, v_text_x3f_787_);
                        v___x_789_ = v___x_785_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_790_, 0, v_text_x3f_787_);
                        v___x_789_ = v_reuseFailAlloc_790_;
                        state = 12;
                        continue;
                    }
                } else {
                    v_newName_x3f_791_ = lean_ctor_get(v_val_783_, 0);
                    lean_inc(v_newName_x3f_791_);
                    lean_dec(v_val_783_);
                    if lean_obj_tag(v_newName_x3f_791_) == 1 {
                        lean_del_object(v___x_785_);
                        v_val_792_ = lean_ctor_get(v_newName_x3f_791_, 0);
                        v_isSharedCheck_808_ = (!lean_is_exclusive(v_newName_x3f_791_)) as u8;
                        if v_isSharedCheck_808_ == 0 {
                            v___x_794_ = v_newName_x3f_791_;
                            v_isShared_795_ = v_isSharedCheck_808_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_val_792_);
                            lean_dec(v_newName_x3f_791_);
                            v___x_794_ = lean_box(0);
                            v_isShared_795_ = v_isSharedCheck_808_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v_newName_x3f_791_);
                        v___x_809_ = l_Lean_Lsp_CompletionItem_resolve___closed__5;
                        lean_inc(v_declName_779_);
                        v___x_810_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v_declName_779_,
                                v___x_778_,
                            );
                        v___x_811_ = lean_string_append(v___x_809_, v___x_810_);
                        lean_dec_ref(v___x_810_);
                        v___x_812_ = l_Lean_Lsp_CompletionItem_resolve___closed__8;
                        v___x_813_ = lean_string_append(v___x_811_, v___x_812_);
                        if v_isShared_786_ == 0 {
                            lean_ctor_set(v___x_785_, 0, v___x_813_);
                            v___x_815_ = v___x_785_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
                            v___x_815_ = v_reuseFailAlloc_816_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___y_717_ = v_data_x3f_774_;
                v___y_718_ = v_textEdit_x3f_772_;
                v___y_719_ = v_sortText_x3f_773_;
                v___y_720_ = v_kind_x3f_771_;
                v___y_721_ = v___f_777_;
                v___y_722_ = v_tags_x3f_775_;
                v___y_723_ = v___x_778_;
                v___y_724_ = v_label_768_;
                v___y_725_ = v___y_776_;
                v___y_726_ = v_detail_x3f_769_;
                v___y_727_ = v_documentation_x3f_770_;
                v___y_728_ = v___x_789_;
                state = 4;
                continue;
            }
            13 => {
                v___x_796_ = l_Lean_Lsp_CompletionItem_resolve___closed__5;
                lean_inc(v_declName_779_);
                v___x_797_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_declName_779_,
                    v___x_778_,
                );
                v___x_798_ = lean_string_append(v___x_796_, v___x_797_);
                lean_dec_ref(v___x_797_);
                v___x_799_ = l_Lean_Lsp_CompletionItem_resolve___closed__6;
                v___x_800_ = lean_string_append(v___x_798_, v___x_799_);
                v___x_801_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_val_792_, v___x_778_,
                );
                v___x_802_ = lean_string_append(v___x_800_, v___x_801_);
                lean_dec_ref(v___x_801_);
                v___x_803_ = l_Lean_Lsp_CompletionItem_resolve___closed__7;
                v___x_804_ = lean_string_append(v___x_802_, v___x_803_);
                if v_isShared_795_ == 0 {
                    lean_ctor_set(v___x_794_, 0, v___x_804_);
                    v___x_806_ = v___x_794_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_807_, 0, v___x_804_);
                    v___x_806_ = v_reuseFailAlloc_807_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___y_753_ = v_textEdit_x3f_772_;
                v___y_754_ = v_data_x3f_774_;
                v___y_755_ = v_sortText_x3f_773_;
                v___y_756_ = v___f_777_;
                v___y_757_ = v_kind_x3f_771_;
                v___y_758_ = v_tags_x3f_775_;
                v___y_759_ = v_label_768_;
                v___y_760_ = v___x_778_;
                v___y_761_ = v___y_776_;
                v___y_762_ = v_detail_x3f_769_;
                v___y_763_ = v_documentation_x3f_770_;
                v___y_764_ = v___x_806_;
                state = 9;
                continue;
            }
            15 => {
                v___y_753_ = v_textEdit_x3f_772_;
                v___y_754_ = v_data_x3f_774_;
                v___y_755_ = v_sortText_x3f_773_;
                v___y_756_ = v___f_777_;
                v___y_757_ = v_kind_x3f_771_;
                v___y_758_ = v_tags_x3f_775_;
                v___y_759_ = v_label_768_;
                v___y_760_ = v___x_778_;
                v___y_761_ = v___y_776_;
                v___y_762_ = v_detail_x3f_769_;
                v___y_763_ = v_documentation_x3f_770_;
                v___y_764_ = v___x_815_;
                state = 9;
                continue;
            }
            16 => {
                if v_isShared_822_ == 0 {
                    lean_ctor_set_tag(v___x_821_, 0);
                    lean_ctor_set(v___x_821_, 0, v_item_767_);
                    v___x_824_ = v___x_821_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_825_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_825_, 0, v_item_767_);
                    v___x_824_ = v_reuseFailAlloc_825_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_824_;
            }
            18 => {
                lean_inc(v_tags_x3f_675_);
                lean_inc(v_data_x3f_674_);
                lean_inc(v_sortText_x3f_673_);
                lean_inc(v_textEdit_x3f_672_);
                lean_inc(v_kind_x3f_671_);
                lean_inc(v_documentation_x3f_670_);
                lean_inc(v_a_829_);
                lean_inc_ref(v_label_668_);
                v___x_830_ = lean_alloc_ctor(0, 8, (0) as u32);
                lean_ctor_set(v___x_830_, 0, v_label_668_);
                lean_ctor_set(v___x_830_, 1, v_a_829_);
                lean_ctor_set(v___x_830_, 2, v_documentation_x3f_670_);
                lean_ctor_set(v___x_830_, 3, v_kind_x3f_671_);
                lean_ctor_set(v___x_830_, 4, v_textEdit_x3f_672_);
                lean_ctor_set(v___x_830_, 5, v_sortText_x3f_673_);
                lean_ctor_set(v___x_830_, 6, v_data_x3f_674_);
                lean_ctor_set(v___x_830_, 7, v_tags_x3f_675_);
                v_item_767_ = v___x_830_;
                v_label_768_ = v_label_668_;
                v_detail_x3f_769_ = v_a_829_;
                v_documentation_x3f_770_ = v_documentation_x3f_670_;
                v_kind_x3f_771_ = v_kind_x3f_671_;
                v_textEdit_x3f_772_ = v_textEdit_x3f_672_;
                v_sortText_x3f_773_ = v_sortText_x3f_673_;
                v_data_x3f_774_ = v_data_x3f_674_;
                v_tags_x3f_775_ = v_tags_x3f_675_;
                v___y_776_ = v_a_652_;
                state = 10;
                continue;
            }
            19 => {
                v___x_834_ = l___private_Lean_Server_Completion_CompletionResolution_0__Lean_Lsp_consumeImplicitPrefix___redArg(v_val_833_, v___f_831_, v_a_650_, v_a_651_, v_a_652_, v_a_653_);
                if lean_obj_tag(v___x_834_) == 0 {
                    v_a_835_ = lean_ctor_get(v___x_834_, 0);
                    lean_inc(v_a_835_);
                    lean_dec_ref_known(v___x_834_, 1);
                    v___x_836_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_836_, 0, v_a_835_);
                    v_a_829_ = v___x_836_;
                    state = 18;
                    continue;
                } else {
                    lean_dec(v_tags_x3f_675_);
                    lean_dec(v_data_x3f_674_);
                    lean_dec(v_sortText_x3f_673_);
                    lean_dec(v_textEdit_x3f_672_);
                    lean_dec(v_kind_x3f_671_);
                    lean_dec(v_documentation_x3f_670_);
                    lean_dec_ref(v_label_668_);
                    lean_dec_ref(v_env_667_);
                    lean_dec_ref(v_id_649_);
                    v_a_837_ = lean_ctor_get(v___x_834_, 0);
                    v_isSharedCheck_844_ = (!lean_is_exclusive(v___x_834_)) as u8;
                    if v_isSharedCheck_844_ == 0 {
                        v___x_839_ = v___x_834_;
                        v_isShared_840_ = v_isSharedCheck_844_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_837_);
                        lean_dec(v___x_834_);
                        v___x_839_ = lean_box(0);
                        v_isShared_840_ = v_isSharedCheck_844_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_840_ == 0 {
                    v___x_842_ = v___x_839_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
                    v___x_842_ = v_reuseFailAlloc_843_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_CompletionItem_resolve___boxed(
    mut v_item_855_: *mut LeanObject,
    mut v_id_856_: *mut LeanObject,
    mut v_a_857_: *mut LeanObject,
    mut v_a_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
    mut v_a_860_: *mut LeanObject,
    mut v_a_861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_862_: *mut LeanObject = core::ptr::null_mut();
    v_res_862_ = l_Lean_Lsp_CompletionItem_resolve(
        v_item_855_,
        v_id_856_,
        v_a_857_,
        v_a_858_,
        v_a_859_,
        v_a_860_,
    );
    lean_dec(v_a_860_);
    lean_dec_ref(v_a_859_);
    lean_dec(v_a_858_);
    lean_dec_ref(v_a_857_);
    return v_res_862_;
}
pub unsafe fn l_Lean_Server_Completion_resolveCompletionItem_x3f(
    mut v_fileMap_863_: *mut LeanObject,
    mut v_hoverPos_864_: *mut LeanObject,
    mut v_cmdStx_865_: *mut LeanObject,
    mut v_infoTree_866_: *mut LeanObject,
    mut v_item_867_: *mut LeanObject,
    mut v_id_868_: *mut LeanObject,
    mut v_completionInfoPos_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: u8 = 0;
    v___x_871_ = l_Lean_Server_Completion_findCompletionInfosAt(
        v_fileMap_863_,
        v_hoverPos_864_,
        v_cmdStx_865_,
        v_infoTree_866_,
    );
    v_fst_872_ = lean_ctor_get(v___x_871_, 0);
    lean_inc(v_fst_872_);
    lean_dec_ref(v___x_871_);
    v___x_873_ = lean_array_get_size(v_fst_872_);
    v___x_874_ = lean_nat_dec_lt(v_completionInfoPos_869_, v___x_873_);
    if v___x_874_ == 0 {
        let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_872_);
        lean_dec_ref(v_id_868_);
        v___x_875_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_875_, 0, v_item_867_);
        return v___x_875_;
    } else {
        let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
        let mut v_ctx_877_: *mut LeanObject = core::ptr::null_mut();
        let mut v_info_878_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
        v___x_876_ = lean_array_fget(v_fst_872_, v_completionInfoPos_869_);
        lean_dec(v_fst_872_);
        v_ctx_877_ = lean_ctor_get(v___x_876_, 1);
        lean_inc_ref(v_ctx_877_);
        v_info_878_ = lean_ctor_get(v___x_876_, 2);
        lean_inc_ref(v_info_878_);
        lean_dec(v___x_876_);
        v___x_879_ = l_Lean_Elab_CompletionInfo_lctx(v_info_878_);
        lean_dec_ref(v_info_878_);
        v___x_880_ = lean_alloc_closure(
            l_Lean_Lsp_CompletionItem_resolve___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_880_, 0, v_item_867_);
        lean_closure_set(v___x_880_, 1, v_id_868_);
        v___x_881_ = l_Lean_Elab_ContextInfo_runMetaM___redArg(v_ctx_877_, v___x_879_, v___x_880_);
        return v___x_881_;
    }
}
pub unsafe fn l_Lean_Server_Completion_resolveCompletionItem_x3f___boxed(
    mut v_fileMap_882_: *mut LeanObject,
    mut v_hoverPos_883_: *mut LeanObject,
    mut v_cmdStx_884_: *mut LeanObject,
    mut v_infoTree_885_: *mut LeanObject,
    mut v_item_886_: *mut LeanObject,
    mut v_id_887_: *mut LeanObject,
    mut v_completionInfoPos_888_: *mut LeanObject,
    mut v_a_889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_890_: *mut LeanObject = core::ptr::null_mut();
    v_res_890_ = l_Lean_Server_Completion_resolveCompletionItem_x3f(
        v_fileMap_882_,
        v_hoverPos_883_,
        v_cmdStx_884_,
        v_infoTree_885_,
        v_item_886_,
        v_id_887_,
        v_completionInfoPos_888_,
    );
    lean_dec(v_completionInfoPos_888_);
    return v_res_890_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Completion_CompletionResolution(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Linter_Deprecated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Completion_CompletionResolution(
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
pub unsafe fn initialize_Lean_Server_Completion_CompletionResolution(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Server_Completion_CompletionInfoSelection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Linter_Deprecated(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Completion_CompletionResolution(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Completion_CompletionResolution(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Server_Completion_CompletionResolution(builtin);
}
