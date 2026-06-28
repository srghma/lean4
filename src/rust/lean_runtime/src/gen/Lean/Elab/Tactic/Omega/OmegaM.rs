// Lean compiler output
// Module: Lean.Elab.Tactic.Omega.OmegaM
// Imports: Lean.Meta.AppBuilder Lean.Meta.Canonicalizer Init.Omega
use crate::r#gen::Init::Data::Int::Basic::{
    l_Int_add___boxed, l_Int_mul___boxed, l_Int_pow, l_Int_sub___boxed, l_Int_toNat,
};
use crate::r#gen::Init::Data::Int::DivMod::Basic::l_Int_ediv___boxed;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Nat_add___boxed, l_Nat_div___boxed, l_Nat_mul___boxed, l_Nat_pow___boxed,
    l_Nat_sub___boxed,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_const___override, l_Lean_Expr_getAppFnArgs,
    l_Lean_Expr_hash, l_Lean_Expr_int_x3f, l_Lean_Expr_nat_x3f, l_Lean_mkApp3, l_Lean_mkApp4,
    l_Lean_mkApp5, l_Lean_mkAppB, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofList, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkDecideProof, l_Lean_Meta_mkEq,
    l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkExpectedPropHint, l_Lean_Meta_mkListLit,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Canonicalizer::{
    initialize_Lean_Meta_Canonicalizer, l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg,
    l_Lean_Meta_Canonicalizer_canon, runtime_initialize_Lean_Meta_Canonicalizer,
};
use crate::r#gen::Lean::ToExpr::l_Lean_instToExprInt_mkNat;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_le, lean_int_neg, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_string_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_10, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint8_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value: LeanStringObject<4> =
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
        m_data: [73, 110, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [79, 109, 101, 103, 97, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value: LeanStringObject<7> =
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
        m_data: [67, 111, 101, 102, 102, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value: LeanStringObject<7> =
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
        m_data: [111, 102, 76, 105, 115, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
                as *mut LeanObject,
            17910073349994400881 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__2_value)
                as *mut LeanObject,
            10725639862586182856 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__3_value)
                as *mut LeanObject,
            11430621368878064144 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value: LeanStringObject<4> =
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
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1_value: LeanStringObject<5> =
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
        m_data: [99, 97, 115, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0_value: LeanStringObject<5> =
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
        m_data: [72, 65, 100, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1_value: LeanStringObject<5> =
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
        m_data: [72, 77, 117, 108, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2_value: LeanStringObject<5> =
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
        m_data: [72, 83, 117, 98, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3_value: LeanStringObject<5> =
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
        m_data: [72, 68, 105, 118, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4_value: LeanStringObject<5> =
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
        m_data: [72, 80, 111, 119, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5_value: LeanStringObject<5> =
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
        m_data: [104, 80, 111, 119, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6_value: LeanClosureObject<0> =
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
        m_fun: l_Nat_pow___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7_value: LeanStringObject<5> =
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
        m_data: [104, 68, 105, 118, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8_value: LeanClosureObject<0> =
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
        m_fun: l_Nat_div___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9_value: LeanStringObject<5> =
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
        m_data: [104, 83, 117, 98, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10_value: LeanClosureObject<0> =
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
        m_fun: l_Nat_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11_value: LeanStringObject<5> =
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
        m_data: [104, 77, 117, 108, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12_value: LeanClosureObject<0> =
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
        m_fun: l_Nat_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13_value: LeanStringObject<5> =
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
        m_data: [104, 65, 100, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14_value: LeanClosureObject<0> =
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
        m_fun: l_Nat_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Int_ediv___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Int_sub___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Int_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3_value: LeanClosureObject<0> =
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
        m_fun: l_Int_add___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0_value: LeanStringObject<5> =
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
        m_data: [72, 77, 111, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1_value: LeanStringObject<4> =
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
        m_data: [77, 105, 110, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2_value: LeanStringObject<4> =
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
        m_data: [77, 97, 120, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3_value: LeanStringObject<4> =
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
        m_data: [109, 97, 120, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [108, 101, 95, 109, 97, 120, 95, 108, 101, 102, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__4_value)
                as *mut LeanObject,
            8528684718952576202 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value: LeanStringObject<13> =
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
        m_data: [108, 101, 95, 109, 97, 120, 95, 114, 105, 103, 104, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__7_value)
                as *mut LeanObject,
            4653461862122275003 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10_value: LeanStringObject<4> =
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
        m_data: [109, 105, 110, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [109, 105, 110, 95, 108, 101, 95, 108, 101, 102, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__11_value)
                as *mut LeanObject,
            15037249822398505490 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value: LeanStringObject<13> =
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
        m_data: [109, 105, 110, 95, 108, 101, 95, 114, 105, 103, 104, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__14_value)
                as *mut LeanObject,
            970802058389122393 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17_value: LeanStringObject<5> =
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
        m_data: [104, 77, 111, 100, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value: LeanStringObject<18> =
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
            101, 109, 111, 100, 95, 111, 102, 78, 97, 116, 95, 110, 111, 110, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
                as *mut LeanObject,
            17910073349994400881 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            488667332567600511 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__18_value)
                as *mut LeanObject,
            10638584452205461697 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value: LeanStringObject<3> =
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
        m_data: [76, 84, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value: LeanStringObject<3> =
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
        m_data: [108, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__20_value)
                as *mut LeanObject,
            17878876274162330439 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__21_value)
                as *mut LeanObject,
            11833570877100518198 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value: LeanStringObject<10> =
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
        m_data: [105, 110, 115, 116, 76, 84, 78, 97, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__25_value)
                as *mut LeanObject,
            14651840373392481165 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value: LeanStringObject<8> =
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
        m_data: [112, 111, 119, 95, 112, 111, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__28_value)
                as *mut LeanObject,
            14111604343637326856 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            111, 102, 78, 97, 116, 95, 112, 111, 115, 95, 111, 102, 95, 112, 111, 115, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
                as *mut LeanObject,
            17910073349994400881 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            488667332567600511 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__30_value)
                as *mut LeanObject,
            13216564244333251368 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [101, 109, 111, 100, 95, 110, 111, 110, 110, 101, 103, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__32_value)
                as *mut LeanObject,
            17157738005422892093 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value: LeanStringObject<9> =
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
        m_data: [110, 101, 95, 111, 102, 95, 103, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__34_value)
                as *mut LeanObject,
            11675868500096275836 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            101, 109, 111, 100, 95, 108, 116, 95, 111, 102, 95, 112, 111, 115, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__36_value)
                as *mut LeanObject,
            15154550989551304115 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39: u8 = 0;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value: LeanStringObject<4> =
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
        m_data: [78, 101, 103, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value: LeanStringObject<4> =
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
        m_data: [110, 101, 103, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__40_value)
                as *mut LeanObject,
            9626815015619986526 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__41_value)
                as *mut LeanObject,
            17185717442815859305 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value: LeanStringObject<11> =
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
        m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__43_value)
                as *mut LeanObject,
            6362876895233142233 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value: LeanStringObject<10> =
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
        m_data: [105, 110, 115, 116, 76, 84, 73, 110, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__52_value)
                as *mut LeanObject,
            9121383836933346478 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            112, 111, 115, 95, 112, 111, 119, 95, 111, 102, 95, 112, 111, 115, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
                as *mut LeanObject,
            17910073349994400881 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            488667332567600511 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__55_value)
                as *mut LeanObject,
            8404793396275648913 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value: LeanStringObject<3> =
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
        m_data: [78, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__64_value)
                as *mut LeanObject,
            6695605208187598753 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value: LeanStringObject<17> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            109, 117, 108, 95, 101, 100, 105, 118, 95, 115, 101, 108, 102, 95, 108, 101, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__69_value)
                as *mut LeanObject,
            15464796390623215100 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value: LeanStringObject<21> =
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
            108, 116, 95, 109, 117, 108, 95, 101, 100, 105, 118, 95, 115, 101, 108, 102, 95, 97,
            100, 100, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__72_value)
                as *mut LeanObject,
            17601256755593845854 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value: LeanStringObject<14> =
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
        m_data: [
            110, 101, 103, 95, 108, 101, 95, 110, 97, 116, 65, 98, 115, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
                as *mut LeanObject,
            17910073349994400881 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            488667332567600511 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__75_value)
                as *mut LeanObject,
            13309385938308562393 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            110, 97, 116, 67, 97, 115, 116, 95, 110, 111, 110, 110, 101, 103, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__77_value)
                as *mut LeanObject,
            17750334692303158606 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value: LeanStringObject<7> =
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
        m_data: [66, 105, 116, 86, 101, 99, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value: LeanStringObject<5> =
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
        m_data: [105, 115, 76, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79_value)
                as *mut LeanObject,
            5394957827732845164 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value)
                as *mut LeanObject,
            8436147975023434436 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value: LeanStringObject<4> =
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
        m_data: [70, 105, 110, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82_value)
                as *mut LeanObject,
            15815496672699636542 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__80_value)
                as *mut LeanObject,
            4938441192065111774 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value: LeanStringObject<10> =
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
        m_data: [108, 101, 95, 110, 97, 116, 65, 98, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__84_value)
                as *mut LeanObject,
            6348096724845679194 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 111, 78, 97, 116, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value: LeanStringObject<4> =
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
        m_data: [118, 97, 108, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_value: LeanStringObject<7> =
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
        m_data: [110, 97, 116, 65, 98, 115, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value: LeanStringObject<20> =
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
            111, 102, 78, 97, 116, 95, 115, 117, 98, 95, 100, 105, 99, 104, 111, 116, 111, 109,
            121, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
                as *mut LeanObject,
            17910073349994400881 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_2: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0_value)
                as *mut LeanObject,
            488667332567600511 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__89_value)
                as *mut LeanObject,
            4345411359602094212 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91_value: LeanStringObject<4> =
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
        m_data: [105, 116, 101, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            105, 116, 101, 95, 100, 105, 115, 106, 117, 110, 99, 116, 105, 111, 110, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value)
        as *mut LeanObject;
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__1_value)
                as *mut LeanObject,
            17910073349994400881 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__92_value)
                as *mut LeanObject,
            7682406714577881933 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0:
    f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__0_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [111, 109, 101, 103, 97, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__0_value) as *mut LeanObject,
        11366375744198450027 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__2_value: LeanStringObject<6> =
    LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__2_value) as *mut LeanObject,
        14231257465488249300 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__3_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__5_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [78, 101, 119, 32, 102, 97, 99, 116, 115, 58, 32, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__5_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Omega_lookup___closed__7_value: LeanStringObject<11> =
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
        m_data: [78, 101, 119, 32, 97, 116, 111, 109, 58, 32, 0],
    };
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Omega_lookup___closed__7_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Omega_lookup___closed__8: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(
    mut v___x_2347_: *mut LeanObject,
    mut v___x_2348_: *mut LeanObject,
    mut v_m_2349_: *mut LeanObject,
    mut v_cfg_2350_: *mut LeanObject,
    mut v___y_2351_: u8,
    mut v___y_2352_: *mut LeanObject,
    mut v___y_2353_: *mut LeanObject,
    mut v___y_2354_: *mut LeanObject,
    mut v___y_2355_: *mut LeanObject,
    mut v___y_2356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2358_ = lean_st_mk_ref(v___x_2347_);
                v___x_2359_ = lean_st_mk_ref(v___x_2348_);
                v___x_2360_ = lean_box((v___y_2351_) as usize);
                lean_inc(v___y_2356_);
                lean_inc_ref(v___y_2355_);
                lean_inc(v___y_2354_);
                lean_inc_ref(v___y_2353_);
                lean_inc(v___y_2352_);
                lean_inc(v___x_2358_);
                lean_inc(v___x_2359_);
                v___x_2361_ = lean_apply_10(
                    v_m_2349_,
                    v___x_2359_,
                    v___x_2358_,
                    v_cfg_2350_,
                    v___x_2360_,
                    v___y_2352_,
                    v___y_2353_,
                    v___y_2354_,
                    v___y_2355_,
                    v___y_2356_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2361_) == 0 {
                    v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
                    v_isSharedCheck_2371_ = (!lean_is_exclusive(v___x_2361_)) as u8;
                    if v_isSharedCheck_2371_ == 0 {
                        v___x_2364_ = v___x_2361_;
                        v_isShared_2365_ = v_isSharedCheck_2371_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2362_);
                        lean_dec(v___x_2361_);
                        v___x_2364_ = lean_box(0);
                        v_isShared_2365_ = v_isSharedCheck_2371_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2359_);
                    lean_dec(v___x_2358_);
                    return v___x_2361_;
                }
            }
            1 => {
                v___x_2366_ = lean_st_ref_get(v___x_2359_);
                lean_dec(v___x_2359_);
                lean_dec(v___x_2366_);
                v___x_2367_ = lean_st_ref_get(v___x_2358_);
                lean_dec(v___x_2358_);
                lean_dec(v___x_2367_);
                if v_isShared_2365_ == 0 {
                    v___x_2369_ = v___x_2364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2362_);
                    v___x_2369_ = v_reuseFailAlloc_2370_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2369_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed(
    mut v___x_2372_: *mut LeanObject,
    mut v___x_2373_: *mut LeanObject,
    mut v_m_2374_: *mut LeanObject,
    mut v_cfg_2375_: *mut LeanObject,
    mut v___y_2376_: *mut LeanObject,
    mut v___y_2377_: *mut LeanObject,
    mut v___y_2378_: *mut LeanObject,
    mut v___y_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_4823__boxed_2383_: u8 = 0;
    let mut v_res_2384_: *mut LeanObject = core::ptr::null_mut();
    v___y_4823__boxed_2383_ = (lean_unbox(v___y_2376_) as u8);
    v_res_2384_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0(
        v___x_2372_,
        v___x_2373_,
        v_m_2374_,
        v_cfg_2375_,
        v___y_4823__boxed_2383_,
        v___y_2377_,
        v___y_2378_,
        v___y_2379_,
        v___y_2380_,
        v___y_2381_,
    );
    lean_dec(v___y_2381_);
    lean_dec_ref(v___y_2380_);
    lean_dec(v___y_2379_);
    lean_dec_ref(v___y_2378_);
    lean_dec(v___y_2377_);
    return v_res_2384_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    v___x_2385_ = lean_box(0);
    v___x_2386_ = lean_unsigned_to_nat(16);
    v___x_2387_ = lean_mk_array(v___x_2386_, v___x_2385_);
    return v___x_2387_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    v___x_2388_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__0,
    );
    v___x_2389_ = lean_unsigned_to_nat(0);
    v___x_2390_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2390_, 0, v___x_2389_);
    lean_ctor_set(v___x_2390_, 1, v___x_2388_);
    return v___x_2390_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v___x_2391_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1,
    );
    v___x_2392_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2392_, 0, v___x_2391_);
    lean_ctor_set(v___x_2392_, 1, v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(
    mut v_m_2393_: *mut LeanObject,
    mut v_cfg_2394_: *mut LeanObject,
    mut v_a_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
    mut v_a_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: u8 = 0;
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut LeanObject = core::ptr::null_mut();
    v___x_2400_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__1,
    );
    v___f_2401_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___lam__0___boxed as *mut core::ffi::c_void,
        11,
        4,
    );
    lean_closure_set(v___f_2401_, 0, v___x_2400_);
    lean_closure_set(v___f_2401_, 1, v___x_2400_);
    lean_closure_set(v___f_2401_, 2, v_m_2393_);
    lean_closure_set(v___f_2401_, 3, v_cfg_2394_);
    v___x_2402_ = 3;
    v___x_2403_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___closed__2,
    );
    v___x_2404_ = l_Lean_Meta_Canonicalizer_CanonM_run_x27___redArg(
        v___f_2401_,
        v___x_2402_,
        v___x_2403_,
        v_a_2395_,
        v_a_2396_,
        v_a_2397_,
        v_a_2398_,
    );
    return v___x_2404_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg___boxed(
    mut v_m_2405_: *mut LeanObject,
    mut v_cfg_2406_: *mut LeanObject,
    mut v_a_2407_: *mut LeanObject,
    mut v_a_2408_: *mut LeanObject,
    mut v_a_2409_: *mut LeanObject,
    mut v_a_2410_: *mut LeanObject,
    mut v_a_2411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2412_: *mut LeanObject = core::ptr::null_mut();
    v_res_2412_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(
        v_m_2405_,
        v_cfg_2406_,
        v_a_2407_,
        v_a_2408_,
        v_a_2409_,
        v_a_2410_,
    );
    lean_dec(v_a_2410_);
    lean_dec_ref(v_a_2409_);
    lean_dec(v_a_2408_);
    lean_dec_ref(v_a_2407_);
    return v_res_2412_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run(
    mut v_00_u03b1_2413_: *mut LeanObject,
    mut v_m_2414_: *mut LeanObject,
    mut v_cfg_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
    mut v_a_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    v___x_2421_ = l_Lean_Elab_Tactic_Omega_OmegaM_run___redArg(
        v_m_2414_,
        v_cfg_2415_,
        v_a_2416_,
        v_a_2417_,
        v_a_2418_,
        v_a_2419_,
    );
    return v___x_2421_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_OmegaM_run___boxed(
    mut v_00_u03b1_2422_: *mut LeanObject,
    mut v_m_2423_: *mut LeanObject,
    mut v_cfg_2424_: *mut LeanObject,
    mut v_a_2425_: *mut LeanObject,
    mut v_a_2426_: *mut LeanObject,
    mut v_a_2427_: *mut LeanObject,
    mut v_a_2428_: *mut LeanObject,
    mut v_a_2429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2430_: *mut LeanObject = core::ptr::null_mut();
    v_res_2430_ = l_Lean_Elab_Tactic_Omega_OmegaM_run(
        v_00_u03b1_2422_,
        v_m_2423_,
        v_cfg_2424_,
        v_a_2425_,
        v_a_2426_,
        v_a_2427_,
        v_a_2428_,
    );
    lean_dec(v_a_2428_);
    lean_dec_ref(v_a_2427_);
    lean_dec(v_a_2426_);
    lean_dec_ref(v_a_2425_);
    return v_res_2430_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg___redArg(
    mut v_a_2431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_2431_);
    v___x_2433_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2433_, 0, v_a_2431_);
    return v___x_2433_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg___redArg___boxed(
    mut v_a_2434_: *mut LeanObject,
    mut v_a_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2436_: *mut LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_Elab_Tactic_Omega_cfg___redArg(v_a_2434_);
    lean_dec_ref(v_a_2434_);
    return v_res_2436_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg(
    mut v_a_2437_: *mut LeanObject,
    mut v_a_2438_: *mut LeanObject,
    mut v_a_2439_: *mut LeanObject,
    mut v_a_2440_: u8,
    mut v_a_2441_: *mut LeanObject,
    mut v_a_2442_: *mut LeanObject,
    mut v_a_2443_: *mut LeanObject,
    mut v_a_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_a_2439_);
    v___x_2447_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2447_, 0, v_a_2439_);
    return v___x_2447_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_cfg___boxed(
    mut v_a_2448_: *mut LeanObject,
    mut v_a_2449_: *mut LeanObject,
    mut v_a_2450_: *mut LeanObject,
    mut v_a_2451_: *mut LeanObject,
    mut v_a_2452_: *mut LeanObject,
    mut v_a_2453_: *mut LeanObject,
    mut v_a_2454_: *mut LeanObject,
    mut v_a_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
    mut v_a_2457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2458_: u8 = 0;
    let mut v_res_2459_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2458_ = (lean_unbox(v_a_2451_) as u8);
    v_res_2459_ = l_Lean_Elab_Tactic_Omega_cfg(
        v_a_2448_,
        v_a_2449_,
        v_a_2450_,
        v_a_boxed_2458_,
        v_a_2452_,
        v_a_2453_,
        v_a_2454_,
        v_a_2455_,
        v_a_2456_,
    );
    lean_dec(v_a_2456_);
    lean_dec_ref(v_a_2455_);
    lean_dec(v_a_2454_);
    lean_dec_ref(v_a_2453_);
    lean_dec(v_a_2452_);
    lean_dec_ref(v_a_2450_);
    lean_dec(v_a_2449_);
    lean_dec(v_a_2448_);
    return v_res_2459_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(
    mut v_hi_2460_: *mut LeanObject,
    mut v_pivot_2461_: *mut LeanObject,
    mut v_as_2462_: *mut LeanObject,
    mut v_i_2463_: *mut LeanObject,
    mut v_k_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2465_ = lean_nat_dec_lt(v_k_2464_, v_hi_2460_);
                if v___x_2465_ == 0 {
                    lean_dec(v_k_2464_);
                    v___x_2466_ = lean_array_fswap(v_as_2462_, v_i_2463_, v_hi_2460_);
                    v___x_2467_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2467_, 0, v_i_2463_);
                    lean_ctor_set(v___x_2467_, 1, v___x_2466_);
                    return v___x_2467_;
                } else {
                    v___x_2468_ = lean_array_fget_borrowed(v_as_2462_, v_k_2464_);
                    v_snd_2469_ = lean_ctor_get(v___x_2468_, 1);
                    v_snd_2470_ = lean_ctor_get(v_pivot_2461_, 1);
                    v___x_2471_ = lean_nat_dec_lt(v_snd_2469_, v_snd_2470_);
                    if v___x_2471_ == 0 {
                        v___x_2472_ = lean_unsigned_to_nat(1);
                        v___x_2473_ = lean_nat_add(v_k_2464_, v___x_2472_);
                        lean_dec(v_k_2464_);
                        v_k_2464_ = v___x_2473_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2475_ = lean_array_fswap(v_as_2462_, v_i_2463_, v_k_2464_);
                        v___x_2476_ = lean_unsigned_to_nat(1);
                        v___x_2477_ = lean_nat_add(v_i_2463_, v___x_2476_);
                        lean_dec(v_i_2463_);
                        v___x_2478_ = lean_nat_add(v_k_2464_, v___x_2476_);
                        lean_dec(v_k_2464_);
                        v_as_2462_ = v___x_2475_;
                        v_i_2463_ = v___x_2477_;
                        v_k_2464_ = v___x_2478_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg___boxed(
    mut v_hi_2480_: *mut LeanObject,
    mut v_pivot_2481_: *mut LeanObject,
    mut v_as_2482_: *mut LeanObject,
    mut v_i_2483_: *mut LeanObject,
    mut v_k_2484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2485_: *mut LeanObject = core::ptr::null_mut();
    v_res_2485_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_2480_, v_pivot_2481_, v_as_2482_, v_i_2483_, v_k_2484_);
    lean_dec_ref(v_pivot_2481_);
    lean_dec(v_hi_2480_);
    return v_res_2485_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(
    mut v_x1_2486_: *mut LeanObject,
    mut v_x2_2487_: *mut LeanObject,
) -> u8 {
    let mut v_snd_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: u8 = 0;
    v_snd_2488_ = lean_ctor_get(v_x1_2486_, 1);
    v_snd_2489_ = lean_ctor_get(v_x2_2487_, 1);
    v___x_2490_ = lean_nat_dec_lt(v_snd_2488_, v_snd_2489_);
    return v___x_2490_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0___boxed(
    mut v_x1_2491_: *mut LeanObject,
    mut v_x2_2492_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2493_: u8 = 0;
    let mut v_r_2494_: *mut LeanObject = core::ptr::null_mut();
    v_res_2493_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v_x1_2491_, v_x2_2492_);
    lean_dec_ref(v_x2_2492_);
    lean_dec_ref(v_x1_2491_);
    v_r_2494_ = lean_box((v_res_2493_) as usize);
    return v_r_2494_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(
    mut v_n_2495_: *mut LeanObject,
    mut v_as_2496_: *mut LeanObject,
    mut v_lo_2497_: *mut LeanObject,
    mut v_hi_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pivot_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: u8 = 0;
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mid_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: u8 = 0;
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: u8 = 0;
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: u8 = 0;
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2510_ = lean_nat_dec_lt(v_lo_2497_, v_hi_2498_);
                if v___x_2510_ == 0 {
                    lean_dec(v_lo_2497_);
                    return v_as_2496_;
                } else {
                    v___x_2511_ = lean_nat_add(v_lo_2497_, v_hi_2498_);
                    v___x_2512_ = lean_unsigned_to_nat(1);
                    v_mid_2513_ = lean_nat_shiftr(v___x_2511_, v___x_2512_);
                    lean_dec(v___x_2511_);
                    v___x_2526_ = lean_array_fget_borrowed(v_as_2496_, v_mid_2513_);
                    v___x_2527_ = lean_array_fget_borrowed(v_as_2496_, v_lo_2497_);
                    v___x_2528_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_2526_, v___x_2527_);
                    if v___x_2528_ == 0 {
                        v___y_2521_ = v_as_2496_;
                        state = 3;
                        continue;
                    } else {
                        v___x_2529_ = lean_array_fswap(v_as_2496_, v_lo_2497_, v_mid_2513_);
                        v___y_2521_ = v___x_2529_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_2501_ = lean_array_fget(v___y_2500_, v_hi_2498_);
                lean_inc_n(v_lo_2497_, 2);
                v___x_2502_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_2498_, v_pivot_2501_, v___y_2500_, v_lo_2497_, v_lo_2497_);
                lean_dec(v_pivot_2501_);
                v_fst_2503_ = lean_ctor_get(v___x_2502_, 0);
                lean_inc(v_fst_2503_);
                v_snd_2504_ = lean_ctor_get(v___x_2502_, 1);
                lean_inc(v_snd_2504_);
                lean_dec_ref(v___x_2502_);
                v___x_2505_ = lean_nat_dec_le(v_hi_2498_, v_fst_2503_);
                if v___x_2505_ == 0 {
                    v___x_2506_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_2495_, v_snd_2504_, v_lo_2497_, v_fst_2503_);
                    v___x_2507_ = lean_unsigned_to_nat(1);
                    v___x_2508_ = lean_nat_add(v_fst_2503_, v___x_2507_);
                    lean_dec(v_fst_2503_);
                    v_as_2496_ = v___x_2506_;
                    v_lo_2497_ = v___x_2508_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_fst_2503_);
                    lean_dec(v_lo_2497_);
                    return v_snd_2504_;
                }
            }
            2 => {
                v___x_2516_ = lean_array_fget_borrowed(v___y_2515_, v_mid_2513_);
                v___x_2517_ = lean_array_fget_borrowed(v___y_2515_, v_hi_2498_);
                v___x_2518_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_2516_, v___x_2517_);
                if v___x_2518_ == 0 {
                    lean_dec(v_mid_2513_);
                    v___y_2500_ = v___y_2515_;
                    state = 1;
                    continue;
                } else {
                    v___x_2519_ = lean_array_fswap(v___y_2515_, v_mid_2513_, v_hi_2498_);
                    lean_dec(v_mid_2513_);
                    v___y_2500_ = v___x_2519_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_2522_ = lean_array_fget_borrowed(v___y_2521_, v_hi_2498_);
                v___x_2523_ = lean_array_fget_borrowed(v___y_2521_, v_lo_2497_);
                v___x_2524_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___lam__0(v___x_2522_, v___x_2523_);
                if v___x_2524_ == 0 {
                    v___y_2515_ = v___y_2521_;
                    state = 2;
                    continue;
                } else {
                    v___x_2525_ = lean_array_fswap(v___y_2521_, v_lo_2497_, v_hi_2498_);
                    v___y_2515_ = v___x_2525_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg___boxed(
    mut v_n_2530_: *mut LeanObject,
    mut v_as_2531_: *mut LeanObject,
    mut v_lo_2532_: *mut LeanObject,
    mut v_hi_2533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2534_: *mut LeanObject = core::ptr::null_mut();
    v_res_2534_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_2530_, v_as_2531_, v_lo_2532_, v_hi_2533_);
    lean_dec(v_hi_2533_);
    lean_dec(v_n_2530_);
    return v_res_2534_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(
    mut v_x_2535_: *mut LeanObject,
    mut v_x_2536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2536_) == 0 {
                    return v_x_2535_;
                } else {
                    v_key_2537_ = lean_ctor_get(v_x_2536_, 0);
                    v_value_2538_ = lean_ctor_get(v_x_2536_, 1);
                    v_tail_2539_ = lean_ctor_get(v_x_2536_, 2);
                    lean_inc(v_value_2538_);
                    lean_inc(v_key_2537_);
                    v___x_2540_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2540_, 0, v_key_2537_);
                    lean_ctor_set(v___x_2540_, 1, v_value_2538_);
                    v___x_2541_ = lean_array_push(v_x_2535_, v___x_2540_);
                    v_x_2535_ = v___x_2541_;
                    v_x_2536_ = v_tail_2539_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2___boxed(
    mut v_x_2543_: *mut LeanObject,
    mut v_x_2544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2545_: *mut LeanObject = core::ptr::null_mut();
    v_res_2545_ =
        l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(
            v_x_2543_, v_x_2544_,
        );
    lean_dec(v_x_2544_);
    return v_res_2545_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(
    mut v_as_2546_: *mut LeanObject,
    mut v_i_2547_: usize,
    mut v_stop_2548_: usize,
    mut v_b_2549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2550_: u8 = 0;
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: usize = 0;
    let mut v___x_2554_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2550_ = lean_usize_dec_eq(v_i_2547_, v_stop_2548_);
                if v___x_2550_ == 0 {
                    v___x_2551_ = lean_array_uget_borrowed(v_as_2546_, v_i_2547_);
                    v___x_2552_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Lean_Elab_Tactic_Omega_atoms_spec__2(v_b_2549_, v___x_2551_);
                    v___x_2553_ = 1usize;
                    v___x_2554_ = lean_usize_add(v_i_2547_, v___x_2553_);
                    v_i_2547_ = v___x_2554_;
                    v_b_2549_ = v___x_2552_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2549_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3___boxed(
    mut v_as_2556_: *mut LeanObject,
    mut v_i_2557_: *mut LeanObject,
    mut v_stop_2558_: *mut LeanObject,
    mut v_b_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2560_: usize = 0;
    let mut v_stop_boxed_2561_: usize = 0;
    let mut v_res_2562_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2560_ = lean_unbox_usize(v_i_2557_);
    lean_dec(v_i_2557_);
    v_stop_boxed_2561_ = lean_unbox_usize(v_stop_2558_);
    lean_dec(v_stop_2558_);
    v_res_2562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_as_2556_, v_i_boxed_2560_, v_stop_boxed_2561_, v_b_2559_);
    lean_dec_ref(v_as_2556_);
    return v_res_2562_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(
    mut v_sz_2563_: usize,
    mut v_i_2564_: usize,
    mut v_bs_2565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2566_: u8 = 0;
    let mut v_v_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2566_ = lean_usize_dec_lt(v_i_2564_, v_sz_2563_);
                if v___x_2566_ == 0 {
                    return v_bs_2565_;
                } else {
                    v_v_2567_ = lean_array_uget_borrowed(v_bs_2565_, v_i_2564_);
                    v_fst_2568_ = lean_ctor_get(v_v_2567_, 0);
                    lean_inc(v_fst_2568_);
                    v___x_2569_ = lean_unsigned_to_nat(0);
                    v_bs_x27_2570_ = lean_array_uset(v_bs_2565_, v_i_2564_, v___x_2569_);
                    v___x_2571_ = 1usize;
                    v___x_2572_ = lean_usize_add(v_i_2564_, v___x_2571_);
                    v___x_2573_ = lean_array_uset(v_bs_x27_2570_, v_i_2564_, v_fst_2568_);
                    v_i_2564_ = v___x_2572_;
                    v_bs_2565_ = v___x_2573_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0___boxed(
    mut v_sz_2575_: *mut LeanObject,
    mut v_i_2576_: *mut LeanObject,
    mut v_bs_2577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2578_: usize = 0;
    let mut v_i_boxed_2579_: usize = 0;
    let mut v_res_2580_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2578_ = lean_unbox_usize(v_sz_2575_);
    lean_dec(v_sz_2575_);
    v_i_boxed_2579_ = lean_unbox_usize(v_i_2576_);
    lean_dec(v_i_2576_);
    v_res_2580_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_boxed_2578_, v_i_boxed_2579_, v_bs_2577_);
    return v_res_2580_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms___redArg(
    mut v_a_2581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2586_: usize = 0;
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: u8 = 0;
    let mut v___y_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: u8 = 0;
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: u8 = 0;
    let mut v_size_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: u8 = 0;
    let mut v___x_2616_: u8 = 0;
    let mut v___x_2617_: usize = 0;
    let mut v___x_2618_: usize = 0;
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: usize = 0;
    let mut v___x_2621_: usize = 0;
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2583_ = lean_st_ref_get(v_a_2581_);
                v_size_2610_ = lean_ctor_get(v___x_2583_, 0);
                lean_inc(v_size_2610_);
                v_buckets_2611_ = lean_ctor_get(v___x_2583_, 1);
                lean_inc_ref(v_buckets_2611_);
                lean_dec(v___x_2583_);
                v___x_2612_ = lean_mk_empty_array_with_capacity(v_size_2610_);
                lean_dec(v_size_2610_);
                v___x_2613_ = lean_unsigned_to_nat(0);
                v___x_2614_ = lean_array_get_size(v_buckets_2611_);
                v___x_2615_ = lean_nat_dec_lt(v___x_2613_, v___x_2614_);
                if v___x_2615_ == 0 {
                    lean_dec_ref(v_buckets_2611_);
                    v___y_2603_ = v___x_2612_;
                    state = 4;
                    continue;
                } else {
                    v___x_2616_ = lean_nat_dec_le(v___x_2614_, v___x_2614_);
                    if v___x_2616_ == 0 {
                        if v___x_2615_ == 0 {
                            lean_dec_ref(v_buckets_2611_);
                            v___y_2603_ = v___x_2612_;
                            state = 4;
                            continue;
                        } else {
                            v___x_2617_ = 0usize;
                            v___x_2618_ = lean_usize_of_nat(v___x_2614_);
                            v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_2611_, v___x_2617_, v___x_2618_, v___x_2612_);
                            lean_dec_ref(v_buckets_2611_);
                            v___y_2603_ = v___x_2619_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___x_2620_ = 0usize;
                        v___x_2621_ = lean_usize_of_nat(v___x_2614_);
                        v___x_2622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Tactic_Omega_atoms_spec__3(v_buckets_2611_, v___x_2620_, v___x_2621_, v___x_2612_);
                        lean_dec_ref(v_buckets_2611_);
                        v___y_2603_ = v___x_2622_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_2586_ = lean_array_size(v___y_2585_);
                v___x_2587_ = 0usize;
                v___x_2588_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Tactic_Omega_atoms_spec__0(v_sz_2586_, v___x_2587_, v___y_2585_);
                v___x_2589_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2589_, 0, v___x_2588_);
                return v___x_2589_;
            }
            2 => {
                v___x_2595_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v___y_2593_, v___y_2591_, v___y_2592_, v___y_2594_);
                lean_dec(v___y_2594_);
                lean_dec(v___y_2593_);
                v___y_2585_ = v___x_2595_;
                state = 1;
                continue;
            }
            3 => {
                v___x_2601_ = lean_nat_dec_le(v___y_2600_, v___y_2598_);
                if v___x_2601_ == 0 {
                    lean_dec(v___y_2598_);
                    lean_inc(v___y_2600_);
                    v___y_2591_ = v___y_2597_;
                    v___y_2592_ = v___y_2600_;
                    v___y_2593_ = v___y_2599_;
                    v___y_2594_ = v___y_2600_;
                    state = 2;
                    continue;
                } else {
                    v___y_2591_ = v___y_2597_;
                    v___y_2592_ = v___y_2600_;
                    v___y_2593_ = v___y_2599_;
                    v___y_2594_ = v___y_2598_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2604_ = lean_array_get_size(v___y_2603_);
                v___x_2605_ = lean_unsigned_to_nat(0);
                v___x_2606_ = lean_nat_dec_eq(v___x_2604_, v___x_2605_);
                if v___x_2606_ == 0 {
                    v___x_2607_ = lean_unsigned_to_nat(1);
                    v___x_2608_ = lean_nat_sub(v___x_2604_, v___x_2607_);
                    v___x_2609_ = lean_nat_dec_le(v___x_2605_, v___x_2608_);
                    if v___x_2609_ == 0 {
                        lean_inc(v___x_2608_);
                        v___y_2597_ = v___y_2603_;
                        v___y_2598_ = v___x_2608_;
                        v___y_2599_ = v___x_2604_;
                        v___y_2600_ = v___x_2608_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2597_ = v___y_2603_;
                        v___y_2598_ = v___x_2608_;
                        v___y_2599_ = v___x_2604_;
                        v___y_2600_ = v___x_2605_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_2585_ = v___y_2603_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms___redArg___boxed(
    mut v_a_2623_: *mut LeanObject,
    mut v_a_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2625_: *mut LeanObject = core::ptr::null_mut();
    v_res_2625_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_2623_);
    lean_dec(v_a_2623_);
    return v_res_2625_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms(
    mut v_a_2626_: *mut LeanObject,
    mut v_a_2627_: *mut LeanObject,
    mut v_a_2628_: *mut LeanObject,
    mut v_a_2629_: u8,
    mut v_a_2630_: *mut LeanObject,
    mut v_a_2631_: *mut LeanObject,
    mut v_a_2632_: *mut LeanObject,
    mut v_a_2633_: *mut LeanObject,
    mut v_a_2634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    v___x_2636_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_2627_);
    return v___x_2636_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atoms___boxed(
    mut v_a_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_a_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v_a_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
    mut v_a_2644_: *mut LeanObject,
    mut v_a_2645_: *mut LeanObject,
    mut v_a_2646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2647_: u8 = 0;
    let mut v_res_2648_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2647_ = (lean_unbox(v_a_2640_) as u8);
    v_res_2648_ = l_Lean_Elab_Tactic_Omega_atoms(
        v_a_2637_,
        v_a_2638_,
        v_a_2639_,
        v_a_boxed_2647_,
        v_a_2641_,
        v_a_2642_,
        v_a_2643_,
        v_a_2644_,
        v_a_2645_,
    );
    lean_dec(v_a_2645_);
    lean_dec_ref(v_a_2644_);
    lean_dec(v_a_2643_);
    lean_dec_ref(v_a_2642_);
    lean_dec(v_a_2641_);
    lean_dec_ref(v_a_2639_);
    lean_dec(v_a_2638_);
    lean_dec(v_a_2637_);
    return v_res_2648_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(
    mut v_n_2649_: *mut LeanObject,
    mut v_as_2650_: *mut LeanObject,
    mut v_lo_2651_: *mut LeanObject,
    mut v_hi_2652_: *mut LeanObject,
    mut v_w_2653_: *mut LeanObject,
    mut v_hlo_2654_: *mut LeanObject,
    mut v_hhi_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    v___x_2656_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___redArg(v_n_2649_, v_as_2650_, v_lo_2651_, v_hi_2652_);
    return v___x_2656_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1___boxed(
    mut v_n_2657_: *mut LeanObject,
    mut v_as_2658_: *mut LeanObject,
    mut v_lo_2659_: *mut LeanObject,
    mut v_hi_2660_: *mut LeanObject,
    mut v_w_2661_: *mut LeanObject,
    mut v_hlo_2662_: *mut LeanObject,
    mut v_hhi_2663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2664_: *mut LeanObject = core::ptr::null_mut();
    v_res_2664_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1(v_n_2657_, v_as_2658_, v_lo_2659_, v_hi_2660_, v_w_2661_, v_hlo_2662_, v_hhi_2663_);
    lean_dec(v_hi_2660_);
    lean_dec(v_n_2657_);
    return v_res_2664_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(
    mut v_n_2665_: *mut LeanObject,
    mut v_lo_2666_: *mut LeanObject,
    mut v_hi_2667_: *mut LeanObject,
    mut v_hhi_2668_: *mut LeanObject,
    mut v_pivot_2669_: *mut LeanObject,
    mut v_as_2670_: *mut LeanObject,
    mut v_i_2671_: *mut LeanObject,
    mut v_k_2672_: *mut LeanObject,
    mut v_ilo_2673_: *mut LeanObject,
    mut v_ik_2674_: *mut LeanObject,
    mut v_w_2675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    v___x_2676_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___redArg(v_hi_2667_, v_pivot_2669_, v_as_2670_, v_i_2671_, v_k_2672_);
    return v___x_2676_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1___boxed(
    mut v_n_2677_: *mut LeanObject,
    mut v_lo_2678_: *mut LeanObject,
    mut v_hi_2679_: *mut LeanObject,
    mut v_hhi_2680_: *mut LeanObject,
    mut v_pivot_2681_: *mut LeanObject,
    mut v_as_2682_: *mut LeanObject,
    mut v_i_2683_: *mut LeanObject,
    mut v_k_2684_: *mut LeanObject,
    mut v_ilo_2685_: *mut LeanObject,
    mut v_ik_2686_: *mut LeanObject,
    mut v_w_2687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2688_: *mut LeanObject = core::ptr::null_mut();
    v_res_2688_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_Tactic_Omega_atoms_spec__1_spec__1(v_n_2677_, v_lo_2678_, v_hi_2679_, v_hhi_2680_, v_pivot_2681_, v_as_2682_, v_i_2683_, v_k_2684_, v_ilo_2685_, v_ik_2686_, v_w_2687_);
    lean_dec_ref(v_pivot_2681_);
    lean_dec(v_hi_2679_);
    lean_dec(v_lo_2678_);
    lean_dec(v_n_2677_);
    return v_res_2688_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    v___x_2692_ = lean_box(0);
    v___x_2693_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
    v___x_2694_ = l_Lean_Expr_const___override(v___x_2693_, v___x_2692_);
    return v___x_2694_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList___redArg(
    mut v_a_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
    mut v_a_2699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    v___x_2701_ = l_Lean_Elab_Tactic_Omega_atoms___redArg(v_a_2695_);
    v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
    lean_inc(v_a_2702_);
    lean_dec_ref(v___x_2701_);
    v___x_2703_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2,
    );
    v___x_2704_ = lean_array_to_list(v_a_2702_);
    v___x_2705_ = l_Lean_Meta_mkListLit(
        v___x_2703_,
        v___x_2704_,
        v_a_2696_,
        v_a_2697_,
        v_a_2698_,
        v_a_2699_,
    );
    return v___x_2705_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList___redArg___boxed(
    mut v_a_2706_: *mut LeanObject,
    mut v_a_2707_: *mut LeanObject,
    mut v_a_2708_: *mut LeanObject,
    mut v_a_2709_: *mut LeanObject,
    mut v_a_2710_: *mut LeanObject,
    mut v_a_2711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2712_: *mut LeanObject = core::ptr::null_mut();
    v_res_2712_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(
        v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_,
    );
    lean_dec(v_a_2710_);
    lean_dec_ref(v_a_2709_);
    lean_dec(v_a_2708_);
    lean_dec_ref(v_a_2707_);
    lean_dec(v_a_2706_);
    return v_res_2712_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList(
    mut v_a_2713_: *mut LeanObject,
    mut v_a_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
    mut v_a_2716_: u8,
    mut v_a_2717_: *mut LeanObject,
    mut v_a_2718_: *mut LeanObject,
    mut v_a_2719_: *mut LeanObject,
    mut v_a_2720_: *mut LeanObject,
    mut v_a_2721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    v___x_2723_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(
        v_a_2714_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_,
    );
    return v___x_2723_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsList___boxed(
    mut v_a_2724_: *mut LeanObject,
    mut v_a_2725_: *mut LeanObject,
    mut v_a_2726_: *mut LeanObject,
    mut v_a_2727_: *mut LeanObject,
    mut v_a_2728_: *mut LeanObject,
    mut v_a_2729_: *mut LeanObject,
    mut v_a_2730_: *mut LeanObject,
    mut v_a_2731_: *mut LeanObject,
    mut v_a_2732_: *mut LeanObject,
    mut v_a_2733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2734_: u8 = 0;
    let mut v_res_2735_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2734_ = (lean_unbox(v_a_2727_) as u8);
    v_res_2735_ = l_Lean_Elab_Tactic_Omega_atomsList(
        v_a_2724_,
        v_a_2725_,
        v_a_2726_,
        v_a_boxed_2734_,
        v_a_2728_,
        v_a_2729_,
        v_a_2730_,
        v_a_2731_,
        v_a_2732_,
    );
    lean_dec(v_a_2732_);
    lean_dec_ref(v_a_2731_);
    lean_dec(v_a_2730_);
    lean_dec_ref(v_a_2729_);
    lean_dec(v_a_2728_);
    lean_dec_ref(v_a_2726_);
    lean_dec(v_a_2725_);
    lean_dec(v_a_2724_);
    return v_res_2735_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    v___x_2745_ = lean_box(0);
    v___x_2746_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__4;
    v___x_2747_ = l_Lean_Expr_const___override(v___x_2746_, v___x_2745_);
    return v___x_2747_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(
    mut v_a_2748_: *mut LeanObject,
    mut v_a_2749_: *mut LeanObject,
    mut v_a_2750_: *mut LeanObject,
    mut v_a_2751_: *mut LeanObject,
    mut v_a_2752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2764_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2754_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg(
                    v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_, v_a_2752_,
                );
                if lean_obj_tag(v___x_2754_) == 0 {
                    v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
                    v_isSharedCheck_2764_ = (!lean_is_exclusive(v___x_2754_)) as u8;
                    if v_isSharedCheck_2764_ == 0 {
                        v___x_2757_ = v___x_2754_;
                        v_isShared_2758_ = v_isSharedCheck_2764_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2755_);
                        lean_dec(v___x_2754_);
                        v___x_2757_ = lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2764_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2754_;
                }
            }
            1 => {
                v___x_2759_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___closed__5,
                );
                v___x_2760_ = l_Lean_Expr_app___override(v___x_2759_, v_a_2755_);
                if v_isShared_2758_ == 0 {
                    lean_ctor_set(v___x_2757_, 0, v___x_2760_);
                    v___x_2762_ = v___x_2757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2760_);
                    v___x_2762_ = v_reuseFailAlloc_2763_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg___boxed(
    mut v_a_2765_: *mut LeanObject,
    mut v_a_2766_: *mut LeanObject,
    mut v_a_2767_: *mut LeanObject,
    mut v_a_2768_: *mut LeanObject,
    mut v_a_2769_: *mut LeanObject,
    mut v_a_2770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2771_: *mut LeanObject = core::ptr::null_mut();
    v_res_2771_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(
        v_a_2765_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_,
    );
    lean_dec(v_a_2769_);
    lean_dec_ref(v_a_2768_);
    lean_dec(v_a_2767_);
    lean_dec_ref(v_a_2766_);
    lean_dec(v_a_2765_);
    return v_res_2771_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs(
    mut v_a_2772_: *mut LeanObject,
    mut v_a_2773_: *mut LeanObject,
    mut v_a_2774_: *mut LeanObject,
    mut v_a_2775_: u8,
    mut v_a_2776_: *mut LeanObject,
    mut v_a_2777_: *mut LeanObject,
    mut v_a_2778_: *mut LeanObject,
    mut v_a_2779_: *mut LeanObject,
    mut v_a_2780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    v___x_2782_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs___redArg(
        v_a_2773_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_,
    );
    return v___x_2782_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_atomsCoeffs___boxed(
    mut v_a_2783_: *mut LeanObject,
    mut v_a_2784_: *mut LeanObject,
    mut v_a_2785_: *mut LeanObject,
    mut v_a_2786_: *mut LeanObject,
    mut v_a_2787_: *mut LeanObject,
    mut v_a_2788_: *mut LeanObject,
    mut v_a_2789_: *mut LeanObject,
    mut v_a_2790_: *mut LeanObject,
    mut v_a_2791_: *mut LeanObject,
    mut v_a_2792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2793_: u8 = 0;
    let mut v_res_2794_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2793_ = (lean_unbox(v_a_2786_) as u8);
    v_res_2794_ = l_Lean_Elab_Tactic_Omega_atomsCoeffs(
        v_a_2783_,
        v_a_2784_,
        v_a_2785_,
        v_a_boxed_2793_,
        v_a_2787_,
        v_a_2788_,
        v_a_2789_,
        v_a_2790_,
        v_a_2791_,
    );
    lean_dec(v_a_2791_);
    lean_dec_ref(v_a_2790_);
    lean_dec(v_a_2789_);
    lean_dec_ref(v_a_2788_);
    lean_dec(v_a_2787_);
    lean_dec_ref(v_a_2785_);
    lean_dec(v_a_2784_);
    lean_dec(v_a_2783_);
    return v_res_2794_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
    mut v_t_2795_: *mut LeanObject,
    mut v_a_2796_: *mut LeanObject,
    mut v_a_2797_: *mut LeanObject,
    mut v_a_2798_: *mut LeanObject,
    mut v_a_2799_: u8,
    mut v_a_2800_: *mut LeanObject,
    mut v_a_2801_: *mut LeanObject,
    mut v_a_2802_: *mut LeanObject,
    mut v_a_2803_: *mut LeanObject,
    mut v_a_2804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v_snd_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: u8 = 0;
    let mut v_fst_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2828_: u8 = 0;
    let mut v_a_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2832_: u8 = 0;
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2806_ = lean_st_ref_get(v_a_2797_);
                v___x_2807_ = lean_st_ref_get(v_a_2796_);
                v___x_2808_ = lean_box((v_a_2799_) as usize);
                lean_inc(v_a_2804_);
                lean_inc_ref(v_a_2803_);
                lean_inc(v_a_2802_);
                lean_inc_ref(v_a_2801_);
                lean_inc(v_a_2800_);
                lean_inc_ref(v_a_2798_);
                lean_inc(v_a_2797_);
                lean_inc(v_a_2796_);
                v___x_2809_ = lean_apply_10(
                    v_t_2795_,
                    v_a_2796_,
                    v_a_2797_,
                    v_a_2798_,
                    v___x_2808_,
                    v_a_2800_,
                    v_a_2801_,
                    v_a_2802_,
                    v_a_2803_,
                    v_a_2804_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2809_) == 0 {
                    v_a_2810_ = lean_ctor_get(v___x_2809_, 0);
                    v_isSharedCheck_2828_ = (!lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2828_ == 0 {
                        v___x_2812_ = v___x_2809_;
                        v_isShared_2813_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2810_);
                        lean_dec(v___x_2809_);
                        v___x_2812_ = lean_box(0);
                        v_isShared_2813_ = v_isSharedCheck_2828_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2807_);
                    lean_dec(v___x_2806_);
                    v_a_2829_ = lean_ctor_get(v___x_2809_, 0);
                    v_isSharedCheck_2836_ = (!lean_is_exclusive(v___x_2809_)) as u8;
                    if v_isSharedCheck_2836_ == 0 {
                        v___x_2831_ = v___x_2809_;
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2829_);
                        lean_dec(v___x_2809_);
                        v___x_2831_ = lean_box(0);
                        v_isShared_2832_ = v_isSharedCheck_2836_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2814_ = lean_ctor_get(v_a_2810_, 1);
                v___x_2815_ = (lean_unbox(v_snd_2814_) as u8);
                if v___x_2815_ == 0 {
                    v_fst_2816_ = lean_ctor_get(v_a_2810_, 0);
                    lean_inc(v_fst_2816_);
                    lean_dec(v_a_2810_);
                    v___x_2817_ = lean_st_ref_take(v_a_2797_);
                    lean_dec(v___x_2817_);
                    v___x_2818_ = lean_st_ref_set(v_a_2797_, v___x_2806_);
                    v___x_2819_ = lean_st_ref_take(v_a_2796_);
                    lean_dec(v___x_2819_);
                    v___x_2820_ = lean_st_ref_set(v_a_2796_, v___x_2807_);
                    if v_isShared_2813_ == 0 {
                        lean_ctor_set(v___x_2812_, 0, v_fst_2816_);
                        v___x_2822_ = v___x_2812_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_fst_2816_);
                        v___x_2822_ = v_reuseFailAlloc_2823_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2807_);
                    lean_dec(v___x_2806_);
                    v_fst_2824_ = lean_ctor_get(v_a_2810_, 0);
                    lean_inc(v_fst_2824_);
                    lean_dec(v_a_2810_);
                    if v_isShared_2813_ == 0 {
                        lean_ctor_set(v___x_2812_, 0, v_fst_2824_);
                        v___x_2826_ = v___x_2812_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_fst_2824_);
                        v___x_2826_ = v_reuseFailAlloc_2827_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2822_;
            }
            3 => {
                return v___x_2826_;
            }
            4 => {
                if v_isShared_2832_ == 0 {
                    v___x_2834_ = v___x_2831_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
                    v___x_2834_ = v_reuseFailAlloc_2835_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen___redArg___boxed(
    mut v_t_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
    mut v_a_2839_: *mut LeanObject,
    mut v_a_2840_: *mut LeanObject,
    mut v_a_2841_: *mut LeanObject,
    mut v_a_2842_: *mut LeanObject,
    mut v_a_2843_: *mut LeanObject,
    mut v_a_2844_: *mut LeanObject,
    mut v_a_2845_: *mut LeanObject,
    mut v_a_2846_: *mut LeanObject,
    mut v_a_2847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2848_: u8 = 0;
    let mut v_res_2849_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2848_ = (lean_unbox(v_a_2841_) as u8);
    v_res_2849_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
        v_t_2837_,
        v_a_2838_,
        v_a_2839_,
        v_a_2840_,
        v_a_boxed_2848_,
        v_a_2842_,
        v_a_2843_,
        v_a_2844_,
        v_a_2845_,
        v_a_2846_,
    );
    lean_dec(v_a_2846_);
    lean_dec_ref(v_a_2845_);
    lean_dec(v_a_2844_);
    lean_dec_ref(v_a_2843_);
    lean_dec(v_a_2842_);
    lean_dec_ref(v_a_2840_);
    lean_dec(v_a_2839_);
    lean_dec(v_a_2838_);
    return v_res_2849_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen(
    mut v_00_u03b1_2850_: *mut LeanObject,
    mut v_t_2851_: *mut LeanObject,
    mut v_a_2852_: *mut LeanObject,
    mut v_a_2853_: *mut LeanObject,
    mut v_a_2854_: *mut LeanObject,
    mut v_a_2855_: u8,
    mut v_a_2856_: *mut LeanObject,
    mut v_a_2857_: *mut LeanObject,
    mut v_a_2858_: *mut LeanObject,
    mut v_a_2859_: *mut LeanObject,
    mut v_a_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    v___x_2862_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
        v_t_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_, v_a_2856_, v_a_2857_, v_a_2858_,
        v_a_2859_, v_a_2860_,
    );
    return v___x_2862_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_commitWhen___boxed(
    mut v_00_u03b1_2863_: *mut LeanObject,
    mut v_t_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
    mut v_a_2866_: *mut LeanObject,
    mut v_a_2867_: *mut LeanObject,
    mut v_a_2868_: *mut LeanObject,
    mut v_a_2869_: *mut LeanObject,
    mut v_a_2870_: *mut LeanObject,
    mut v_a_2871_: *mut LeanObject,
    mut v_a_2872_: *mut LeanObject,
    mut v_a_2873_: *mut LeanObject,
    mut v_a_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2875_: u8 = 0;
    let mut v_res_2876_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2875_ = (lean_unbox(v_a_2868_) as u8);
    v_res_2876_ = l_Lean_Elab_Tactic_Omega_commitWhen(
        v_00_u03b1_2863_,
        v_t_2864_,
        v_a_2865_,
        v_a_2866_,
        v_a_2867_,
        v_a_boxed_2875_,
        v_a_2869_,
        v_a_2870_,
        v_a_2871_,
        v_a_2872_,
        v_a_2873_,
    );
    lean_dec(v_a_2873_);
    lean_dec_ref(v_a_2872_);
    lean_dec(v_a_2871_);
    lean_dec_ref(v_a_2870_);
    lean_dec(v_a_2869_);
    lean_dec_ref(v_a_2867_);
    lean_dec(v_a_2866_);
    lean_dec(v_a_2865_);
    return v_res_2876_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(
    mut v_t_2877_: *mut LeanObject,
    mut v___y_2878_: *mut LeanObject,
    mut v___y_2879_: *mut LeanObject,
    mut v___y_2880_: *mut LeanObject,
    mut v___y_2881_: u8,
    mut v___y_2882_: *mut LeanObject,
    mut v___y_2883_: *mut LeanObject,
    mut v___y_2884_: *mut LeanObject,
    mut v___y_2885_: *mut LeanObject,
    mut v___y_2886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_a_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2888_ = lean_box((v___y_2881_) as usize);
                lean_inc(v___y_2886_);
                lean_inc_ref(v___y_2885_);
                lean_inc(v___y_2884_);
                lean_inc_ref(v___y_2883_);
                lean_inc(v___y_2882_);
                lean_inc_ref(v___y_2880_);
                lean_inc(v___y_2879_);
                lean_inc(v___y_2878_);
                v___x_2889_ = lean_apply_10(
                    v_t_2877_,
                    v___y_2878_,
                    v___y_2879_,
                    v___y_2880_,
                    v___x_2888_,
                    v___y_2882_,
                    v___y_2883_,
                    v___y_2884_,
                    v___y_2885_,
                    v___y_2886_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2889_) == 0 {
                    v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
                    v_isSharedCheck_2900_ = (!lean_is_exclusive(v___x_2889_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2892_ = v___x_2889_;
                        v_isShared_2893_ = v_isSharedCheck_2900_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2890_);
                        lean_dec(v___x_2889_);
                        v___x_2892_ = lean_box(0);
                        v_isShared_2893_ = v_isSharedCheck_2900_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2901_ = lean_ctor_get(v___x_2889_, 0);
                    v_isSharedCheck_2908_ = (!lean_is_exclusive(v___x_2889_)) as u8;
                    if v_isSharedCheck_2908_ == 0 {
                        v___x_2903_ = v___x_2889_;
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2901_);
                        lean_dec(v___x_2889_);
                        v___x_2903_ = lean_box(0);
                        v_isShared_2904_ = v_isSharedCheck_2908_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2894_ = 0;
                v___x_2895_ = lean_box((v___x_2894_) as usize);
                v___x_2896_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2896_, 0, v_a_2890_);
                lean_ctor_set(v___x_2896_, 1, v___x_2895_);
                if v_isShared_2893_ == 0 {
                    lean_ctor_set(v___x_2892_, 0, v___x_2896_);
                    v___x_2898_ = v___x_2892_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
                    v___x_2898_ = v_reuseFailAlloc_2899_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2898_;
            }
            3 => {
                if v_isShared_2904_ == 0 {
                    v___x_2906_ = v___x_2903_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
                    v___x_2906_ = v_reuseFailAlloc_2907_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed(
    mut v_t_2909_: *mut LeanObject,
    mut v___y_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
    mut v___y_2912_: *mut LeanObject,
    mut v___y_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
    mut v___y_2915_: *mut LeanObject,
    mut v___y_2916_: *mut LeanObject,
    mut v___y_2917_: *mut LeanObject,
    mut v___y_2918_: *mut LeanObject,
    mut v___y_2919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_657__boxed_2920_: u8 = 0;
    let mut v_res_2921_: *mut LeanObject = core::ptr::null_mut();
    v___y_657__boxed_2920_ = (lean_unbox(v___y_2913_) as u8);
    v_res_2921_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0(
        v_t_2909_,
        v___y_2910_,
        v___y_2911_,
        v___y_2912_,
        v___y_657__boxed_2920_,
        v___y_2914_,
        v___y_2915_,
        v___y_2916_,
        v___y_2917_,
        v___y_2918_,
    );
    lean_dec(v___y_2918_);
    lean_dec_ref(v___y_2917_);
    lean_dec(v___y_2916_);
    lean_dec_ref(v___y_2915_);
    lean_dec(v___y_2914_);
    lean_dec_ref(v___y_2912_);
    lean_dec(v___y_2911_);
    lean_dec(v___y_2910_);
    return v_res_2921_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(
    mut v_t_2922_: *mut LeanObject,
    mut v_a_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
    mut v_a_2925_: *mut LeanObject,
    mut v_a_2926_: u8,
    mut v_a_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    v___f_2933_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        11,
        1,
    );
    lean_closure_set(v___f_2933_, 0, v_t_2922_);
    v___x_2934_ = l_Lean_Elab_Tactic_Omega_commitWhen___redArg(
        v___f_2933_,
        v_a_2923_,
        v_a_2924_,
        v_a_2925_,
        v_a_2926_,
        v_a_2927_,
        v_a_2928_,
        v_a_2929_,
        v_a_2930_,
        v_a_2931_,
    );
    return v___x_2934_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg___boxed(
    mut v_t_2935_: *mut LeanObject,
    mut v_a_2936_: *mut LeanObject,
    mut v_a_2937_: *mut LeanObject,
    mut v_a_2938_: *mut LeanObject,
    mut v_a_2939_: *mut LeanObject,
    mut v_a_2940_: *mut LeanObject,
    mut v_a_2941_: *mut LeanObject,
    mut v_a_2942_: *mut LeanObject,
    mut v_a_2943_: *mut LeanObject,
    mut v_a_2944_: *mut LeanObject,
    mut v_a_2945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2946_: u8 = 0;
    let mut v_res_2947_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2946_ = (lean_unbox(v_a_2939_) as u8);
    v_res_2947_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(
        v_t_2935_,
        v_a_2936_,
        v_a_2937_,
        v_a_2938_,
        v_a_boxed_2946_,
        v_a_2940_,
        v_a_2941_,
        v_a_2942_,
        v_a_2943_,
        v_a_2944_,
    );
    lean_dec(v_a_2944_);
    lean_dec_ref(v_a_2943_);
    lean_dec(v_a_2942_);
    lean_dec_ref(v_a_2941_);
    lean_dec(v_a_2940_);
    lean_dec_ref(v_a_2938_);
    lean_dec(v_a_2937_);
    lean_dec(v_a_2936_);
    return v_res_2947_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState(
    mut v_00_u03b1_2948_: *mut LeanObject,
    mut v_t_2949_: *mut LeanObject,
    mut v_a_2950_: *mut LeanObject,
    mut v_a_2951_: *mut LeanObject,
    mut v_a_2952_: *mut LeanObject,
    mut v_a_2953_: u8,
    mut v_a_2954_: *mut LeanObject,
    mut v_a_2955_: *mut LeanObject,
    mut v_a_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
    mut v_a_2958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    v___x_2960_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState___redArg(
        v_t_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_,
        v_a_2957_, v_a_2958_,
    );
    return v___x_2960_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_withoutModifyingState___boxed(
    mut v_00_u03b1_2961_: *mut LeanObject,
    mut v_t_2962_: *mut LeanObject,
    mut v_a_2963_: *mut LeanObject,
    mut v_a_2964_: *mut LeanObject,
    mut v_a_2965_: *mut LeanObject,
    mut v_a_2966_: *mut LeanObject,
    mut v_a_2967_: *mut LeanObject,
    mut v_a_2968_: *mut LeanObject,
    mut v_a_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
    mut v_a_2971_: *mut LeanObject,
    mut v_a_2972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2973_: u8 = 0;
    let mut v_res_2974_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2973_ = (lean_unbox(v_a_2966_) as u8);
    v_res_2974_ = l_Lean_Elab_Tactic_Omega_withoutModifyingState(
        v_00_u03b1_2961_,
        v_t_2962_,
        v_a_2963_,
        v_a_2964_,
        v_a_2965_,
        v_a_boxed_2973_,
        v_a_2967_,
        v_a_2968_,
        v_a_2969_,
        v_a_2970_,
        v_a_2971_,
    );
    lean_dec(v_a_2971_);
    lean_dec_ref(v_a_2970_);
    lean_dec(v_a_2969_);
    lean_dec_ref(v_a_2968_);
    lean_dec(v_a_2967_);
    lean_dec_ref(v_a_2965_);
    lean_dec(v_a_2964_);
    lean_dec(v_a_2963_);
    return v_res_2974_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_natCast_x3f(
    mut v_n_2977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2979_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_n_2977_);
    v___x_2978_ = l_Lean_Expr_getAppFnArgs(v_n_2977_);
    v_fst_2979_ = lean_ctor_get(v___x_2978_, 0);
    lean_inc(v_fst_2979_);
    if lean_obj_tag(v_fst_2979_) == 1 {
        let mut v_pre_2980_: *mut LeanObject = core::ptr::null_mut();
        v_pre_2980_ = lean_ctor_get(v_fst_2979_, 0);
        lean_inc(v_pre_2980_);
        if lean_obj_tag(v_pre_2980_) == 1 {
            let mut v_pre_2981_: *mut LeanObject = core::ptr::null_mut();
            v_pre_2981_ = lean_ctor_get(v_pre_2980_, 0);
            if lean_obj_tag(v_pre_2981_) == 0 {
                let mut v_snd_2982_: *mut LeanObject = core::ptr::null_mut();
                let mut v_str_2983_: *mut LeanObject = core::ptr::null_mut();
                let mut v_str_2984_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_2986_: u8 = 0;
                v_snd_2982_ = lean_ctor_get(v___x_2978_, 1);
                lean_inc(v_snd_2982_);
                lean_dec_ref(v___x_2978_);
                v_str_2983_ = lean_ctor_get(v_fst_2979_, 1);
                lean_inc_ref(v_str_2983_);
                lean_dec_ref_known(v_fst_2979_, 2);
                v_str_2984_ = lean_ctor_get(v_pre_2980_, 1);
                lean_inc_ref(v_str_2984_);
                lean_dec_ref_known(v_pre_2980_, 2);
                v___x_2985_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                v___x_2986_ = lean_string_dec_eq(v_str_2984_, v___x_2985_);
                lean_dec_ref(v_str_2984_);
                if v___x_2986_ == 0 {
                    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
                    lean_dec_ref(v_str_2983_);
                    lean_dec(v_snd_2982_);
                    v___x_2987_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                    return v___x_2987_;
                } else {
                    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_2989_: u8 = 0;
                    v___x_2988_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                    v___x_2989_ = lean_string_dec_eq(v_str_2983_, v___x_2988_);
                    lean_dec_ref(v_str_2983_);
                    if v___x_2989_ == 0 {
                        let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
                        lean_dec(v_snd_2982_);
                        v___x_2990_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                        return v___x_2990_;
                    } else {
                        let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_2993_: u8 = 0;
                        v___x_2991_ = lean_array_get_size(v_snd_2982_);
                        v___x_2992_ = lean_unsigned_to_nat(3);
                        v___x_2993_ = lean_nat_dec_eq(v___x_2991_, v___x_2992_);
                        if v___x_2993_ == 0 {
                            let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec(v_snd_2982_);
                            v___x_2994_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                            return v___x_2994_;
                        } else {
                            let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
                            lean_dec_ref(v_n_2977_);
                            v___x_2995_ = lean_unsigned_to_nat(2);
                            v___x_2996_ = lean_array_fget(v_snd_2982_, v___x_2995_);
                            lean_dec(v_snd_2982_);
                            v___x_2997_ = l_Lean_Expr_nat_x3f(v___x_2996_);
                            return v___x_2997_;
                        }
                    }
                }
            } else {
                let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v_pre_2980_, 2);
                lean_dec_ref_known(v_fst_2979_, 2);
                lean_dec_ref(v___x_2978_);
                v___x_2998_ = l_Lean_Expr_nat_x3f(v_n_2977_);
                return v___x_2998_;
            }
        } else {
            let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_pre_2980_);
            lean_dec_ref_known(v_fst_2979_, 2);
            lean_dec_ref(v___x_2978_);
            v___x_2999_ = l_Lean_Expr_nat_x3f(v_n_2977_);
            return v___x_2999_;
        }
    } else {
        let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_fst_2979_);
        lean_dec_ref(v___x_2978_);
        v___x_3000_ = l_Lean_Expr_nat_x3f(v_n_2977_);
        return v___x_3000_;
    }
}
pub unsafe fn l_Nat_cast___at___00Lean_Elab_Tactic_Omega_intCast_x3f_spec__0(
    mut v_a_3001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    v___x_3002_ = lean_nat_to_int(v_a_3001_);
    return v___x_3002_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_intCast_x3f(
    mut v_n_3003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: u8 = 0;
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3028_: u8 = 0;
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_n_3003_);
                v___x_3004_ = l_Lean_Expr_getAppFnArgs(v_n_3003_);
                v_fst_3005_ = lean_ctor_get(v___x_3004_, 0);
                lean_inc(v_fst_3005_);
                if lean_obj_tag(v_fst_3005_) == 1 {
                    v_pre_3006_ = lean_ctor_get(v_fst_3005_, 0);
                    lean_inc(v_pre_3006_);
                    if lean_obj_tag(v_pre_3006_) == 1 {
                        v_pre_3007_ = lean_ctor_get(v_pre_3006_, 0);
                        if lean_obj_tag(v_pre_3007_) == 0 {
                            v_snd_3008_ = lean_ctor_get(v___x_3004_, 1);
                            lean_inc(v_snd_3008_);
                            lean_dec_ref(v___x_3004_);
                            v_str_3009_ = lean_ctor_get(v_fst_3005_, 1);
                            lean_inc_ref(v_str_3009_);
                            lean_dec_ref_known(v_fst_3005_, 2);
                            v_str_3010_ = lean_ctor_get(v_pre_3006_, 1);
                            lean_inc_ref(v_str_3010_);
                            lean_dec_ref_known(v_pre_3006_, 2);
                            v___x_3011_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                            v___x_3012_ = lean_string_dec_eq(v_str_3010_, v___x_3011_);
                            lean_dec_ref(v_str_3010_);
                            if v___x_3012_ == 0 {
                                lean_dec_ref(v_str_3009_);
                                lean_dec(v_snd_3008_);
                                v___x_3013_ = l_Lean_Expr_int_x3f(v_n_3003_);
                                return v___x_3013_;
                            } else {
                                v___x_3014_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                                v___x_3015_ = lean_string_dec_eq(v_str_3009_, v___x_3014_);
                                lean_dec_ref(v_str_3009_);
                                if v___x_3015_ == 0 {
                                    lean_dec(v_snd_3008_);
                                    v___x_3016_ = l_Lean_Expr_int_x3f(v_n_3003_);
                                    return v___x_3016_;
                                } else {
                                    v___x_3017_ = lean_array_get_size(v_snd_3008_);
                                    v___x_3018_ = lean_unsigned_to_nat(3);
                                    v___x_3019_ = lean_nat_dec_eq(v___x_3017_, v___x_3018_);
                                    if v___x_3019_ == 0 {
                                        lean_dec(v_snd_3008_);
                                        v___x_3020_ = l_Lean_Expr_int_x3f(v_n_3003_);
                                        return v___x_3020_;
                                    } else {
                                        lean_dec_ref(v_n_3003_);
                                        v___x_3021_ = lean_unsigned_to_nat(2);
                                        v___x_3022_ = lean_array_fget(v_snd_3008_, v___x_3021_);
                                        lean_dec(v_snd_3008_);
                                        v___x_3023_ = l_Lean_Expr_nat_x3f(v___x_3022_);
                                        if lean_obj_tag(v___x_3023_) == 0 {
                                            v___x_3024_ = lean_box(0);
                                            return v___x_3024_;
                                        } else {
                                            v_val_3025_ = lean_ctor_get(v___x_3023_, 0);
                                            v_isSharedCheck_3033_ =
                                                (!lean_is_exclusive(v___x_3023_)) as u8;
                                            if v_isSharedCheck_3033_ == 0 {
                                                v___x_3027_ = v___x_3023_;
                                                v_isShared_3028_ = v_isSharedCheck_3033_;
                                                state = 1;
                                                continue;
                                            } else {
                                                lean_inc(v_val_3025_);
                                                lean_dec(v___x_3023_);
                                                v___x_3027_ = lean_box(0);
                                                v_isShared_3028_ = v_isSharedCheck_3033_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_pre_3006_, 2);
                            lean_dec_ref_known(v_fst_3005_, 2);
                            lean_dec_ref(v___x_3004_);
                            v___x_3034_ = l_Lean_Expr_int_x3f(v_n_3003_);
                            return v___x_3034_;
                        }
                    } else {
                        lean_dec(v_pre_3006_);
                        lean_dec_ref_known(v_fst_3005_, 2);
                        lean_dec_ref(v___x_3004_);
                        v___x_3035_ = l_Lean_Expr_int_x3f(v_n_3003_);
                        return v___x_3035_;
                    }
                } else {
                    lean_dec(v_fst_3005_);
                    lean_dec_ref(v___x_3004_);
                    v___x_3036_ = l_Lean_Expr_int_x3f(v_n_3003_);
                    return v___x_3036_;
                }
            }
            1 => {
                v___x_3029_ = lean_nat_to_int(v_val_3025_);
                if v_isShared_3028_ == 0 {
                    lean_ctor_set(v___x_3027_, 0, v___x_3029_);
                    v___x_3031_ = v___x_3027_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
                    v___x_3031_ = v_reuseFailAlloc_3032_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3031_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_groundNat_x3f(
    mut v_e_3052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: u8 = 0;
    let mut v___x_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: u8 = 0;
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: u8 = 0;
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: u8 = 0;
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: u8 = 0;
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: u8 = 0;
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: u8 = 0;
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: u8 = 0;
    let mut v___x_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: u8 = 0;
    let mut v___x_3101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: u8 = 0;
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: u8 = 0;
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: u8 = 0;
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: u8 = 0;
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: u8 = 0;
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: u8 = 0;
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: u8 = 0;
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3052_);
                v___x_3053_ = l_Lean_Expr_getAppFnArgs(v_e_3052_);
                v_fst_3054_ = lean_ctor_get(v___x_3053_, 0);
                lean_inc(v_fst_3054_);
                if lean_obj_tag(v_fst_3054_) == 1 {
                    v_pre_3055_ = lean_ctor_get(v_fst_3054_, 0);
                    lean_inc(v_pre_3055_);
                    if lean_obj_tag(v_pre_3055_) == 1 {
                        v_pre_3056_ = lean_ctor_get(v_pre_3055_, 0);
                        if lean_obj_tag(v_pre_3056_) == 0 {
                            v_snd_3057_ = lean_ctor_get(v___x_3053_, 1);
                            lean_inc(v_snd_3057_);
                            lean_dec_ref(v___x_3053_);
                            v_str_3058_ = lean_ctor_get(v_fst_3054_, 1);
                            lean_inc_ref(v_str_3058_);
                            lean_dec_ref_known(v_fst_3054_, 2);
                            v_str_3059_ = lean_ctor_get(v_pre_3055_, 1);
                            lean_inc_ref(v_str_3059_);
                            lean_dec_ref_known(v_pre_3055_, 2);
                            v___x_3060_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                            v___x_3061_ = lean_string_dec_eq(v_str_3059_, v___x_3060_);
                            if v___x_3061_ == 0 {
                                v___x_3062_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0;
                                v___x_3063_ = lean_string_dec_eq(v_str_3059_, v___x_3062_);
                                if v___x_3063_ == 0 {
                                    v___x_3064_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
                                    v___x_3065_ = lean_string_dec_eq(v_str_3059_, v___x_3064_);
                                    if v___x_3065_ == 0 {
                                        v___x_3066_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
                                        v___x_3067_ = lean_string_dec_eq(v_str_3059_, v___x_3066_);
                                        if v___x_3067_ == 0 {
                                            v___x_3068_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
                                            v___x_3069_ =
                                                lean_string_dec_eq(v_str_3059_, v___x_3068_);
                                            if v___x_3069_ == 0 {
                                                v___x_3070_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
                                                v___x_3071_ =
                                                    lean_string_dec_eq(v_str_3059_, v___x_3070_);
                                                lean_dec_ref(v_str_3059_);
                                                if v___x_3071_ == 0 {
                                                    lean_dec_ref(v_str_3058_);
                                                    lean_dec(v_snd_3057_);
                                                    v___x_3072_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                    return v___x_3072_;
                                                } else {
                                                    v___x_3073_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                                                    v___x_3074_ = lean_string_dec_eq(
                                                        v_str_3058_,
                                                        v___x_3073_,
                                                    );
                                                    lean_dec_ref(v_str_3058_);
                                                    if v___x_3074_ == 0 {
                                                        lean_dec(v_snd_3057_);
                                                        v___x_3075_ =
                                                            l_Lean_Expr_nat_x3f(v_e_3052_);
                                                        return v___x_3075_;
                                                    } else {
                                                        v___x_3076_ =
                                                            lean_array_get_size(v_snd_3057_);
                                                        v___x_3077_ = lean_unsigned_to_nat(6);
                                                        v___x_3078_ = lean_nat_dec_eq(
                                                            v___x_3076_,
                                                            v___x_3077_,
                                                        );
                                                        if v___x_3078_ == 0 {
                                                            lean_dec(v_snd_3057_);
                                                            v___x_3079_ =
                                                                l_Lean_Expr_nat_x3f(v_e_3052_);
                                                            return v___x_3079_;
                                                        } else {
                                                            lean_dec_ref(v_e_3052_);
                                                            v___f_3080_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__6;
                                                            v___x_3081_ = lean_unsigned_to_nat(4);
                                                            v___x_3082_ = lean_array_fget(
                                                                v_snd_3057_,
                                                                v___x_3081_,
                                                            );
                                                            v___x_3083_ = lean_unsigned_to_nat(5);
                                                            v___x_3084_ = lean_array_fget(
                                                                v_snd_3057_,
                                                                v___x_3083_,
                                                            );
                                                            lean_dec(v_snd_3057_);
                                                            v___x_3085_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3080_, v___x_3082_, v___x_3084_);
                                                            return v___x_3085_;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_str_3059_);
                                                v___x_3086_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
                                                v___x_3087_ =
                                                    lean_string_dec_eq(v_str_3058_, v___x_3086_);
                                                lean_dec_ref(v_str_3058_);
                                                if v___x_3087_ == 0 {
                                                    lean_dec(v_snd_3057_);
                                                    v___x_3088_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                    return v___x_3088_;
                                                } else {
                                                    v___x_3089_ = lean_array_get_size(v_snd_3057_);
                                                    v___x_3090_ = lean_unsigned_to_nat(6);
                                                    v___x_3091_ =
                                                        lean_nat_dec_eq(v___x_3089_, v___x_3090_);
                                                    if v___x_3091_ == 0 {
                                                        lean_dec(v_snd_3057_);
                                                        v___x_3092_ =
                                                            l_Lean_Expr_nat_x3f(v_e_3052_);
                                                        return v___x_3092_;
                                                    } else {
                                                        lean_dec_ref(v_e_3052_);
                                                        v___f_3093_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__8;
                                                        v___x_3094_ = lean_unsigned_to_nat(4);
                                                        v___x_3095_ = lean_array_fget(
                                                            v_snd_3057_,
                                                            v___x_3094_,
                                                        );
                                                        v___x_3096_ = lean_unsigned_to_nat(5);
                                                        v___x_3097_ = lean_array_fget(
                                                            v_snd_3057_,
                                                            v___x_3096_,
                                                        );
                                                        lean_dec(v_snd_3057_);
                                                        v___x_3098_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3093_, v___x_3095_, v___x_3097_);
                                                        return v___x_3098_;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v_str_3059_);
                                            v___x_3099_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
                                            v___x_3100_ =
                                                lean_string_dec_eq(v_str_3058_, v___x_3099_);
                                            lean_dec_ref(v_str_3058_);
                                            if v___x_3100_ == 0 {
                                                lean_dec(v_snd_3057_);
                                                v___x_3101_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                return v___x_3101_;
                                            } else {
                                                v___x_3102_ = lean_array_get_size(v_snd_3057_);
                                                v___x_3103_ = lean_unsigned_to_nat(6);
                                                v___x_3104_ =
                                                    lean_nat_dec_eq(v___x_3102_, v___x_3103_);
                                                if v___x_3104_ == 0 {
                                                    lean_dec(v_snd_3057_);
                                                    v___x_3105_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                    return v___x_3105_;
                                                } else {
                                                    lean_dec_ref(v_e_3052_);
                                                    v___f_3106_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__10;
                                                    v___x_3107_ = lean_unsigned_to_nat(4);
                                                    v___x_3108_ =
                                                        lean_array_fget(v_snd_3057_, v___x_3107_);
                                                    v___x_3109_ = lean_unsigned_to_nat(5);
                                                    v___x_3110_ =
                                                        lean_array_fget(v_snd_3057_, v___x_3109_);
                                                    lean_dec(v_snd_3057_);
                                                    v___x_3111_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3106_, v___x_3108_, v___x_3110_);
                                                    return v___x_3111_;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_str_3059_);
                                        v___x_3112_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11;
                                        v___x_3113_ = lean_string_dec_eq(v_str_3058_, v___x_3112_);
                                        lean_dec_ref(v_str_3058_);
                                        if v___x_3113_ == 0 {
                                            lean_dec(v_snd_3057_);
                                            v___x_3114_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                            return v___x_3114_;
                                        } else {
                                            v___x_3115_ = lean_array_get_size(v_snd_3057_);
                                            v___x_3116_ = lean_unsigned_to_nat(6);
                                            v___x_3117_ = lean_nat_dec_eq(v___x_3115_, v___x_3116_);
                                            if v___x_3117_ == 0 {
                                                lean_dec(v_snd_3057_);
                                                v___x_3118_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                                return v___x_3118_;
                                            } else {
                                                lean_dec_ref(v_e_3052_);
                                                v___f_3119_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__12;
                                                v___x_3120_ = lean_unsigned_to_nat(4);
                                                v___x_3121_ =
                                                    lean_array_fget(v_snd_3057_, v___x_3120_);
                                                v___x_3122_ = lean_unsigned_to_nat(5);
                                                v___x_3123_ =
                                                    lean_array_fget(v_snd_3057_, v___x_3122_);
                                                lean_dec(v_snd_3057_);
                                                v___x_3124_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3119_, v___x_3121_, v___x_3123_);
                                                return v___x_3124_;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_str_3059_);
                                    v___x_3125_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13;
                                    v___x_3126_ = lean_string_dec_eq(v_str_3058_, v___x_3125_);
                                    lean_dec_ref(v_str_3058_);
                                    if v___x_3126_ == 0 {
                                        lean_dec(v_snd_3057_);
                                        v___x_3127_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                        return v___x_3127_;
                                    } else {
                                        v___x_3128_ = lean_array_get_size(v_snd_3057_);
                                        v___x_3129_ = lean_unsigned_to_nat(6);
                                        v___x_3130_ = lean_nat_dec_eq(v___x_3128_, v___x_3129_);
                                        if v___x_3130_ == 0 {
                                            lean_dec(v_snd_3057_);
                                            v___x_3131_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                            return v___x_3131_;
                                        } else {
                                            lean_dec_ref(v_e_3052_);
                                            v___f_3132_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__14;
                                            v___x_3133_ = lean_unsigned_to_nat(4);
                                            v___x_3134_ = lean_array_fget(v_snd_3057_, v___x_3133_);
                                            v___x_3135_ = lean_unsigned_to_nat(5);
                                            v___x_3136_ = lean_array_fget(v_snd_3057_, v___x_3135_);
                                            lean_dec(v_snd_3057_);
                                            v___x_3137_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(v___f_3132_, v___x_3134_, v___x_3136_);
                                            return v___x_3137_;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_str_3059_);
                                v___x_3138_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                                v___x_3139_ = lean_string_dec_eq(v_str_3058_, v___x_3138_);
                                lean_dec_ref(v_str_3058_);
                                if v___x_3139_ == 0 {
                                    lean_dec(v_snd_3057_);
                                    v___x_3140_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                    return v___x_3140_;
                                } else {
                                    v___x_3141_ = lean_array_get_size(v_snd_3057_);
                                    v___x_3142_ = lean_unsigned_to_nat(3);
                                    v___x_3143_ = lean_nat_dec_eq(v___x_3141_, v___x_3142_);
                                    if v___x_3143_ == 0 {
                                        lean_dec(v_snd_3057_);
                                        v___x_3144_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                                        return v___x_3144_;
                                    } else {
                                        lean_dec_ref(v_e_3052_);
                                        v___x_3145_ = lean_unsigned_to_nat(2);
                                        v___x_3146_ = lean_array_fget(v_snd_3057_, v___x_3145_);
                                        lean_dec(v_snd_3057_);
                                        v_e_3052_ = v___x_3146_;
                                        state = 0;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_pre_3055_, 2);
                            lean_dec_ref_known(v_fst_3054_, 2);
                            lean_dec_ref(v___x_3053_);
                            v___x_3148_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                            return v___x_3148_;
                        }
                    } else {
                        lean_dec_ref_known(v_fst_3054_, 2);
                        lean_dec(v_pre_3055_);
                        lean_dec_ref(v___x_3053_);
                        v___x_3149_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                        return v___x_3149_;
                    }
                } else {
                    lean_dec(v_fst_3054_);
                    lean_dec_ref(v___x_3053_);
                    v___x_3150_ = l_Lean_Expr_nat_x3f(v_e_3052_);
                    return v___x_3150_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundNat_x3f_op(
    mut v_f_3151_: *mut LeanObject,
    mut v_x_3152_: *mut LeanObject,
    mut v_y_3153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3160_: u8 = 0;
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3165_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3154_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_x_3152_);
                if lean_obj_tag(v___x_3154_) == 1 {
                    v_val_3155_ = lean_ctor_get(v___x_3154_, 0);
                    lean_inc(v_val_3155_);
                    lean_dec_ref_known(v___x_3154_, 1);
                    v___x_3156_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v_y_3153_);
                    if lean_obj_tag(v___x_3156_) == 1 {
                        v_val_3157_ = lean_ctor_get(v___x_3156_, 0);
                        v_isSharedCheck_3165_ = (!lean_is_exclusive(v___x_3156_)) as u8;
                        if v_isSharedCheck_3165_ == 0 {
                            v___x_3159_ = v___x_3156_;
                            v_isShared_3160_ = v_isSharedCheck_3165_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_3157_);
                            lean_dec(v___x_3156_);
                            v___x_3159_ = lean_box(0);
                            v_isShared_3160_ = v_isSharedCheck_3165_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3156_);
                        lean_dec(v_val_3155_);
                        lean_dec_ref(v_f_3151_);
                        v___x_3166_ = lean_box(0);
                        return v___x_3166_;
                    }
                } else {
                    lean_dec(v___x_3154_);
                    lean_dec_ref(v_y_3153_);
                    lean_dec_ref(v_f_3151_);
                    v___x_3167_ = lean_box(0);
                    return v___x_3167_;
                }
            }
            1 => {
                v___x_3161_ = lean_apply_2(v_f_3151_, v_val_3155_, v_val_3157_);
                if v_isShared_3160_ == 0 {
                    lean_ctor_set(v___x_3159_, 0, v___x_3161_);
                    v___x_3163_ = v___x_3159_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3164_, 0, v___x_3161_);
                    v___x_3163_ = v_reuseFailAlloc_3164_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_groundInt_x3f(
    mut v_e_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: u8 = 0;
    let mut v___x_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: u8 = 0;
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: u8 = 0;
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: u8 = 0;
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: u8 = 0;
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: u8 = 0;
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3215_: u8 = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: u8 = 0;
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: u8 = 0;
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: u8 = 0;
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: u8 = 0;
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: u8 = 0;
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3284_: u8 = 0;
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3289_: u8 = 0;
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3172_);
                v___x_3173_ = l_Lean_Expr_getAppFnArgs(v_e_3172_);
                v_fst_3174_ = lean_ctor_get(v___x_3173_, 0);
                lean_inc(v_fst_3174_);
                if lean_obj_tag(v_fst_3174_) == 1 {
                    v_pre_3175_ = lean_ctor_get(v_fst_3174_, 0);
                    lean_inc(v_pre_3175_);
                    if lean_obj_tag(v_pre_3175_) == 1 {
                        v_pre_3176_ = lean_ctor_get(v_pre_3175_, 0);
                        if lean_obj_tag(v_pre_3176_) == 0 {
                            v_snd_3177_ = lean_ctor_get(v___x_3173_, 1);
                            lean_inc(v_snd_3177_);
                            lean_dec_ref(v___x_3173_);
                            v_str_3178_ = lean_ctor_get(v_fst_3174_, 1);
                            lean_inc_ref(v_str_3178_);
                            lean_dec_ref_known(v_fst_3174_, 2);
                            v_str_3179_ = lean_ctor_get(v_pre_3175_, 1);
                            lean_inc_ref(v_str_3179_);
                            lean_dec_ref_known(v_pre_3175_, 2);
                            v___x_3180_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                            v___x_3181_ = lean_string_dec_eq(v_str_3179_, v___x_3180_);
                            if v___x_3181_ == 0 {
                                v___x_3182_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__0;
                                v___x_3183_ = lean_string_dec_eq(v_str_3179_, v___x_3182_);
                                if v___x_3183_ == 0 {
                                    v___x_3184_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__1;
                                    v___x_3185_ = lean_string_dec_eq(v_str_3179_, v___x_3184_);
                                    if v___x_3185_ == 0 {
                                        v___x_3186_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
                                        v___x_3187_ = lean_string_dec_eq(v_str_3179_, v___x_3186_);
                                        if v___x_3187_ == 0 {
                                            v___x_3188_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
                                            v___x_3189_ =
                                                lean_string_dec_eq(v_str_3179_, v___x_3188_);
                                            if v___x_3189_ == 0 {
                                                v___x_3190_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
                                                v___x_3191_ =
                                                    lean_string_dec_eq(v_str_3179_, v___x_3190_);
                                                lean_dec_ref(v_str_3179_);
                                                if v___x_3191_ == 0 {
                                                    lean_dec_ref(v_str_3178_);
                                                    lean_dec(v_snd_3177_);
                                                    v___x_3192_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                    return v___x_3192_;
                                                } else {
                                                    v___x_3193_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                                                    v___x_3194_ = lean_string_dec_eq(
                                                        v_str_3178_,
                                                        v___x_3193_,
                                                    );
                                                    lean_dec_ref(v_str_3178_);
                                                    if v___x_3194_ == 0 {
                                                        lean_dec(v_snd_3177_);
                                                        v___x_3195_ =
                                                            l_Lean_Expr_int_x3f(v_e_3172_);
                                                        return v___x_3195_;
                                                    } else {
                                                        v___x_3196_ =
                                                            lean_array_get_size(v_snd_3177_);
                                                        v___x_3197_ = lean_unsigned_to_nat(6);
                                                        v___x_3198_ = lean_nat_dec_eq(
                                                            v___x_3196_,
                                                            v___x_3197_,
                                                        );
                                                        if v___x_3198_ == 0 {
                                                            lean_dec(v_snd_3177_);
                                                            v___x_3199_ =
                                                                l_Lean_Expr_int_x3f(v_e_3172_);
                                                            return v___x_3199_;
                                                        } else {
                                                            lean_dec_ref(v_e_3172_);
                                                            v___x_3200_ = lean_unsigned_to_nat(4);
                                                            v___x_3201_ = lean_array_fget_borrowed(
                                                                v_snd_3177_,
                                                                v___x_3200_,
                                                            );
                                                            lean_inc(v___x_3201_);
                                                            v___x_3202_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v___x_3201_);
                                                            if lean_obj_tag(v___x_3202_) == 1 {
                                                                v_val_3203_ =
                                                                    lean_ctor_get(v___x_3202_, 0);
                                                                lean_inc(v_val_3203_);
                                                                lean_dec_ref_known(v___x_3202_, 1);
                                                                v___x_3204_ =
                                                                    lean_unsigned_to_nat(5);
                                                                v___x_3205_ = lean_array_fget(
                                                                    v_snd_3177_,
                                                                    v___x_3204_,
                                                                );
                                                                lean_dec(v_snd_3177_);
                                                                v___x_3206_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_3205_);
                                                                if lean_obj_tag(v___x_3206_) == 1 {
                                                                    v_val_3207_ = lean_ctor_get(
                                                                        v___x_3206_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_3215_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_3206_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_3215_ == 0 {
                                                                        v___x_3209_ = v___x_3206_;
                                                                        v_isShared_3210_ =
                                                                            v_isSharedCheck_3215_;
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_val_3207_);
                                                                        lean_dec(v___x_3206_);
                                                                        v___x_3209_ = lean_box(0);
                                                                        v_isShared_3210_ =
                                                                            v_isSharedCheck_3215_;
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec(v___x_3206_);
                                                                    lean_dec(v_val_3203_);
                                                                    v___x_3216_ = lean_box(0);
                                                                    return v___x_3216_;
                                                                }
                                                            } else {
                                                                lean_dec(v___x_3202_);
                                                                lean_dec(v_snd_3177_);
                                                                v___x_3217_ = lean_box(0);
                                                                return v___x_3217_;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_str_3179_);
                                                v___x_3218_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
                                                v___x_3219_ =
                                                    lean_string_dec_eq(v_str_3178_, v___x_3218_);
                                                lean_dec_ref(v_str_3178_);
                                                if v___x_3219_ == 0 {
                                                    lean_dec(v_snd_3177_);
                                                    v___x_3220_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                    return v___x_3220_;
                                                } else {
                                                    v___x_3221_ = lean_array_get_size(v_snd_3177_);
                                                    v___x_3222_ = lean_unsigned_to_nat(6);
                                                    v___x_3223_ =
                                                        lean_nat_dec_eq(v___x_3221_, v___x_3222_);
                                                    if v___x_3223_ == 0 {
                                                        lean_dec(v_snd_3177_);
                                                        v___x_3224_ =
                                                            l_Lean_Expr_int_x3f(v_e_3172_);
                                                        return v___x_3224_;
                                                    } else {
                                                        lean_dec_ref(v_e_3172_);
                                                        v___f_3225_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__0;
                                                        v___x_3226_ = lean_unsigned_to_nat(4);
                                                        v___x_3227_ = lean_array_fget(
                                                            v_snd_3177_,
                                                            v___x_3226_,
                                                        );
                                                        v___x_3228_ = lean_unsigned_to_nat(5);
                                                        v___x_3229_ = lean_array_fget(
                                                            v_snd_3177_,
                                                            v___x_3228_,
                                                        );
                                                        lean_dec(v_snd_3177_);
                                                        v___x_3230_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3225_, v___x_3227_, v___x_3229_);
                                                        return v___x_3230_;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v_str_3179_);
                                            v___x_3231_ =
                                                l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
                                            v___x_3232_ =
                                                lean_string_dec_eq(v_str_3178_, v___x_3231_);
                                            lean_dec_ref(v_str_3178_);
                                            if v___x_3232_ == 0 {
                                                lean_dec(v_snd_3177_);
                                                v___x_3233_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                return v___x_3233_;
                                            } else {
                                                v___x_3234_ = lean_array_get_size(v_snd_3177_);
                                                v___x_3235_ = lean_unsigned_to_nat(6);
                                                v___x_3236_ =
                                                    lean_nat_dec_eq(v___x_3234_, v___x_3235_);
                                                if v___x_3236_ == 0 {
                                                    lean_dec(v_snd_3177_);
                                                    v___x_3237_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                    return v___x_3237_;
                                                } else {
                                                    lean_dec_ref(v_e_3172_);
                                                    v___f_3238_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__1;
                                                    v___x_3239_ = lean_unsigned_to_nat(4);
                                                    v___x_3240_ =
                                                        lean_array_fget(v_snd_3177_, v___x_3239_);
                                                    v___x_3241_ = lean_unsigned_to_nat(5);
                                                    v___x_3242_ =
                                                        lean_array_fget(v_snd_3177_, v___x_3241_);
                                                    lean_dec(v_snd_3177_);
                                                    v___x_3243_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3238_, v___x_3240_, v___x_3242_);
                                                    return v___x_3243_;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_str_3179_);
                                        v___x_3244_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__11;
                                        v___x_3245_ = lean_string_dec_eq(v_str_3178_, v___x_3244_);
                                        lean_dec_ref(v_str_3178_);
                                        if v___x_3245_ == 0 {
                                            lean_dec(v_snd_3177_);
                                            v___x_3246_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                            return v___x_3246_;
                                        } else {
                                            v___x_3247_ = lean_array_get_size(v_snd_3177_);
                                            v___x_3248_ = lean_unsigned_to_nat(6);
                                            v___x_3249_ = lean_nat_dec_eq(v___x_3247_, v___x_3248_);
                                            if v___x_3249_ == 0 {
                                                lean_dec(v_snd_3177_);
                                                v___x_3250_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                                return v___x_3250_;
                                            } else {
                                                lean_dec_ref(v_e_3172_);
                                                v___f_3251_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__2;
                                                v___x_3252_ = lean_unsigned_to_nat(4);
                                                v___x_3253_ =
                                                    lean_array_fget(v_snd_3177_, v___x_3252_);
                                                v___x_3254_ = lean_unsigned_to_nat(5);
                                                v___x_3255_ =
                                                    lean_array_fget(v_snd_3177_, v___x_3254_);
                                                lean_dec(v_snd_3177_);
                                                v___x_3256_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3251_, v___x_3253_, v___x_3255_);
                                                return v___x_3256_;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v_str_3179_);
                                    v___x_3257_ =
                                        l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__13;
                                    v___x_3258_ = lean_string_dec_eq(v_str_3178_, v___x_3257_);
                                    lean_dec_ref(v_str_3178_);
                                    if v___x_3258_ == 0 {
                                        lean_dec(v_snd_3177_);
                                        v___x_3259_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                        return v___x_3259_;
                                    } else {
                                        v___x_3260_ = lean_array_get_size(v_snd_3177_);
                                        v___x_3261_ = lean_unsigned_to_nat(6);
                                        v___x_3262_ = lean_nat_dec_eq(v___x_3260_, v___x_3261_);
                                        if v___x_3262_ == 0 {
                                            lean_dec(v_snd_3177_);
                                            v___x_3263_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                            return v___x_3263_;
                                        } else {
                                            lean_dec_ref(v_e_3172_);
                                            v___f_3264_ =
                                                l_Lean_Elab_Tactic_Omega_groundInt_x3f___closed__3;
                                            v___x_3265_ = lean_unsigned_to_nat(4);
                                            v___x_3266_ = lean_array_fget(v_snd_3177_, v___x_3265_);
                                            v___x_3267_ = lean_unsigned_to_nat(5);
                                            v___x_3268_ = lean_array_fget(v_snd_3177_, v___x_3267_);
                                            lean_dec(v_snd_3177_);
                                            v___x_3269_ = l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(v___f_3264_, v___x_3266_, v___x_3268_);
                                            return v___x_3269_;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_str_3179_);
                                v___x_3270_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                                v___x_3271_ = lean_string_dec_eq(v_str_3178_, v___x_3270_);
                                lean_dec_ref(v_str_3178_);
                                if v___x_3271_ == 0 {
                                    lean_dec(v_snd_3177_);
                                    v___x_3272_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                    return v___x_3272_;
                                } else {
                                    v___x_3273_ = lean_array_get_size(v_snd_3177_);
                                    v___x_3274_ = lean_unsigned_to_nat(3);
                                    v___x_3275_ = lean_nat_dec_eq(v___x_3273_, v___x_3274_);
                                    if v___x_3275_ == 0 {
                                        lean_dec(v_snd_3177_);
                                        v___x_3276_ = l_Lean_Expr_int_x3f(v_e_3172_);
                                        return v___x_3276_;
                                    } else {
                                        lean_dec_ref(v_e_3172_);
                                        v___x_3277_ = lean_unsigned_to_nat(2);
                                        v___x_3278_ = lean_array_fget(v_snd_3177_, v___x_3277_);
                                        lean_dec(v_snd_3177_);
                                        v___x_3279_ =
                                            l_Lean_Elab_Tactic_Omega_groundNat_x3f(v___x_3278_);
                                        if lean_obj_tag(v___x_3279_) == 0 {
                                            v___x_3280_ = lean_box(0);
                                            return v___x_3280_;
                                        } else {
                                            v_val_3281_ = lean_ctor_get(v___x_3279_, 0);
                                            v_isSharedCheck_3289_ =
                                                (!lean_is_exclusive(v___x_3279_)) as u8;
                                            if v_isSharedCheck_3289_ == 0 {
                                                v___x_3283_ = v___x_3279_;
                                                v_isShared_3284_ = v_isSharedCheck_3289_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_val_3281_);
                                                lean_dec(v___x_3279_);
                                                v___x_3283_ = lean_box(0);
                                                v_isShared_3284_ = v_isSharedCheck_3289_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_pre_3175_, 2);
                            lean_dec_ref_known(v_fst_3174_, 2);
                            lean_dec_ref(v___x_3173_);
                            v___x_3290_ = l_Lean_Expr_int_x3f(v_e_3172_);
                            return v___x_3290_;
                        }
                    } else {
                        lean_dec_ref_known(v_fst_3174_, 2);
                        lean_dec(v_pre_3175_);
                        lean_dec_ref(v___x_3173_);
                        v___x_3291_ = l_Lean_Expr_int_x3f(v_e_3172_);
                        return v___x_3291_;
                    }
                } else {
                    lean_dec(v_fst_3174_);
                    lean_dec_ref(v___x_3173_);
                    v___x_3292_ = l_Lean_Expr_int_x3f(v_e_3172_);
                    return v___x_3292_;
                }
            }
            1 => {
                v___x_3211_ = l_Int_pow(v_val_3203_, v_val_3207_);
                lean_dec(v_val_3207_);
                lean_dec(v_val_3203_);
                if v_isShared_3210_ == 0 {
                    lean_ctor_set(v___x_3209_, 0, v___x_3211_);
                    v___x_3213_ = v___x_3209_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
                    v___x_3213_ = v_reuseFailAlloc_3214_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3213_;
            }
            3 => {
                v___x_3285_ = lean_nat_to_int(v_val_3281_);
                if v_isShared_3284_ == 0 {
                    lean_ctor_set(v___x_3283_, 0, v___x_3285_);
                    v___x_3287_ = v___x_3283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
                    v___x_3287_ = v_reuseFailAlloc_3288_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3287_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Omega_OmegaM_0__Lean_Elab_Tactic_Omega_groundInt_x3f_op(
    mut v_f_3293_: *mut LeanObject,
    mut v_x_3294_: *mut LeanObject,
    mut v_y_3295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3302_: u8 = 0;
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3307_: u8 = 0;
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3296_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_x_3294_);
                if lean_obj_tag(v___x_3296_) == 1 {
                    v_val_3297_ = lean_ctor_get(v___x_3296_, 0);
                    lean_inc(v_val_3297_);
                    lean_dec_ref_known(v___x_3296_, 1);
                    v___x_3298_ = l_Lean_Elab_Tactic_Omega_groundInt_x3f(v_y_3295_);
                    if lean_obj_tag(v___x_3298_) == 1 {
                        v_val_3299_ = lean_ctor_get(v___x_3298_, 0);
                        v_isSharedCheck_3307_ = (!lean_is_exclusive(v___x_3298_)) as u8;
                        if v_isSharedCheck_3307_ == 0 {
                            v___x_3301_ = v___x_3298_;
                            v_isShared_3302_ = v_isSharedCheck_3307_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_3299_);
                            lean_dec(v___x_3298_);
                            v___x_3301_ = lean_box(0);
                            v_isShared_3302_ = v_isSharedCheck_3307_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3298_);
                        lean_dec(v_val_3297_);
                        lean_dec_ref(v_f_3293_);
                        v___x_3308_ = lean_box(0);
                        return v___x_3308_;
                    }
                } else {
                    lean_dec(v___x_3296_);
                    lean_dec_ref(v_y_3295_);
                    lean_dec_ref(v_f_3293_);
                    v___x_3309_ = lean_box(0);
                    return v___x_3309_;
                }
            }
            1 => {
                v___x_3303_ = lean_apply_2(v_f_3293_, v_val_3297_, v_val_3299_);
                if v_isShared_3302_ == 0 {
                    lean_ctor_set(v___x_3301_, 0, v___x_3303_);
                    v___x_3305_ = v___x_3301_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3306_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3306_, 0, v___x_3303_);
                    v___x_3305_ = v_reuseFailAlloc_3306_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(
    mut v_a_3310_: *mut LeanObject,
    mut v_b_3311_: *mut LeanObject,
    mut v_a_3312_: *mut LeanObject,
    mut v_a_3313_: *mut LeanObject,
    mut v_a_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3323_: u8 = 0;
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_a_3310_);
                v___x_3317_ =
                    l_Lean_Meta_mkEqRefl(v_a_3310_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
                if lean_obj_tag(v___x_3317_) == 0 {
                    v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
                    lean_inc(v_a_3318_);
                    lean_dec_ref_known(v___x_3317_, 1);
                    v___x_3319_ = l_Lean_Meta_mkEq(
                        v_a_3310_, v_b_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_,
                    );
                    if lean_obj_tag(v___x_3319_) == 0 {
                        v_a_3320_ = lean_ctor_get(v___x_3319_, 0);
                        v_isSharedCheck_3328_ = (!lean_is_exclusive(v___x_3319_)) as u8;
                        if v_isSharedCheck_3328_ == 0 {
                            v___x_3322_ = v___x_3319_;
                            v_isShared_3323_ = v_isSharedCheck_3328_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3320_);
                            lean_dec(v___x_3319_);
                            v___x_3322_ = lean_box(0);
                            v_isShared_3323_ = v_isSharedCheck_3328_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3318_);
                        return v___x_3319_;
                    }
                } else {
                    lean_dec_ref(v_b_3311_);
                    lean_dec_ref(v_a_3310_);
                    return v___x_3317_;
                }
            }
            1 => {
                v___x_3324_ = l_Lean_Meta_mkExpectedPropHint(v_a_3318_, v_a_3320_);
                if v_isShared_3323_ == 0 {
                    lean_ctor_set(v___x_3322_, 0, v___x_3324_);
                    v___x_3326_ = v___x_3322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
                    v___x_3326_ = v_reuseFailAlloc_3327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType___boxed(
    mut v_a_3329_: *mut LeanObject,
    mut v_b_3330_: *mut LeanObject,
    mut v_a_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
    mut v_a_3333_: *mut LeanObject,
    mut v_a_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3336_: *mut LeanObject = core::ptr::null_mut();
    v_res_3336_ = l_Lean_Elab_Tactic_Omega_mkEqReflWithExpectedType(
        v_a_3329_, v_b_3330_, v_a_3331_, v_a_3332_, v_a_3333_, v_a_3334_,
    );
    lean_dec(v_a_3334_);
    lean_dec_ref(v_a_3333_);
    lean_dec(v_a_3332_);
    lean_dec_ref(v_a_3331_);
    return v_res_3336_;
}
pub unsafe fn l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
    mut v_a_3337_: *mut LeanObject,
    mut v_x_3338_: *mut LeanObject,
) -> u8 {
    let mut v___x_3339_: u8 = 0;
    let mut v_head_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3338_) == 0 {
                    v___x_3339_ = 0;
                    return v___x_3339_;
                } else {
                    v_head_3340_ = lean_ctor_get(v_x_3338_, 0);
                    v_tail_3341_ = lean_ctor_get(v_x_3338_, 1);
                    v___x_3342_ = lean_expr_eqv(v_a_3337_, v_head_3340_);
                    if v___x_3342_ == 0 {
                        v_x_3338_ = v_tail_3341_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3342_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0___boxed(
    mut v_a_3344_: *mut LeanObject,
    mut v_x_3345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3346_: u8 = 0;
    let mut v_r_3347_: *mut LeanObject = core::ptr::null_mut();
    v_res_3346_ =
        l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(v_a_3344_, v_x_3345_);
    lean_dec(v_x_3345_);
    lean_dec_ref(v_a_3344_);
    v_r_3347_ = lean_box((v_res_3346_) as usize);
    return v_r_3347_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    v___x_3356_ = lean_box(0);
    v___x_3357_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__5;
    v___x_3358_ = l_Lean_Expr_const___override(v___x_3357_, v___x_3356_);
    return v___x_3358_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    v___x_3363_ = lean_box(0);
    v___x_3364_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__8;
    v___x_3365_ = l_Lean_Expr_const___override(v___x_3364_, v___x_3363_);
    return v___x_3365_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13() -> *mut LeanObject
{
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    v___x_3371_ = lean_box(0);
    v___x_3372_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__12;
    v___x_3373_ = l_Lean_Expr_const___override(v___x_3372_, v___x_3371_);
    return v___x_3373_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16() -> *mut LeanObject
{
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut LeanObject = core::ptr::null_mut();
    v___x_3378_ = lean_box(0);
    v___x_3379_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__15;
    v___x_3380_ = l_Lean_Expr_const___override(v___x_3379_, v___x_3378_);
    return v___x_3380_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23() -> *mut LeanObject
{
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    v___x_3393_ = lean_unsigned_to_nat(0);
    v___x_3394_ = l_Lean_Level_ofNat(v___x_3393_);
    return v___x_3394_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27() -> *mut LeanObject
{
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    v___x_3400_ = lean_unsigned_to_nat(0);
    v___x_3401_ = l_Lean_mkNatLit(v___x_3400_);
    return v___x_3401_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38() -> *mut LeanObject
{
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    v___x_3424_ = lean_unsigned_to_nat(0);
    v___x_3425_ = lean_nat_to_int(v___x_3424_);
    return v___x_3425_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39() -> u8 {
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: u8 = 0;
    v___x_3426_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38,
    );
    v___x_3427_ = lean_int_dec_le(v___x_3426_, v___x_3426_);
    return v___x_3427_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45() -> *mut LeanObject
{
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    v___x_3437_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38,
    );
    v___x_3438_ = lean_int_neg(v___x_3437_);
    return v___x_3438_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46() -> *mut LeanObject
{
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    v___x_3439_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__45,
    );
    v___x_3440_ = l_Int_toNat(v___x_3439_);
    return v___x_3440_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47() -> *mut LeanObject
{
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    v___x_3441_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__46,
    );
    v___x_3442_ = l_Lean_instToExprInt_mkNat(v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48() -> *mut LeanObject
{
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    v___x_3443_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__38,
    );
    v___x_3444_ = l_Int_toNat(v___x_3443_);
    return v___x_3444_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49() -> *mut LeanObject
{
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    v___x_3445_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__48,
    );
    v___x_3446_ = l_Lean_instToExprInt_mkNat(v___x_3445_);
    return v___x_3446_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50() -> *mut LeanObject
{
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    v___x_3447_ = lean_box(0);
    v___x_3448_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23,
    );
    v___x_3449_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3449_, 0, v___x_3448_);
    lean_ctor_set(v___x_3449_, 1, v___x_3447_);
    return v___x_3449_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51() -> *mut LeanObject
{
    let mut v___x_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    v___x_3450_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50,
    );
    v___x_3451_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
    v___x_3452_ = l_Lean_Expr_const___override(v___x_3451_, v___x_3450_);
    return v___x_3452_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54() -> *mut LeanObject
{
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    v___x_3457_ = lean_box(0);
    v___x_3458_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__53;
    v___x_3459_ = l_Lean_Expr_const___override(v___x_3458_, v___x_3457_);
    return v___x_3459_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57() -> *mut LeanObject
{
    let mut v___x_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    v___x_3466_ = lean_box(0);
    v___x_3467_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__56;
    v___x_3468_ = l_Lean_Expr_const___override(v___x_3467_, v___x_3466_);
    return v___x_3468_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58() -> *mut LeanObject
{
    let mut v___x_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    v___x_3469_ = lean_box(0);
    v___x_3470_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
    v___x_3471_ = l_Lean_Expr_const___override(v___x_3470_, v___x_3469_);
    return v___x_3471_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59() -> *mut LeanObject
{
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    v___x_3472_ = lean_box(0);
    v___x_3473_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35;
    v___x_3474_ = l_Lean_Expr_const___override(v___x_3473_, v___x_3472_);
    return v___x_3474_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60() -> *mut LeanObject
{
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    v___x_3475_ = lean_box(0);
    v___x_3476_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
    v___x_3477_ = l_Lean_Expr_const___override(v___x_3476_, v___x_3475_);
    return v___x_3477_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61() -> *mut LeanObject
{
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    v___x_3478_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50,
    );
    v___x_3479_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
    v___x_3480_ = l_Lean_Expr_const___override(v___x_3479_, v___x_3478_);
    return v___x_3480_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62() -> *mut LeanObject
{
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    v___x_3481_ = lean_box(0);
    v___x_3482_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
    v___x_3483_ = l_Lean_Expr_const___override(v___x_3482_, v___x_3481_);
    return v___x_3483_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63() -> *mut LeanObject
{
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    v___x_3484_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47,
    );
    v___x_3485_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__62,
    );
    v___x_3486_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once),
        _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2,
    );
    v___x_3487_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__61,
    );
    v___x_3488_ = l_Lean_mkApp3(v___x_3487_, v___x_3486_, v___x_3485_, v___x_3484_);
    return v___x_3488_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66() -> *mut LeanObject
{
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    v___x_3492_ = lean_unsigned_to_nat(1);
    v___x_3493_ = l_Lean_Level_ofNat(v___x_3492_);
    return v___x_3493_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67() -> *mut LeanObject
{
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    v___x_3494_ = lean_box(0);
    v___x_3495_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__66,
    );
    v___x_3496_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_3496_, 0, v___x_3495_);
    lean_ctor_set(v___x_3496_, 1, v___x_3494_);
    return v___x_3496_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68() -> *mut LeanObject
{
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    v___x_3497_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__67,
    );
    v___x_3498_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__65;
    v___x_3499_ = l_Lean_Expr_const___override(v___x_3498_, v___x_3497_);
    return v___x_3499_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71() -> *mut LeanObject
{
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    v___x_3504_ = lean_box(0);
    v___x_3505_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__70;
    v___x_3506_ = l_Lean_Expr_const___override(v___x_3505_, v___x_3504_);
    return v___x_3506_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74() -> *mut LeanObject
{
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    v___x_3511_ = lean_box(0);
    v___x_3512_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__73;
    v___x_3513_ = l_Lean_Expr_const___override(v___x_3512_, v___x_3511_);
    return v___x_3513_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94() -> *mut LeanObject
{
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    v___x_3552_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50),
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50_once),
        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__50,
    );
    v___x_3553_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__93;
    v___x_3554_ = l_Lean_Expr_const___override(v___x_3553_, v___x_3552_);
    return v___x_3554_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
    mut v_e_3555_: *mut LeanObject,
    mut v_a_3556_: *mut LeanObject,
    mut v_a_3557_: *mut LeanObject,
    mut v_a_3558_: *mut LeanObject,
    mut v_a_3559_: *mut LeanObject,
    mut v_a_3560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3587_: u8 = 0;
    let mut v_str_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: u8 = 0;
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: u8 = 0;
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: u8 = 0;
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: u8 = 0;
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: u8 = 0;
    let mut v___x_3602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: u8 = 0;
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: u8 = 0;
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: u8 = 0;
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: u8 = 0;
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3652_: u8 = 0;
    let mut v_str_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3665_: u8 = 0;
    let mut v_str_3666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: u8 = 0;
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3673_: u8 = 0;
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_unused_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: u8 = 0;
    let mut v___x_3696_: u8 = 0;
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: u8 = 0;
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: u8 = 0;
    let mut v___x_3702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: u8 = 0;
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v_str_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: u8 = 0;
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: u8 = 0;
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: u8 = 0;
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b__pos_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3746_: u8 = 0;
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: u8 = 0;
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3785_: u8 = 0;
    let mut v_a_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3789_: u8 = 0;
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3793_: u8 = 0;
    let mut v_reuseFailAlloc_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v_unused_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: u8 = 0;
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u8 = 0;
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: u8 = 0;
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b__pos_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3836_: u8 = 0;
    let mut v_a_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3848_: u8 = 0;
    let mut v_unused_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: u8 = 0;
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: u8 = 0;
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: u8 = 0;
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ne__zero_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pos_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3878_: u8 = 0;
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3890_: u8 = 0;
    let mut v_a_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3894_: u8 = 0;
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut v_a_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3902_: u8 = 0;
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v___x_3907_: u8 = 0;
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: u8 = 0;
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: u8 = 0;
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: u8 = 0;
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: u8 = 0;
    let mut v_splitNatSub_3935_: u8 = 0;
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3977_: u8 = 0;
    let mut v_str_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: u8 = 0;
    let mut v___x_3982_: u8 = 0;
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: u8 = 0;
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: u8 = 0;
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: u8 = 0;
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: u8 = 0;
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: u8 = 0;
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: u8 = 0;
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: u8 = 0;
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: u8 = 0;
    let mut v___x_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: u8 = 0;
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: u8 = 0;
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4034_: u8 = 0;
    let mut v_unused_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4046_: u8 = 0;
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: u8 = 0;
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: u8 = 0;
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: u8 = 0;
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: u8 = 0;
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: u8 = 0;
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4081_: u8 = 0;
    let mut v_unused_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4086_: u8 = 0;
    let mut v_str_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: u8 = 0;
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: u8 = 0;
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4113_: u8 = 0;
    let mut v_unused_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3580_ = l_Lean_Expr_getAppFnArgs(v_e_3555_);
                v_fst_3581_ = lean_ctor_get(v___x_3580_, 0);
                lean_inc(v_fst_3581_);
                if lean_obj_tag(v_fst_3581_) == 1 {
                    v_pre_3582_ = lean_ctor_get(v_fst_3581_, 0);
                    match lean_obj_tag(v_pre_3582_) {
                        1 => {
                            lean_inc_ref(v_pre_3582_);
                            v_pre_3583_ = lean_ctor_get(v_pre_3582_, 0);
                            if lean_obj_tag(v_pre_3583_) == 0 {
                                v_snd_3584_ = lean_ctor_get(v___x_3580_, 1);
                                v_isSharedCheck_4081_ = (!lean_is_exclusive(v___x_3580_)) as u8;
                                if v_isSharedCheck_4081_ == 0 {
                                    v_unused_4082_ = lean_ctor_get(v___x_3580_, 0);
                                    lean_dec(v_unused_4082_);
                                    v___x_3586_ = v___x_3580_;
                                    v_isShared_3587_ = v_isSharedCheck_4081_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_snd_3584_);
                                    lean_dec(v___x_3580_);
                                    v___x_3586_ = lean_box(0);
                                    v_isShared_3587_ = v_isSharedCheck_4081_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_pre_3582_, 2);
                                lean_dec_ref_known(v_fst_3581_, 2);
                                lean_dec_ref(v___x_3580_);
                                state = 3;
                                continue;
                            }
                        }
                        0 => {
                            v_snd_4083_ = lean_ctor_get(v___x_3580_, 1);
                            v_isSharedCheck_4113_ = (!lean_is_exclusive(v___x_3580_)) as u8;
                            if v_isSharedCheck_4113_ == 0 {
                                v_unused_4114_ = lean_ctor_get(v___x_3580_, 0);
                                lean_dec(v_unused_4114_);
                                v___x_4085_ = v___x_3580_;
                                v_isShared_4086_ = v_isSharedCheck_4113_;
                                state = 45;
                                continue;
                            } else {
                                lean_inc(v_snd_4083_);
                                lean_dec(v___x_3580_);
                                v___x_4085_ = lean_box(0);
                                v_isShared_4086_ = v_isSharedCheck_4113_;
                                state = 45;
                                continue;
                            }
                        }
                        _ => {
                            lean_dec_ref_known(v_fst_3581_, 2);
                            lean_dec_ref(v___x_3580_);
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fst_3581_);
                    lean_dec_ref(v___x_3580_);
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3563_ = lean_box(0);
                v___x_3564_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3564_, 0, v___x_3563_);
                return v___x_3564_;
            }
            2 => {
                v___x_3566_ = lean_box(0);
                v___x_3567_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3567_, 0, v___x_3566_);
                return v___x_3567_;
            }
            3 => {
                v___x_3569_ = lean_box(0);
                v___x_3570_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3570_, 0, v___x_3569_);
                return v___x_3570_;
            }
            4 => {
                v___x_3572_ = lean_box(0);
                v___x_3573_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3573_, 0, v___x_3572_);
                return v___x_3573_;
            }
            5 => {
                v___x_3575_ = lean_box(0);
                v___x_3576_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3576_, 0, v___x_3575_);
                return v___x_3576_;
            }
            6 => {
                v___x_3578_ = lean_box(0);
                v___x_3579_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3579_, 0, v___x_3578_);
                return v___x_3579_;
            }
            7 => {
                v_str_3588_ = lean_ctor_get(v_fst_3581_, 1);
                lean_inc_ref(v_str_3588_);
                lean_dec_ref_known(v_fst_3581_, 2);
                v_str_3589_ = lean_ctor_get(v_pre_3582_, 1);
                lean_inc_ref(v_str_3589_);
                lean_dec_ref_known(v_pre_3582_, 2);
                v___x_3590_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__0;
                v___x_3591_ = lean_string_dec_eq(v_str_3589_, v___x_3590_);
                if v___x_3591_ == 0 {
                    v___x_3592_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__3;
                    v___x_3593_ = lean_string_dec_eq(v_str_3589_, v___x_3592_);
                    if v___x_3593_ == 0 {
                        v___x_3594_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__0;
                        v___x_3595_ = lean_string_dec_eq(v_str_3589_, v___x_3594_);
                        if v___x_3595_ == 0 {
                            v___x_3596_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__1;
                            v___x_3597_ = lean_string_dec_eq(v_str_3589_, v___x_3596_);
                            if v___x_3597_ == 0 {
                                v___x_3598_ =
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__2;
                                v___x_3599_ = lean_string_dec_eq(v_str_3589_, v___x_3598_);
                                lean_dec_ref(v_str_3589_);
                                if v___x_3599_ == 0 {
                                    lean_dec_ref(v_str_3588_);
                                    lean_del_object(v___x_3586_);
                                    lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3600_ =
                                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__3;
                                    v___x_3601_ = lean_string_dec_eq(v_str_3588_, v___x_3600_);
                                    lean_dec_ref(v_str_3588_);
                                    if v___x_3601_ == 0 {
                                        lean_del_object(v___x_3586_);
                                        lean_dec(v_snd_3584_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3602_ = lean_array_get_size(v_snd_3584_);
                                        v___x_3603_ = lean_unsigned_to_nat(4);
                                        v___x_3604_ = lean_nat_dec_eq(v___x_3602_, v___x_3603_);
                                        if v___x_3604_ == 0 {
                                            lean_del_object(v___x_3586_);
                                            lean_dec(v_snd_3584_);
                                            state = 3;
                                            continue;
                                        } else {
                                            v___x_3605_ = lean_unsigned_to_nat(2);
                                            v___x_3606_ = lean_array_fget(v_snd_3584_, v___x_3605_);
                                            v___x_3607_ = lean_unsigned_to_nat(3);
                                            v___x_3608_ = lean_array_fget(v_snd_3584_, v___x_3607_);
                                            lean_dec(v_snd_3584_);
                                            v___x_3609_ = lean_box(0);
                                            v___x_3610_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__6);
                                            lean_inc(v___x_3608_);
                                            lean_inc(v___x_3606_);
                                            v___x_3611_ = l_Lean_mkAppB(
                                                v___x_3610_,
                                                v___x_3606_,
                                                v___x_3608_,
                                            );
                                            v___x_3612_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__9);
                                            v___x_3613_ = l_Lean_mkAppB(
                                                v___x_3612_,
                                                v___x_3606_,
                                                v___x_3608_,
                                            );
                                            if v_isShared_3587_ == 0 {
                                                lean_ctor_set_tag(v___x_3586_, 1);
                                                lean_ctor_set(v___x_3586_, 1, v___x_3609_);
                                                lean_ctor_set(v___x_3586_, 0, v___x_3613_);
                                                v___x_3615_ = v___x_3586_;
                                                state = 8;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3618_ =
                                                    lean_alloc_ctor(1, 2, (0) as u32);
                                                lean_ctor_set(
                                                    v_reuseFailAlloc_3618_,
                                                    0,
                                                    v___x_3613_,
                                                );
                                                lean_ctor_set(
                                                    v_reuseFailAlloc_3618_,
                                                    1,
                                                    v___x_3609_,
                                                );
                                                v___x_3615_ = v_reuseFailAlloc_3618_;
                                                state = 8;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_str_3589_);
                                v___x_3619_ =
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__10;
                                v___x_3620_ = lean_string_dec_eq(v_str_3588_, v___x_3619_);
                                lean_dec_ref(v_str_3588_);
                                if v___x_3620_ == 0 {
                                    lean_del_object(v___x_3586_);
                                    lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3621_ = lean_array_get_size(v_snd_3584_);
                                    v___x_3622_ = lean_unsigned_to_nat(4);
                                    v___x_3623_ = lean_nat_dec_eq(v___x_3621_, v___x_3622_);
                                    if v___x_3623_ == 0 {
                                        lean_del_object(v___x_3586_);
                                        lean_dec(v_snd_3584_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3624_ = lean_unsigned_to_nat(2);
                                        v___x_3625_ = lean_array_fget(v_snd_3584_, v___x_3624_);
                                        v___x_3626_ = lean_unsigned_to_nat(3);
                                        v___x_3627_ = lean_array_fget(v_snd_3584_, v___x_3626_);
                                        lean_dec(v_snd_3584_);
                                        v___x_3628_ = lean_box(0);
                                        v___x_3629_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__13);
                                        lean_inc(v___x_3627_);
                                        lean_inc(v___x_3625_);
                                        v___x_3630_ =
                                            l_Lean_mkAppB(v___x_3629_, v___x_3625_, v___x_3627_);
                                        v___x_3631_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__16);
                                        v___x_3632_ =
                                            l_Lean_mkAppB(v___x_3631_, v___x_3625_, v___x_3627_);
                                        if v_isShared_3587_ == 0 {
                                            lean_ctor_set_tag(v___x_3586_, 1);
                                            lean_ctor_set(v___x_3586_, 1, v___x_3628_);
                                            lean_ctor_set(v___x_3586_, 0, v___x_3632_);
                                            v___x_3634_ = v___x_3586_;
                                            state = 9;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3637_ =
                                                lean_alloc_ctor(1, 2, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3632_);
                                            lean_ctor_set(v_reuseFailAlloc_3637_, 1, v___x_3628_);
                                            v___x_3634_ = v_reuseFailAlloc_3637_;
                                            state = 9;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_str_3589_);
                            v___x_3638_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__17;
                            v___x_3639_ = lean_string_dec_eq(v_str_3588_, v___x_3638_);
                            lean_dec_ref(v_str_3588_);
                            if v___x_3639_ == 0 {
                                lean_del_object(v___x_3586_);
                                lean_dec(v_snd_3584_);
                                state = 3;
                                continue;
                            } else {
                                v___x_3640_ = lean_array_get_size(v_snd_3584_);
                                v___x_3641_ = lean_unsigned_to_nat(6);
                                v___x_3642_ = lean_nat_dec_eq(v___x_3640_, v___x_3641_);
                                if v___x_3642_ == 0 {
                                    lean_del_object(v___x_3586_);
                                    lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3643_ = lean_unsigned_to_nat(5);
                                    v___x_3644_ = lean_array_fget(v_snd_3584_, v___x_3643_);
                                    lean_inc(v___x_3644_);
                                    v___x_3645_ = l_Lean_Expr_getAppFnArgs(v___x_3644_);
                                    v_fst_3646_ = lean_ctor_get(v___x_3645_, 0);
                                    lean_inc(v_fst_3646_);
                                    if lean_obj_tag(v_fst_3646_) == 1 {
                                        v_pre_3647_ = lean_ctor_get(v_fst_3646_, 0);
                                        lean_inc(v_pre_3647_);
                                        if lean_obj_tag(v_pre_3647_) == 1 {
                                            v_pre_3648_ = lean_ctor_get(v_pre_3647_, 0);
                                            if lean_obj_tag(v_pre_3648_) == 0 {
                                                v_snd_3649_ = lean_ctor_get(v___x_3645_, 1);
                                                v_isSharedCheck_3848_ =
                                                    (!lean_is_exclusive(v___x_3645_)) as u8;
                                                if v_isSharedCheck_3848_ == 0 {
                                                    v_unused_3849_ = lean_ctor_get(v___x_3645_, 0);
                                                    lean_dec(v_unused_3849_);
                                                    v___x_3651_ = v___x_3645_;
                                                    v_isShared_3652_ = v_isSharedCheck_3848_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    lean_inc(v_snd_3649_);
                                                    lean_dec(v___x_3645_);
                                                    v___x_3651_ = lean_box(0);
                                                    v_isShared_3652_ = v_isSharedCheck_3848_;
                                                    state = 10;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref_known(v_pre_3647_, 2);
                                                lean_dec_ref_known(v_fst_3646_, 2);
                                                lean_dec_ref(v___x_3645_);
                                                lean_dec(v___x_3644_);
                                                lean_del_object(v___x_3586_);
                                                lean_dec(v_snd_3584_);
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref_known(v_fst_3646_, 2);
                                            lean_dec(v_pre_3647_);
                                            lean_dec_ref(v___x_3645_);
                                            lean_dec(v___x_3644_);
                                            lean_del_object(v___x_3586_);
                                            lean_dec(v_snd_3584_);
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_fst_3646_);
                                        lean_dec_ref(v___x_3645_);
                                        lean_dec(v___x_3644_);
                                        lean_del_object(v___x_3586_);
                                        lean_dec(v_snd_3584_);
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_str_3589_);
                        v___x_3850_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__7;
                        v___x_3851_ = lean_string_dec_eq(v_str_3588_, v___x_3850_);
                        lean_dec_ref(v_str_3588_);
                        if v___x_3851_ == 0 {
                            lean_del_object(v___x_3586_);
                            lean_dec(v_snd_3584_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3852_ = lean_array_get_size(v_snd_3584_);
                            v___x_3853_ = lean_unsigned_to_nat(6);
                            v___x_3854_ = lean_nat_dec_eq(v___x_3852_, v___x_3853_);
                            if v___x_3854_ == 0 {
                                lean_del_object(v___x_3586_);
                                lean_dec(v_snd_3584_);
                                state = 3;
                                continue;
                            } else {
                                v___x_3855_ = lean_unsigned_to_nat(5);
                                v___x_3856_ = lean_array_fget(v_snd_3584_, v___x_3855_);
                                lean_inc(v___x_3856_);
                                v___x_3857_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_3856_);
                                if lean_obj_tag(v___x_3857_) == 0 {
                                    lean_dec(v___x_3856_);
                                    lean_del_object(v___x_3586_);
                                    lean_dec(v_snd_3584_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_3858_ = lean_ctor_get(v___x_3857_, 0);
                                    lean_inc(v_val_3858_);
                                    lean_dec_ref_known(v___x_3857_, 1);
                                    v___x_3859_ = lean_unsigned_to_nat(0);
                                    v___x_3860_ = lean_nat_dec_eq(v_val_3858_, v___x_3859_);
                                    lean_dec(v_val_3858_);
                                    if v___x_3860_ == 0 {
                                        v___x_3861_ = lean_unsigned_to_nat(4);
                                        v___x_3862_ = lean_array_fget(v_snd_3584_, v___x_3861_);
                                        lean_dec(v_snd_3584_);
                                        v___x_3863_ = lean_box(0);
                                        v___x_3864_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__68);
                                        v___x_3865_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
                                        v___x_3907_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
                                        if v___x_3907_ == 0 {
                                            v___x_3908_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
                                            v___y_3867_ = v___x_3908_;
                                            state = 30;
                                            continue;
                                        } else {
                                            v___x_3909_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
                                            v___y_3867_ = v___x_3909_;
                                            state = 30;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v___x_3856_);
                                        lean_del_object(v___x_3586_);
                                        lean_dec(v_snd_3584_);
                                        state = 1;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_str_3589_);
                    v___x_3910_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                    v___x_3911_ = lean_string_dec_eq(v_str_3588_, v___x_3910_);
                    lean_dec_ref(v_str_3588_);
                    if v___x_3911_ == 0 {
                        lean_del_object(v___x_3586_);
                        lean_dec(v_snd_3584_);
                        state = 3;
                        continue;
                    } else {
                        v___x_3912_ = lean_array_get_size(v_snd_3584_);
                        v___x_3913_ = lean_unsigned_to_nat(3);
                        v___x_3914_ = lean_nat_dec_eq(v___x_3912_, v___x_3913_);
                        if v___x_3914_ == 0 {
                            lean_del_object(v___x_3586_);
                            lean_dec(v_snd_3584_);
                            state = 3;
                            continue;
                        } else {
                            v___x_3915_ = lean_unsigned_to_nat(0);
                            v___x_3916_ = lean_array_fget_borrowed(v_snd_3584_, v___x_3915_);
                            if lean_obj_tag(v___x_3916_) == 4 {
                                v_declName_3917_ = lean_ctor_get(v___x_3916_, 0);
                                if lean_obj_tag(v_declName_3917_) == 1 {
                                    v_pre_3918_ = lean_ctor_get(v_declName_3917_, 0);
                                    if lean_obj_tag(v_pre_3918_) == 0 {
                                        v_us_3919_ = lean_ctor_get(v___x_3916_, 1);
                                        lean_inc(v_us_3919_);
                                        v_str_3920_ = lean_ctor_get(v_declName_3917_, 1);
                                        v___x_3921_ =
                                            l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
                                        v___x_3934_ = lean_string_dec_eq(v_str_3920_, v___x_3921_);
                                        if v___x_3934_ == 0 {
                                            lean_dec(v_us_3919_);
                                            lean_del_object(v___x_3586_);
                                            lean_dec(v_snd_3584_);
                                            state = 3;
                                            continue;
                                        } else {
                                            if lean_obj_tag(v_us_3919_) == 0 {
                                                v_splitNatSub_3935_ =
                                                    lean_ctor_get_uint8(v_a_3556_, 1 as u32);
                                                v___x_3936_ = lean_unsigned_to_nat(2);
                                                v___x_3937_ =
                                                    lean_array_fget(v_snd_3584_, v___x_3936_);
                                                lean_dec(v_snd_3584_);
                                                v___x_3938_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__78;
                                                v___x_3939_ = l_Lean_Expr_const___override(
                                                    v___x_3938_,
                                                    v_us_3919_,
                                                );
                                                lean_inc(v___x_3937_);
                                                v___x_3940_ = l_Lean_Expr_app___override(
                                                    v___x_3939_,
                                                    v___x_3937_,
                                                );
                                                v___x_3941_ = lean_box(0);
                                                v_r_3942_ = lean_alloc_ctor(1, 2, (0) as u32);
                                                lean_ctor_set(v_r_3942_, 0, v___x_3940_);
                                                lean_ctor_set(v_r_3942_, 1, v___x_3941_);
                                                if v_splitNatSub_3935_ == 1 {
                                                    v___x_3970_ =
                                                        l_Lean_Expr_getAppFnArgs(v___x_3937_);
                                                    v_fst_3971_ = lean_ctor_get(v___x_3970_, 0);
                                                    lean_inc(v_fst_3971_);
                                                    if lean_obj_tag(v_fst_3971_) == 1 {
                                                        v_pre_3972_ = lean_ctor_get(v_fst_3971_, 0);
                                                        lean_inc(v_pre_3972_);
                                                        if lean_obj_tag(v_pre_3972_) == 1 {
                                                            v_pre_3973_ =
                                                                lean_ctor_get(v_pre_3972_, 0);
                                                            if lean_obj_tag(v_pre_3973_) == 0 {
                                                                v_snd_3974_ =
                                                                    lean_ctor_get(v___x_3970_, 1);
                                                                v_isSharedCheck_4034_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3970_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_4034_ == 0 {
                                                                    v_unused_4035_ = lean_ctor_get(
                                                                        v___x_3970_,
                                                                        0,
                                                                    );
                                                                    lean_dec(v_unused_4035_);
                                                                    v___x_3976_ = v___x_3970_;
                                                                    v_isShared_3977_ =
                                                                        v_isSharedCheck_4034_;
                                                                    state = 43;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_snd_3974_);
                                                                    lean_dec(v___x_3970_);
                                                                    v___x_3976_ = lean_box(0);
                                                                    v_isShared_3977_ =
                                                                        v_isSharedCheck_4034_;
                                                                    state = 43;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref_known(v_pre_3972_, 2);
                                                                lean_dec_ref_known(v_fst_3971_, 2);
                                                                lean_dec_ref(v___x_3970_);
                                                                lean_del_object(v___x_3586_);
                                                                v___x_4036_ = lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_4036_,
                                                                    0,
                                                                    v_r_3942_,
                                                                );
                                                                return v___x_4036_;
                                                            }
                                                        } else {
                                                            lean_dec_ref_known(v_fst_3971_, 2);
                                                            lean_dec(v_pre_3972_);
                                                            lean_dec_ref(v___x_3970_);
                                                            lean_del_object(v___x_3586_);
                                                            v___x_4037_ =
                                                                lean_alloc_ctor(0, 1, (0) as u32);
                                                            lean_ctor_set(
                                                                v___x_4037_,
                                                                0,
                                                                v_r_3942_,
                                                            );
                                                            return v___x_4037_;
                                                        }
                                                    } else {
                                                        lean_dec(v_fst_3971_);
                                                        lean_dec_ref(v___x_3970_);
                                                        lean_del_object(v___x_3586_);
                                                        v___x_4038_ =
                                                            lean_alloc_ctor(0, 1, (0) as u32);
                                                        lean_ctor_set(v___x_4038_, 0, v_r_3942_);
                                                        return v___x_4038_;
                                                    }
                                                } else {
                                                    v___x_4039_ =
                                                        l_Lean_Expr_getAppFnArgs(v___x_3937_);
                                                    v_fst_4040_ = lean_ctor_get(v___x_4039_, 0);
                                                    lean_inc(v_fst_4040_);
                                                    if lean_obj_tag(v_fst_4040_) == 1 {
                                                        v_pre_4041_ = lean_ctor_get(v_fst_4040_, 0);
                                                        lean_inc(v_pre_4041_);
                                                        if lean_obj_tag(v_pre_4041_) == 1 {
                                                            v_pre_4042_ =
                                                                lean_ctor_get(v_pre_4041_, 0);
                                                            if lean_obj_tag(v_pre_4042_) == 0 {
                                                                v_snd_4043_ =
                                                                    lean_ctor_get(v___x_4039_, 1);
                                                                lean_inc(v_snd_4043_);
                                                                lean_dec_ref(v___x_4039_);
                                                                v_str_4044_ =
                                                                    lean_ctor_get(v_fst_4040_, 1);
                                                                lean_inc_ref(v_str_4044_);
                                                                lean_dec_ref_known(v_fst_4040_, 2);
                                                                v_str_4045_ =
                                                                    lean_ctor_get(v_pre_4041_, 1);
                                                                lean_inc_ref(v_str_4045_);
                                                                lean_dec_ref_known(v_pre_4041_, 2);
                                                                v___x_4046_ = lean_string_dec_eq(
                                                                    v_str_4045_,
                                                                    v___x_3921_,
                                                                );
                                                                if v___x_4046_ == 0 {
                                                                    lean_del_object(v___x_3586_);
                                                                    v___x_4047_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
                                                                    v___x_4048_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_4045_,
                                                                            v___x_4047_,
                                                                        );
                                                                    if v___x_4048_ == 0 {
                                                                        v___x_4049_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79;
                                                                        v___x_4050_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_4045_,
                                                                                v___x_4049_,
                                                                            );
                                                                        lean_dec_ref(v_str_4045_);
                                                                        if v___x_4050_ == 0 {
                                                                            lean_dec_ref(
                                                                                v_str_4044_,
                                                                            );
                                                                            lean_dec(v_snd_4043_);
                                                                            v___x_4051_ =
                                                                                lean_alloc_ctor(
                                                                                    0,
                                                                                    1,
                                                                                    (0) as u32,
                                                                                );
                                                                            lean_ctor_set(
                                                                                v___x_4051_,
                                                                                0,
                                                                                v_r_3942_,
                                                                            );
                                                                            return v___x_4051_;
                                                                        } else {
                                                                            v___x_4052_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
                                                                            v___x_4053_ =
                                                                                lean_string_dec_eq(
                                                                                    v_str_4044_,
                                                                                    v___x_4052_,
                                                                                );
                                                                            lean_dec_ref(
                                                                                v_str_4044_,
                                                                            );
                                                                            if v___x_4053_ == 0 {
                                                                                lean_dec(
                                                                                    v_snd_4043_,
                                                                                );
                                                                                v___x_4054_ =
                                                                                    lean_alloc_ctor(
                                                                                        0,
                                                                                        1,
                                                                                        (0) as u32,
                                                                                    );
                                                                                lean_ctor_set(
                                                                                    v___x_4054_,
                                                                                    0,
                                                                                    v_r_3942_,
                                                                                );
                                                                                return v___x_4054_;
                                                                            } else {
                                                                                v___x_4055_ = lean_array_get_size(v_snd_4043_);
                                                                                v___x_4056_ =
                                                                                    lean_nat_dec_eq(
                                                                                        v___x_4055_,
                                                                                        v___x_3936_,
                                                                                    );
                                                                                if v___x_4056_ == 0
                                                                                {
                                                                                    lean_dec(
                                                                                        v_snd_4043_,
                                                                                    );
                                                                                    v___x_4057_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                                                    lean_ctor_set(
                                                                                        v___x_4057_,
                                                                                        0,
                                                                                        v_r_3942_,
                                                                                    );
                                                                                    return v___x_4057_;
                                                                                } else {
                                                                                    v___x_4058_ = lean_array_fget(v_snd_4043_, v___x_3915_);
                                                                                    v___x_4059_ = lean_unsigned_to_nat(1);
                                                                                    v___x_4060_ = lean_array_fget(v_snd_4043_, v___x_4059_);
                                                                                    lean_dec(
                                                                                        v_snd_4043_,
                                                                                    );
                                                                                    v_n_3944_ =
                                                                                        v___x_4058_;
                                                                                    v_x_3945_ =
                                                                                        v___x_4060_;
                                                                                    state = 40;
                                                                                    continue;
                                                                                }
                                                                            }
                                                                        }
                                                                    } else {
                                                                        lean_dec_ref(v_str_4045_);
                                                                        v___x_4061_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
                                                                        v___x_4062_ =
                                                                            lean_string_dec_eq(
                                                                                v_str_4044_,
                                                                                v___x_4061_,
                                                                            );
                                                                        lean_dec_ref(v_str_4044_);
                                                                        if v___x_4062_ == 0 {
                                                                            lean_dec(v_snd_4043_);
                                                                            v___x_4063_ =
                                                                                lean_alloc_ctor(
                                                                                    0,
                                                                                    1,
                                                                                    (0) as u32,
                                                                                );
                                                                            lean_ctor_set(
                                                                                v___x_4063_,
                                                                                0,
                                                                                v_r_3942_,
                                                                            );
                                                                            return v___x_4063_;
                                                                        } else {
                                                                            v___x_4064_ =
                                                                                lean_array_get_size(
                                                                                    v_snd_4043_,
                                                                                );
                                                                            v___x_4065_ =
                                                                                lean_nat_dec_eq(
                                                                                    v___x_4064_,
                                                                                    v___x_3936_,
                                                                                );
                                                                            if v___x_4065_ == 0 {
                                                                                lean_dec(
                                                                                    v_snd_4043_,
                                                                                );
                                                                                v___x_4066_ =
                                                                                    lean_alloc_ctor(
                                                                                        0,
                                                                                        1,
                                                                                        (0) as u32,
                                                                                    );
                                                                                lean_ctor_set(
                                                                                    v___x_4066_,
                                                                                    0,
                                                                                    v_r_3942_,
                                                                                );
                                                                                return v___x_4066_;
                                                                            } else {
                                                                                v___x_4067_ =
                                                                                    lean_array_fget(
                                                                                        v_snd_4043_,
                                                                                        v___x_3915_,
                                                                                    );
                                                                                v___x_4068_ = lean_unsigned_to_nat(1);
                                                                                v___x_4069_ =
                                                                                    lean_array_fget(
                                                                                        v_snd_4043_,
                                                                                        v___x_4068_,
                                                                                    );
                                                                                lean_dec(
                                                                                    v_snd_4043_,
                                                                                );
                                                                                v_n_3954_ =
                                                                                    v___x_4067_;
                                                                                v_i_3955_ =
                                                                                    v___x_4069_;
                                                                                state = 41;
                                                                                continue;
                                                                            }
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_str_4045_);
                                                                    v___x_4070_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
                                                                    v___x_4071_ =
                                                                        lean_string_dec_eq(
                                                                            v_str_4044_,
                                                                            v___x_4070_,
                                                                        );
                                                                    lean_dec_ref(v_str_4044_);
                                                                    if v___x_4071_ == 0 {
                                                                        lean_dec(v_snd_4043_);
                                                                        lean_del_object(
                                                                            v___x_3586_,
                                                                        );
                                                                        v___x_4072_ =
                                                                            lean_alloc_ctor(
                                                                                0,
                                                                                1,
                                                                                (0) as u32,
                                                                            );
                                                                        lean_ctor_set(
                                                                            v___x_4072_,
                                                                            0,
                                                                            v_r_3942_,
                                                                        );
                                                                        return v___x_4072_;
                                                                    } else {
                                                                        v___x_4073_ =
                                                                            lean_array_get_size(
                                                                                v_snd_4043_,
                                                                            );
                                                                        v___x_4074_ =
                                                                            lean_unsigned_to_nat(1);
                                                                        v___x_4075_ =
                                                                            lean_nat_dec_eq(
                                                                                v___x_4073_,
                                                                                v___x_4074_,
                                                                            );
                                                                        if v___x_4075_ == 0 {
                                                                            lean_dec(v_snd_4043_);
                                                                            lean_del_object(
                                                                                v___x_3586_,
                                                                            );
                                                                            v___x_4076_ =
                                                                                lean_alloc_ctor(
                                                                                    0,
                                                                                    1,
                                                                                    (0) as u32,
                                                                                );
                                                                            lean_ctor_set(
                                                                                v___x_4076_,
                                                                                0,
                                                                                v_r_3942_,
                                                                            );
                                                                            return v___x_4076_;
                                                                        } else {
                                                                            v___x_4077_ =
                                                                                lean_array_fget(
                                                                                    v_snd_4043_,
                                                                                    v___x_3915_,
                                                                                );
                                                                            lean_dec(v_snd_4043_);
                                                                            v_x_3964_ = v___x_4077_;
                                                                            state = 42;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref_known(v_pre_4041_, 2);
                                                                lean_dec_ref_known(v_fst_4040_, 2);
                                                                lean_dec_ref(v___x_4039_);
                                                                lean_del_object(v___x_3586_);
                                                                v___x_4078_ = lean_alloc_ctor(
                                                                    0,
                                                                    1,
                                                                    (0) as u32,
                                                                );
                                                                lean_ctor_set(
                                                                    v___x_4078_,
                                                                    0,
                                                                    v_r_3942_,
                                                                );
                                                                return v___x_4078_;
                                                            }
                                                        } else {
                                                            lean_dec_ref_known(v_fst_4040_, 2);
                                                            lean_dec(v_pre_4041_);
                                                            lean_dec_ref(v___x_4039_);
                                                            lean_del_object(v___x_3586_);
                                                            v___x_4079_ =
                                                                lean_alloc_ctor(0, 1, (0) as u32);
                                                            lean_ctor_set(
                                                                v___x_4079_,
                                                                0,
                                                                v_r_3942_,
                                                            );
                                                            return v___x_4079_;
                                                        }
                                                    } else {
                                                        lean_dec(v_fst_4040_);
                                                        lean_dec_ref(v___x_4039_);
                                                        lean_del_object(v___x_3586_);
                                                        v___x_4080_ =
                                                            lean_alloc_ctor(0, 1, (0) as u32);
                                                        lean_ctor_set(v___x_4080_, 0, v_r_3942_);
                                                        return v___x_4080_;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_us_3919_);
                                                lean_del_object(v___x_3586_);
                                                lean_dec(v_snd_3584_);
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_del_object(v___x_3586_);
                                        lean_dec(v_snd_3584_);
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_3586_);
                                    lean_dec(v_snd_3584_);
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_3586_);
                                lean_dec(v_snd_3584_);
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            8 => {
                v___x_3616_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3616_, 0, v___x_3611_);
                lean_ctor_set(v___x_3616_, 1, v___x_3615_);
                v___x_3617_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3617_, 0, v___x_3616_);
                return v___x_3617_;
            }
            9 => {
                v___x_3635_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3635_, 0, v___x_3630_);
                lean_ctor_set(v___x_3635_, 1, v___x_3634_);
                v___x_3636_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3636_, 0, v___x_3635_);
                return v___x_3636_;
            }
            10 => {
                v_str_3653_ = lean_ctor_get(v_fst_3646_, 1);
                lean_inc_ref(v_str_3653_);
                lean_dec_ref_known(v_fst_3646_, 2);
                v_str_3654_ = lean_ctor_get(v_pre_3647_, 1);
                lean_inc_ref(v_str_3654_);
                lean_dec_ref_known(v_pre_3647_, 2);
                v___x_3655_ = lean_unsigned_to_nat(4);
                v___x_3656_ = lean_array_fget(v_snd_3584_, v___x_3655_);
                lean_dec(v_snd_3584_);
                v___x_3694_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__4;
                v___x_3695_ = lean_string_dec_eq(v_str_3654_, v___x_3694_);
                if v___x_3695_ == 0 {
                    v___x_3696_ = lean_string_dec_eq(v_str_3654_, v___x_3590_);
                    lean_dec_ref(v_str_3654_);
                    if v___x_3696_ == 0 {
                        lean_dec(v___x_3656_);
                        lean_dec_ref(v_str_3653_);
                        lean_del_object(v___x_3651_);
                        lean_dec(v_snd_3649_);
                        lean_dec(v___x_3644_);
                        lean_del_object(v___x_3586_);
                        state = 4;
                        continue;
                    } else {
                        v___x_3697_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                        v___x_3698_ = lean_string_dec_eq(v_str_3653_, v___x_3697_);
                        lean_dec_ref(v_str_3653_);
                        if v___x_3698_ == 0 {
                            lean_dec(v___x_3656_);
                            lean_del_object(v___x_3651_);
                            lean_dec(v_snd_3649_);
                            lean_dec(v___x_3644_);
                            lean_del_object(v___x_3586_);
                            state = 4;
                            continue;
                        } else {
                            v___x_3699_ = lean_array_get_size(v_snd_3649_);
                            v___x_3700_ = lean_unsigned_to_nat(3);
                            v___x_3701_ = lean_nat_dec_eq(v___x_3699_, v___x_3700_);
                            if v___x_3701_ == 0 {
                                lean_dec(v___x_3656_);
                                lean_del_object(v___x_3651_);
                                lean_dec(v_snd_3649_);
                                lean_dec(v___x_3644_);
                                lean_del_object(v___x_3586_);
                                state = 4;
                                continue;
                            } else {
                                v___x_3702_ = lean_unsigned_to_nat(0);
                                v___x_3703_ = lean_array_fget_borrowed(v_snd_3649_, v___x_3702_);
                                if lean_obj_tag(v___x_3703_) == 4 {
                                    v_declName_3704_ = lean_ctor_get(v___x_3703_, 0);
                                    if lean_obj_tag(v_declName_3704_) == 1 {
                                        v_pre_3705_ = lean_ctor_get(v_declName_3704_, 0);
                                        if lean_obj_tag(v_pre_3705_) == 0 {
                                            v_us_3706_ = lean_ctor_get(v___x_3703_, 1);
                                            lean_inc(v_us_3706_);
                                            v_str_3707_ = lean_ctor_get(v_declName_3704_, 1);
                                            v___x_3708_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
                                            v___x_3709_ =
                                                lean_string_dec_eq(v_str_3707_, v___x_3708_);
                                            if v___x_3709_ == 0 {
                                                lean_dec(v_us_3706_);
                                                lean_dec(v___x_3656_);
                                                lean_del_object(v___x_3651_);
                                                lean_dec(v_snd_3649_);
                                                lean_dec(v___x_3644_);
                                                lean_del_object(v___x_3586_);
                                                state = 4;
                                                continue;
                                            } else {
                                                if lean_obj_tag(v_us_3706_) == 0 {
                                                    v___x_3710_ = lean_unsigned_to_nat(2);
                                                    v___x_3711_ =
                                                        lean_array_fget(v_snd_3649_, v___x_3710_);
                                                    lean_dec(v_snd_3649_);
                                                    lean_inc(v___x_3711_);
                                                    v___x_3712_ =
                                                        l_Lean_Expr_getAppFnArgs(v___x_3711_);
                                                    v_fst_3713_ = lean_ctor_get(v___x_3712_, 0);
                                                    lean_inc(v_fst_3713_);
                                                    if lean_obj_tag(v_fst_3713_) == 1 {
                                                        v_pre_3714_ = lean_ctor_get(v_fst_3713_, 0);
                                                        lean_inc(v_pre_3714_);
                                                        if lean_obj_tag(v_pre_3714_) == 1 {
                                                            v_pre_3715_ =
                                                                lean_ctor_get(v_pre_3714_, 0);
                                                            if lean_obj_tag(v_pre_3715_) == 0 {
                                                                v_snd_3716_ =
                                                                    lean_ctor_get(v___x_3712_, 1);
                                                                v_isSharedCheck_3795_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3712_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_3795_ == 0 {
                                                                    v_unused_3796_ = lean_ctor_get(
                                                                        v___x_3712_,
                                                                        0,
                                                                    );
                                                                    lean_dec(v_unused_3796_);
                                                                    v___x_3718_ = v___x_3712_;
                                                                    v_isShared_3719_ =
                                                                        v_isSharedCheck_3795_;
                                                                    state = 14;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_snd_3716_);
                                                                    lean_dec(v___x_3712_);
                                                                    v___x_3718_ = lean_box(0);
                                                                    v_isShared_3719_ =
                                                                        v_isSharedCheck_3795_;
                                                                    state = 14;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref_known(v_pre_3714_, 2);
                                                                lean_dec_ref_known(v_fst_3713_, 2);
                                                                lean_dec_ref(v___x_3712_);
                                                                lean_dec(v___x_3711_);
                                                                lean_del_object(v___x_3651_);
                                                                lean_del_object(v___x_3586_);
                                                                state = 11;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec(v_pre_3714_);
                                                            lean_dec_ref_known(v_fst_3713_, 2);
                                                            lean_dec_ref(v___x_3712_);
                                                            lean_dec(v___x_3711_);
                                                            lean_del_object(v___x_3651_);
                                                            lean_del_object(v___x_3586_);
                                                            state = 11;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec(v_fst_3713_);
                                                        lean_dec_ref(v___x_3712_);
                                                        lean_dec(v___x_3711_);
                                                        lean_del_object(v___x_3651_);
                                                        lean_del_object(v___x_3586_);
                                                        state = 11;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec(v_us_3706_);
                                                    lean_dec(v___x_3656_);
                                                    lean_del_object(v___x_3651_);
                                                    lean_dec(v_snd_3649_);
                                                    lean_dec(v___x_3644_);
                                                    lean_del_object(v___x_3586_);
                                                    state = 4;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v___x_3656_);
                                            lean_del_object(v___x_3651_);
                                            lean_dec(v_snd_3649_);
                                            lean_dec(v___x_3644_);
                                            lean_del_object(v___x_3586_);
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v___x_3656_);
                                        lean_del_object(v___x_3651_);
                                        lean_dec(v_snd_3649_);
                                        lean_dec(v___x_3644_);
                                        lean_del_object(v___x_3586_);
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_3656_);
                                    lean_del_object(v___x_3651_);
                                    lean_dec(v_snd_3649_);
                                    lean_dec(v___x_3644_);
                                    lean_del_object(v___x_3586_);
                                    state = 4;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_str_3654_);
                    v___x_3797_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                    v___x_3798_ = lean_string_dec_eq(v_str_3653_, v___x_3797_);
                    lean_dec_ref(v_str_3653_);
                    if v___x_3798_ == 0 {
                        lean_dec(v___x_3656_);
                        lean_del_object(v___x_3651_);
                        lean_dec(v_snd_3649_);
                        lean_dec(v___x_3644_);
                        lean_del_object(v___x_3586_);
                        state = 4;
                        continue;
                    } else {
                        v___x_3799_ = lean_array_get_size(v_snd_3649_);
                        v___x_3800_ = lean_nat_dec_eq(v___x_3799_, v___x_3641_);
                        if v___x_3800_ == 0 {
                            lean_dec(v___x_3656_);
                            lean_del_object(v___x_3651_);
                            lean_dec(v_snd_3649_);
                            lean_dec(v___x_3644_);
                            lean_del_object(v___x_3586_);
                            state = 4;
                            continue;
                        } else {
                            v___x_3801_ = lean_array_fget(v_snd_3649_, v___x_3655_);
                            lean_inc(v___x_3801_);
                            v___x_3802_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_3801_);
                            if lean_obj_tag(v___x_3802_) == 0 {
                                lean_dec(v___x_3801_);
                                lean_dec(v___x_3656_);
                                lean_del_object(v___x_3651_);
                                lean_dec(v_snd_3649_);
                                lean_dec(v___x_3644_);
                                lean_del_object(v___x_3586_);
                                state = 2;
                                continue;
                            } else {
                                v_val_3803_ = lean_ctor_get(v___x_3802_, 0);
                                lean_inc(v_val_3803_);
                                lean_dec_ref_known(v___x_3802_, 1);
                                v___x_3804_ = lean_unsigned_to_nat(0);
                                v___x_3805_ = lean_nat_dec_eq(v_val_3803_, v___x_3804_);
                                lean_dec(v_val_3803_);
                                if v___x_3805_ == 0 {
                                    v___x_3806_ = lean_array_fget(v_snd_3649_, v___x_3643_);
                                    lean_dec(v_snd_3649_);
                                    v___x_3807_ = lean_box(0);
                                    v___x_3808_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51);
                                    v___x_3809_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2);
                                    v___x_3810_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54);
                                    v___x_3845_ = lean_uint8_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39);
                                    if v___x_3845_ == 0 {
                                        v___x_3846_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__63);
                                        v___y_3812_ = v___x_3846_;
                                        state = 23;
                                        continue;
                                    } else {
                                        v___x_3847_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49);
                                        v___y_3812_ = v___x_3847_;
                                        state = 23;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_3801_);
                                    lean_dec(v___x_3656_);
                                    lean_del_object(v___x_3651_);
                                    lean_dec(v_snd_3649_);
                                    lean_dec(v___x_3644_);
                                    lean_del_object(v___x_3586_);
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            11 => {
                v___x_3658_ = l_Lean_Expr_getAppFnArgs(v___x_3656_);
                v_fst_3659_ = lean_ctor_get(v___x_3658_, 0);
                lean_inc(v_fst_3659_);
                if lean_obj_tag(v_fst_3659_) == 1 {
                    v_pre_3660_ = lean_ctor_get(v_fst_3659_, 0);
                    lean_inc(v_pre_3660_);
                    if lean_obj_tag(v_pre_3660_) == 1 {
                        v_pre_3661_ = lean_ctor_get(v_pre_3660_, 0);
                        if lean_obj_tag(v_pre_3661_) == 0 {
                            v_snd_3662_ = lean_ctor_get(v___x_3658_, 1);
                            v_isSharedCheck_3692_ = (!lean_is_exclusive(v___x_3658_)) as u8;
                            if v_isSharedCheck_3692_ == 0 {
                                v_unused_3693_ = lean_ctor_get(v___x_3658_, 0);
                                lean_dec(v_unused_3693_);
                                v___x_3664_ = v___x_3658_;
                                v_isShared_3665_ = v_isSharedCheck_3692_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_snd_3662_);
                                lean_dec(v___x_3658_);
                                v___x_3664_ = lean_box(0);
                                v_isShared_3665_ = v_isSharedCheck_3692_;
                                state = 12;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_pre_3660_, 2);
                            lean_dec_ref_known(v_fst_3659_, 2);
                            lean_dec_ref(v___x_3658_);
                            lean_dec(v___x_3644_);
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_fst_3659_, 2);
                        lean_dec(v_pre_3660_);
                        lean_dec_ref(v___x_3658_);
                        lean_dec(v___x_3644_);
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_3659_);
                    lean_dec_ref(v___x_3658_);
                    lean_dec(v___x_3644_);
                    state = 5;
                    continue;
                }
            }
            12 => {
                v_str_3666_ = lean_ctor_get(v_fst_3659_, 1);
                lean_inc_ref(v_str_3666_);
                lean_dec_ref_known(v_fst_3659_, 2);
                v_str_3667_ = lean_ctor_get(v_pre_3660_, 1);
                lean_inc_ref(v_str_3667_);
                lean_dec_ref_known(v_pre_3660_, 2);
                v___x_3668_ = lean_string_dec_eq(v_str_3667_, v___x_3590_);
                lean_dec_ref(v_str_3667_);
                if v___x_3668_ == 0 {
                    lean_dec_ref(v_str_3666_);
                    lean_del_object(v___x_3664_);
                    lean_dec(v_snd_3662_);
                    lean_dec(v___x_3644_);
                    state = 5;
                    continue;
                } else {
                    v___x_3669_ = l_Lean_Elab_Tactic_Omega_natCast_x3f___closed__1;
                    v___x_3670_ = lean_string_dec_eq(v_str_3666_, v___x_3669_);
                    lean_dec_ref(v_str_3666_);
                    if v___x_3670_ == 0 {
                        lean_del_object(v___x_3664_);
                        lean_dec(v_snd_3662_);
                        lean_dec(v___x_3644_);
                        state = 5;
                        continue;
                    } else {
                        v___x_3671_ = lean_array_get_size(v_snd_3662_);
                        v___x_3672_ = lean_unsigned_to_nat(3);
                        v___x_3673_ = lean_nat_dec_eq(v___x_3671_, v___x_3672_);
                        if v___x_3673_ == 0 {
                            lean_del_object(v___x_3664_);
                            lean_dec(v_snd_3662_);
                            lean_dec(v___x_3644_);
                            state = 5;
                            continue;
                        } else {
                            v___x_3674_ = lean_unsigned_to_nat(0);
                            v___x_3675_ = lean_array_fget_borrowed(v_snd_3662_, v___x_3674_);
                            if lean_obj_tag(v___x_3675_) == 4 {
                                v_declName_3676_ = lean_ctor_get(v___x_3675_, 0);
                                if lean_obj_tag(v_declName_3676_) == 1 {
                                    v_pre_3677_ = lean_ctor_get(v_declName_3676_, 0);
                                    if lean_obj_tag(v_pre_3677_) == 0 {
                                        v_us_3678_ = lean_ctor_get(v___x_3675_, 1);
                                        lean_inc(v_us_3678_);
                                        v_str_3679_ = lean_ctor_get(v_declName_3676_, 1);
                                        v___x_3680_ =
                                            l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__0;
                                        v___x_3681_ = lean_string_dec_eq(v_str_3679_, v___x_3680_);
                                        if v___x_3681_ == 0 {
                                            lean_dec(v_us_3678_);
                                            lean_del_object(v___x_3664_);
                                            lean_dec(v_snd_3662_);
                                            lean_dec(v___x_3644_);
                                            state = 5;
                                            continue;
                                        } else {
                                            if lean_obj_tag(v_us_3678_) == 0 {
                                                v___x_3682_ = lean_unsigned_to_nat(2);
                                                v___x_3683_ =
                                                    lean_array_fget(v_snd_3662_, v___x_3682_);
                                                lean_dec(v_snd_3662_);
                                                v___x_3684_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__19;
                                                v___x_3685_ = l_Lean_Expr_const___override(
                                                    v___x_3684_,
                                                    v_us_3678_,
                                                );
                                                v___x_3686_ = l_Lean_mkAppB(
                                                    v___x_3685_,
                                                    v___x_3683_,
                                                    v___x_3644_,
                                                );
                                                v___x_3687_ = lean_box(0);
                                                if v_isShared_3665_ == 0 {
                                                    lean_ctor_set_tag(v___x_3664_, 1);
                                                    lean_ctor_set(v___x_3664_, 1, v___x_3687_);
                                                    lean_ctor_set(v___x_3664_, 0, v___x_3686_);
                                                    v___x_3689_ = v___x_3664_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3691_ =
                                                        lean_alloc_ctor(1, 2, (0) as u32);
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_3691_,
                                                        0,
                                                        v___x_3686_,
                                                    );
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_3691_,
                                                        1,
                                                        v___x_3687_,
                                                    );
                                                    v___x_3689_ = v_reuseFailAlloc_3691_;
                                                    state = 13;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec(v_us_3678_);
                                                lean_del_object(v___x_3664_);
                                                lean_dec(v_snd_3662_);
                                                lean_dec(v___x_3644_);
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_del_object(v___x_3664_);
                                        lean_dec(v_snd_3662_);
                                        lean_dec(v___x_3644_);
                                        state = 5;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_3664_);
                                    lean_dec(v_snd_3662_);
                                    lean_dec(v___x_3644_);
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_3664_);
                                lean_dec(v_snd_3662_);
                                lean_dec(v___x_3644_);
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            13 => {
                v___x_3690_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3690_, 0, v___x_3689_);
                return v___x_3690_;
            }
            14 => {
                v_str_3720_ = lean_ctor_get(v_fst_3713_, 1);
                lean_inc_ref(v_str_3720_);
                lean_dec_ref_known(v_fst_3713_, 2);
                v_str_3721_ = lean_ctor_get(v_pre_3714_, 1);
                lean_inc_ref(v_str_3721_);
                lean_dec_ref_known(v_pre_3714_, 2);
                v___x_3722_ = lean_string_dec_eq(v_str_3721_, v___x_3694_);
                lean_dec_ref(v_str_3721_);
                if v___x_3722_ == 0 {
                    lean_dec_ref(v_str_3720_);
                    lean_del_object(v___x_3718_);
                    lean_dec(v_snd_3716_);
                    lean_dec(v___x_3711_);
                    lean_del_object(v___x_3651_);
                    lean_del_object(v___x_3586_);
                    state = 11;
                    continue;
                } else {
                    v___x_3723_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__5;
                    v___x_3724_ = lean_string_dec_eq(v_str_3720_, v___x_3723_);
                    lean_dec_ref(v_str_3720_);
                    if v___x_3724_ == 0 {
                        lean_del_object(v___x_3718_);
                        lean_dec(v_snd_3716_);
                        lean_dec(v___x_3711_);
                        lean_del_object(v___x_3651_);
                        lean_del_object(v___x_3586_);
                        state = 11;
                        continue;
                    } else {
                        v___x_3725_ = lean_array_get_size(v_snd_3716_);
                        v___x_3726_ = lean_nat_dec_eq(v___x_3725_, v___x_3641_);
                        if v___x_3726_ == 0 {
                            lean_del_object(v___x_3718_);
                            lean_dec(v_snd_3716_);
                            lean_dec(v___x_3711_);
                            lean_del_object(v___x_3651_);
                            lean_del_object(v___x_3586_);
                            state = 11;
                            continue;
                        } else {
                            v___x_3727_ = lean_array_fget(v_snd_3716_, v___x_3655_);
                            lean_inc(v___x_3727_);
                            v___x_3728_ = l_Lean_Elab_Tactic_Omega_natCast_x3f(v___x_3727_);
                            if lean_obj_tag(v___x_3728_) == 0 {
                                lean_dec(v___x_3727_);
                                lean_del_object(v___x_3718_);
                                lean_dec(v_snd_3716_);
                                lean_dec(v___x_3711_);
                                lean_dec(v___x_3656_);
                                lean_del_object(v___x_3651_);
                                lean_dec(v___x_3644_);
                                lean_del_object(v___x_3586_);
                                state = 6;
                                continue;
                            } else {
                                v_val_3729_ = lean_ctor_get(v___x_3728_, 0);
                                lean_inc(v_val_3729_);
                                lean_dec_ref_known(v___x_3728_, 1);
                                v___x_3730_ = lean_nat_dec_eq(v_val_3729_, v___x_3702_);
                                lean_dec(v_val_3729_);
                                if v___x_3730_ == 0 {
                                    v___x_3731_ =
                                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__22;
                                    v___x_3732_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23_once), _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__23);
                                    if v_isShared_3719_ == 0 {
                                        lean_ctor_set_tag(v___x_3718_, 1);
                                        lean_ctor_set(v___x_3718_, 1, v_us_3706_);
                                        lean_ctor_set(v___x_3718_, 0, v___x_3732_);
                                        v___x_3734_ = v___x_3718_;
                                        state = 15;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3732_);
                                        lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_us_3706_);
                                        v___x_3734_ = v_reuseFailAlloc_3794_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_3727_);
                                    lean_del_object(v___x_3718_);
                                    lean_dec(v_snd_3716_);
                                    lean_dec(v___x_3711_);
                                    lean_dec(v___x_3656_);
                                    lean_del_object(v___x_3651_);
                                    lean_dec(v___x_3644_);
                                    lean_del_object(v___x_3586_);
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            15 => {
                lean_inc_ref(v___x_3734_);
                v___x_3735_ = l_Lean_Expr_const___override(v___x_3731_, v___x_3734_);
                v___x_3736_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__24;
                v___x_3737_ = l_Lean_Expr_const___override(v___x_3736_, v_us_3706_);
                v___x_3738_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__26;
                v___x_3739_ = l_Lean_Expr_const___override(v___x_3738_, v_us_3706_);
                v___x_3740_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__27,
                );
                lean_inc(v___x_3727_);
                v_b__pos_3741_ = l_Lean_mkApp4(
                    v___x_3735_,
                    v___x_3737_,
                    v___x_3739_,
                    v___x_3740_,
                    v___x_3727_,
                );
                v___x_3742_ = l_Lean_Meta_mkDecideProof(
                    v_b__pos_3741_,
                    v_a_3557_,
                    v_a_3558_,
                    v_a_3559_,
                    v_a_3560_,
                );
                if lean_obj_tag(v___x_3742_) == 0 {
                    v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
                    v_isSharedCheck_3785_ = (!lean_is_exclusive(v___x_3742_)) as u8;
                    if v_isSharedCheck_3785_ == 0 {
                        v___x_3745_ = v___x_3742_;
                        v_isShared_3746_ = v_isSharedCheck_3785_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_3743_);
                        lean_dec(v___x_3742_);
                        v___x_3745_ = lean_box(0);
                        v_isShared_3746_ = v_isSharedCheck_3785_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3734_);
                    lean_dec(v___x_3727_);
                    lean_dec(v_snd_3716_);
                    lean_dec(v___x_3711_);
                    lean_dec(v___x_3656_);
                    lean_del_object(v___x_3651_);
                    lean_dec(v___x_3644_);
                    lean_del_object(v___x_3586_);
                    v_a_3786_ = lean_ctor_get(v___x_3742_, 0);
                    v_isSharedCheck_3793_ = (!lean_is_exclusive(v___x_3742_)) as u8;
                    if v_isSharedCheck_3793_ == 0 {
                        v___x_3788_ = v___x_3742_;
                        v_isShared_3789_ = v_isSharedCheck_3793_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_3786_);
                        lean_dec(v___x_3742_);
                        v___x_3788_ = lean_box(0);
                        v_isShared_3789_ = v_isSharedCheck_3793_;
                        state = 21;
                        continue;
                    }
                }
            }
            16 => {
                v___x_3747_ = lean_array_fget(v_snd_3716_, v___x_3643_);
                lean_dec(v_snd_3716_);
                v___x_3748_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__29;
                v___x_3749_ = l_Lean_Expr_const___override(v___x_3748_, v_us_3706_);
                v___x_3750_ = l_Lean_mkApp3(v___x_3749_, v___x_3727_, v___x_3747_, v_a_3743_);
                v___x_3751_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__31;
                v___x_3752_ = l_Lean_Expr_const___override(v___x_3751_, v_us_3706_);
                v___x_3753_ = l_Lean_mkAppB(v___x_3752_, v___x_3711_, v___x_3750_);
                v___x_3754_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__33;
                v___x_3755_ = l_Lean_Expr_const___override(v___x_3754_, v_us_3706_);
                v___x_3756_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__35;
                v___x_3757_ = l_Lean_Expr_const___override(v___x_3756_, v_us_3706_);
                v___x_3775_ = lean_uint8_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__39,
                );
                if v___x_3775_ == 0 {
                    v___x_3776_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__42;
                    v___x_3777_ = l_Lean_Expr_const___override(v___x_3776_, v___x_3734_);
                    v___x_3778_ = l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__1;
                    v___x_3779_ = l_Lean_Expr_const___override(v___x_3778_, v_us_3706_);
                    v___x_3780_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__44;
                    v___x_3781_ = l_Lean_Expr_const___override(v___x_3780_, v_us_3706_);
                    v___x_3782_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__47,
                    );
                    v___x_3783_ = l_Lean_mkApp3(v___x_3777_, v___x_3779_, v___x_3781_, v___x_3782_);
                    v___y_3759_ = v___x_3783_;
                    state = 17;
                    continue;
                } else {
                    lean_dec_ref(v___x_3734_);
                    v___x_3784_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__49,
                    );
                    v___y_3759_ = v___x_3784_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                lean_inc_ref(v___x_3753_);
                lean_inc_n(v___x_3644_, 2);
                v___x_3760_ = l_Lean_mkApp3(v___x_3757_, v___x_3644_, v___y_3759_, v___x_3753_);
                lean_inc(v___x_3656_);
                v___x_3761_ = l_Lean_mkApp3(v___x_3755_, v___x_3656_, v___x_3644_, v___x_3760_);
                v___x_3762_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__37;
                v___x_3763_ = l_Lean_Expr_const___override(v___x_3762_, v_us_3706_);
                v___x_3764_ = l_Lean_mkApp3(v___x_3763_, v___x_3656_, v___x_3644_, v___x_3753_);
                v___x_3765_ = lean_box(0);
                if v_isShared_3652_ == 0 {
                    lean_ctor_set_tag(v___x_3651_, 1);
                    lean_ctor_set(v___x_3651_, 1, v___x_3765_);
                    lean_ctor_set(v___x_3651_, 0, v___x_3764_);
                    v___x_3767_ = v___x_3651_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 0, v___x_3764_);
                    lean_ctor_set(v_reuseFailAlloc_3774_, 1, v___x_3765_);
                    v___x_3767_ = v_reuseFailAlloc_3774_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3587_ == 0 {
                    lean_ctor_set_tag(v___x_3586_, 1);
                    lean_ctor_set(v___x_3586_, 1, v___x_3767_);
                    lean_ctor_set(v___x_3586_, 0, v___x_3761_);
                    v___x_3769_ = v___x_3586_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3761_);
                    lean_ctor_set(v_reuseFailAlloc_3773_, 1, v___x_3767_);
                    v___x_3769_ = v_reuseFailAlloc_3773_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3746_ == 0 {
                    lean_ctor_set(v___x_3745_, 0, v___x_3769_);
                    v___x_3771_ = v___x_3745_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3772_, 0, v___x_3769_);
                    v___x_3771_ = v_reuseFailAlloc_3772_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3771_;
            }
            21 => {
                if v_isShared_3789_ == 0 {
                    v___x_3791_ = v___x_3788_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3786_);
                    v___x_3791_ = v_reuseFailAlloc_3792_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3791_;
            }
            23 => {
                lean_inc(v___x_3801_);
                lean_inc_ref(v___y_3812_);
                v_b__pos_3813_ = l_Lean_mkApp4(
                    v___x_3808_,
                    v___x_3809_,
                    v___x_3810_,
                    v___y_3812_,
                    v___x_3801_,
                );
                v___x_3814_ = l_Lean_Meta_mkDecideProof(
                    v_b__pos_3813_,
                    v_a_3557_,
                    v_a_3558_,
                    v_a_3559_,
                    v_a_3560_,
                );
                if lean_obj_tag(v___x_3814_) == 0 {
                    v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
                    v_isSharedCheck_3836_ = (!lean_is_exclusive(v___x_3814_)) as u8;
                    if v_isSharedCheck_3836_ == 0 {
                        v___x_3817_ = v___x_3814_;
                        v_isShared_3818_ = v_isSharedCheck_3836_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_3815_);
                        lean_dec(v___x_3814_);
                        v___x_3817_ = lean_box(0);
                        v_isShared_3818_ = v_isSharedCheck_3836_;
                        state = 24;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3806_);
                    lean_dec(v___x_3801_);
                    lean_dec(v___x_3656_);
                    lean_del_object(v___x_3651_);
                    lean_dec(v___x_3644_);
                    lean_del_object(v___x_3586_);
                    v_a_3837_ = lean_ctor_get(v___x_3814_, 0);
                    v_isSharedCheck_3844_ = (!lean_is_exclusive(v___x_3814_)) as u8;
                    if v_isSharedCheck_3844_ == 0 {
                        v___x_3839_ = v___x_3814_;
                        v_isShared_3840_ = v_isSharedCheck_3844_;
                        state = 28;
                        continue;
                    } else {
                        lean_inc(v_a_3837_);
                        lean_dec(v___x_3814_);
                        v___x_3839_ = lean_box(0);
                        v_isShared_3840_ = v_isSharedCheck_3844_;
                        state = 28;
                        continue;
                    }
                }
            }
            24 => {
                v___x_3819_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__57,
                );
                v___x_3820_ = l_Lean_mkApp3(v___x_3819_, v___x_3801_, v___x_3806_, v_a_3815_);
                v___x_3821_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__58,
                );
                v___x_3822_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__59,
                );
                lean_inc_ref(v___x_3820_);
                lean_inc_ref(v___y_3812_);
                lean_inc_n(v___x_3644_, 2);
                v___x_3823_ = l_Lean_mkApp3(v___x_3822_, v___x_3644_, v___y_3812_, v___x_3820_);
                lean_inc(v___x_3656_);
                v___x_3824_ = l_Lean_mkApp3(v___x_3821_, v___x_3656_, v___x_3644_, v___x_3823_);
                v___x_3825_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__60,
                );
                v___x_3826_ = l_Lean_mkApp3(v___x_3825_, v___x_3656_, v___x_3644_, v___x_3820_);
                if v_isShared_3652_ == 0 {
                    lean_ctor_set_tag(v___x_3651_, 1);
                    lean_ctor_set(v___x_3651_, 1, v___x_3807_);
                    lean_ctor_set(v___x_3651_, 0, v___x_3826_);
                    v___x_3828_ = v___x_3651_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3826_);
                    lean_ctor_set(v_reuseFailAlloc_3835_, 1, v___x_3807_);
                    v___x_3828_ = v_reuseFailAlloc_3835_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_3587_ == 0 {
                    lean_ctor_set_tag(v___x_3586_, 1);
                    lean_ctor_set(v___x_3586_, 1, v___x_3828_);
                    lean_ctor_set(v___x_3586_, 0, v___x_3824_);
                    v___x_3830_ = v___x_3586_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3824_);
                    lean_ctor_set(v_reuseFailAlloc_3834_, 1, v___x_3828_);
                    v___x_3830_ = v_reuseFailAlloc_3834_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_3818_ == 0 {
                    lean_ctor_set(v___x_3817_, 0, v___x_3830_);
                    v___x_3832_ = v___x_3817_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3833_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
                    v___x_3832_ = v_reuseFailAlloc_3833_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3832_;
            }
            28 => {
                if v_isShared_3840_ == 0 {
                    v___x_3842_ = v___x_3839_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
                    v___x_3842_ = v_reuseFailAlloc_3843_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3842_;
            }
            30 => {
                lean_inc_ref(v___y_3867_);
                lean_inc(v___x_3856_);
                v_ne__zero_3868_ =
                    l_Lean_mkApp3(v___x_3864_, v___x_3865_, v___x_3856_, v___y_3867_);
                v___x_3869_ = l_Lean_Meta_mkDecideProof(
                    v_ne__zero_3868_,
                    v_a_3557_,
                    v_a_3558_,
                    v_a_3559_,
                    v_a_3560_,
                );
                if lean_obj_tag(v___x_3869_) == 0 {
                    v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
                    lean_inc(v_a_3870_);
                    lean_dec_ref_known(v___x_3869_, 1);
                    v___x_3871_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__51,
                    );
                    v___x_3872_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54_once
                        ),
                        _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__54,
                    );
                    lean_inc(v___x_3856_);
                    lean_inc_ref(v___y_3867_);
                    v_pos_3873_ = l_Lean_mkApp4(
                        v___x_3871_,
                        v___x_3865_,
                        v___x_3872_,
                        v___y_3867_,
                        v___x_3856_,
                    );
                    v___x_3874_ = l_Lean_Meta_mkDecideProof(
                        v_pos_3873_,
                        v_a_3557_,
                        v_a_3558_,
                        v_a_3559_,
                        v_a_3560_,
                    );
                    if lean_obj_tag(v___x_3874_) == 0 {
                        v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
                        v_isSharedCheck_3890_ = (!lean_is_exclusive(v___x_3874_)) as u8;
                        if v_isSharedCheck_3890_ == 0 {
                            v___x_3877_ = v___x_3874_;
                            v_isShared_3878_ = v_isSharedCheck_3890_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_3875_);
                            lean_dec(v___x_3874_);
                            v___x_3877_ = lean_box(0);
                            v_isShared_3878_ = v_isSharedCheck_3890_;
                            state = 31;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3870_);
                        lean_dec(v___x_3862_);
                        lean_dec(v___x_3856_);
                        lean_del_object(v___x_3586_);
                        v_a_3891_ = lean_ctor_get(v___x_3874_, 0);
                        v_isSharedCheck_3898_ = (!lean_is_exclusive(v___x_3874_)) as u8;
                        if v_isSharedCheck_3898_ == 0 {
                            v___x_3893_ = v___x_3874_;
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_a_3891_);
                            lean_dec(v___x_3874_);
                            v___x_3893_ = lean_box(0);
                            v_isShared_3894_ = v_isSharedCheck_3898_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3862_);
                    lean_dec(v___x_3856_);
                    lean_del_object(v___x_3586_);
                    v_a_3899_ = lean_ctor_get(v___x_3869_, 0);
                    v_isSharedCheck_3906_ = (!lean_is_exclusive(v___x_3869_)) as u8;
                    if v_isSharedCheck_3906_ == 0 {
                        v___x_3901_ = v___x_3869_;
                        v_isShared_3902_ = v_isSharedCheck_3906_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_3899_);
                        lean_dec(v___x_3869_);
                        v___x_3901_ = lean_box(0);
                        v_isShared_3902_ = v_isSharedCheck_3906_;
                        state = 36;
                        continue;
                    }
                }
            }
            31 => {
                v___x_3879_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__71,
                );
                lean_inc(v___x_3856_);
                lean_inc(v___x_3862_);
                v___x_3880_ = l_Lean_mkApp3(v___x_3879_, v___x_3862_, v___x_3856_, v_a_3870_);
                v___x_3881_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74_once
                    ),
                    _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__74,
                );
                v___x_3882_ = l_Lean_mkApp3(v___x_3881_, v___x_3862_, v___x_3856_, v_a_3875_);
                if v_isShared_3587_ == 0 {
                    lean_ctor_set_tag(v___x_3586_, 1);
                    lean_ctor_set(v___x_3586_, 1, v___x_3863_);
                    lean_ctor_set(v___x_3586_, 0, v___x_3882_);
                    v___x_3884_ = v___x_3586_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3889_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3882_);
                    lean_ctor_set(v_reuseFailAlloc_3889_, 1, v___x_3863_);
                    v___x_3884_ = v_reuseFailAlloc_3889_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                v___x_3885_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3885_, 0, v___x_3880_);
                lean_ctor_set(v___x_3885_, 1, v___x_3884_);
                if v_isShared_3878_ == 0 {
                    lean_ctor_set(v___x_3877_, 0, v___x_3885_);
                    v___x_3887_ = v___x_3877_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_3888_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3888_, 0, v___x_3885_);
                    v___x_3887_ = v_reuseFailAlloc_3888_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_3887_;
            }
            34 => {
                if v_isShared_3894_ == 0 {
                    v___x_3896_ = v___x_3893_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
                    v___x_3896_ = v_reuseFailAlloc_3897_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3896_;
            }
            36 => {
                if v_isShared_3902_ == 0 {
                    v___x_3904_ = v___x_3901_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_a_3899_);
                    v___x_3904_ = v_reuseFailAlloc_3905_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3904_;
            }
            38 => {
                v___x_3925_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__76;
                v___x_3926_ = l_Lean_Expr_const___override(v___x_3925_, v_us_3919_);
                v___x_3927_ = l_Lean_Expr_app___override(v___x_3926_, v___y_3923_);
                v___x_3928_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                    v___x_3927_,
                    v___y_3924_,
                );
                if v___x_3928_ == 0 {
                    if v_isShared_3587_ == 0 {
                        lean_ctor_set_tag(v___x_3586_, 1);
                        lean_ctor_set(v___x_3586_, 1, v___y_3924_);
                        lean_ctor_set(v___x_3586_, 0, v___x_3927_);
                        v___x_3930_ = v___x_3586_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3932_, 0, v___x_3927_);
                        lean_ctor_set(v_reuseFailAlloc_3932_, 1, v___y_3924_);
                        v___x_3930_ = v_reuseFailAlloc_3932_;
                        state = 39;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3927_);
                    lean_del_object(v___x_3586_);
                    v___x_3933_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3933_, 0, v___y_3924_);
                    return v___x_3933_;
                }
            }
            39 => {
                v___x_3931_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3931_, 0, v___x_3930_);
                return v___x_3931_;
            }
            40 => {
                v___x_3946_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__81;
                v___x_3947_ = l_Lean_Expr_const___override(v___x_3946_, v_us_3919_);
                v___x_3948_ = l_Lean_mkAppB(v___x_3947_, v_n_3944_, v_x_3945_);
                v___x_3949_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                    v___x_3948_,
                    v_r_3942_,
                );
                if v___x_3949_ == 0 {
                    v___x_3950_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3950_, 0, v___x_3948_);
                    lean_ctor_set(v___x_3950_, 1, v_r_3942_);
                    v___x_3951_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3951_, 0, v___x_3950_);
                    return v___x_3951_;
                } else {
                    lean_dec_ref(v___x_3948_);
                    v___x_3952_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3952_, 0, v_r_3942_);
                    return v___x_3952_;
                }
            }
            41 => {
                v___x_3956_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__83;
                v___x_3957_ = l_Lean_Expr_const___override(v___x_3956_, v_us_3919_);
                v___x_3958_ = l_Lean_mkAppB(v___x_3957_, v_n_3954_, v_i_3955_);
                v___x_3959_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                    v___x_3958_,
                    v_r_3942_,
                );
                if v___x_3959_ == 0 {
                    v___x_3960_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3960_, 0, v___x_3958_);
                    lean_ctor_set(v___x_3960_, 1, v_r_3942_);
                    v___x_3961_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3961_, 0, v___x_3960_);
                    return v___x_3961_;
                } else {
                    lean_dec_ref(v___x_3958_);
                    v___x_3962_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3962_, 0, v_r_3942_);
                    return v___x_3962_;
                }
            }
            42 => {
                v___x_3965_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__85;
                v___x_3966_ = l_Lean_Expr_const___override(v___x_3965_, v_us_3919_);
                lean_inc_ref(v_x_3964_);
                v___x_3967_ = l_Lean_Expr_app___override(v___x_3966_, v_x_3964_);
                v___x_3968_ = l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                    v___x_3967_,
                    v_r_3942_,
                );
                if v___x_3968_ == 0 {
                    v___x_3969_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3969_, 0, v___x_3967_);
                    lean_ctor_set(v___x_3969_, 1, v_r_3942_);
                    v___y_3923_ = v_x_3964_;
                    v___y_3924_ = v___x_3969_;
                    state = 38;
                    continue;
                } else {
                    lean_dec_ref(v___x_3967_);
                    v___y_3923_ = v_x_3964_;
                    v___y_3924_ = v_r_3942_;
                    state = 38;
                    continue;
                }
            }
            43 => {
                v_str_3978_ = lean_ctor_get(v_fst_3971_, 1);
                lean_inc_ref(v_str_3978_);
                lean_dec_ref_known(v_fst_3971_, 2);
                v_str_3979_ = lean_ctor_get(v_pre_3972_, 1);
                lean_inc_ref(v_str_3979_);
                lean_dec_ref_known(v_pre_3972_, 2);
                v___x_3980_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__2;
                v___x_3981_ = lean_string_dec_eq(v_str_3979_, v___x_3980_);
                if v___x_3981_ == 0 {
                    lean_del_object(v___x_3976_);
                    v___x_3982_ = lean_string_dec_eq(v_str_3979_, v___x_3921_);
                    if v___x_3982_ == 0 {
                        lean_del_object(v___x_3586_);
                        v___x_3983_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__82;
                        v___x_3984_ = lean_string_dec_eq(v_str_3979_, v___x_3983_);
                        if v___x_3984_ == 0 {
                            v___x_3985_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__79;
                            v___x_3986_ = lean_string_dec_eq(v_str_3979_, v___x_3985_);
                            lean_dec_ref(v_str_3979_);
                            if v___x_3986_ == 0 {
                                lean_dec_ref(v_str_3978_);
                                lean_dec(v_snd_3974_);
                                v___x_3987_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3987_, 0, v_r_3942_);
                                return v___x_3987_;
                            } else {
                                v___x_3988_ =
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__86;
                                v___x_3989_ = lean_string_dec_eq(v_str_3978_, v___x_3988_);
                                lean_dec_ref(v_str_3978_);
                                if v___x_3989_ == 0 {
                                    lean_dec(v_snd_3974_);
                                    v___x_3990_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_3990_, 0, v_r_3942_);
                                    return v___x_3990_;
                                } else {
                                    v___x_3991_ = lean_array_get_size(v_snd_3974_);
                                    v___x_3992_ = lean_nat_dec_eq(v___x_3991_, v___x_3936_);
                                    if v___x_3992_ == 0 {
                                        lean_dec(v_snd_3974_);
                                        v___x_3993_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v___x_3993_, 0, v_r_3942_);
                                        return v___x_3993_;
                                    } else {
                                        v___x_3994_ = lean_array_fget(v_snd_3974_, v___x_3915_);
                                        v___x_3995_ = lean_unsigned_to_nat(1);
                                        v___x_3996_ = lean_array_fget(v_snd_3974_, v___x_3995_);
                                        lean_dec(v_snd_3974_);
                                        v_n_3944_ = v___x_3994_;
                                        v_x_3945_ = v___x_3996_;
                                        state = 40;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_str_3979_);
                            v___x_3997_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__87;
                            v___x_3998_ = lean_string_dec_eq(v_str_3978_, v___x_3997_);
                            lean_dec_ref(v_str_3978_);
                            if v___x_3998_ == 0 {
                                lean_dec(v_snd_3974_);
                                v___x_3999_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_3999_, 0, v_r_3942_);
                                return v___x_3999_;
                            } else {
                                v___x_4000_ = lean_array_get_size(v_snd_3974_);
                                v___x_4001_ = lean_nat_dec_eq(v___x_4000_, v___x_3936_);
                                if v___x_4001_ == 0 {
                                    lean_dec(v_snd_3974_);
                                    v___x_4002_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_4002_, 0, v_r_3942_);
                                    return v___x_4002_;
                                } else {
                                    v___x_4003_ = lean_array_fget(v_snd_3974_, v___x_3915_);
                                    v___x_4004_ = lean_unsigned_to_nat(1);
                                    v___x_4005_ = lean_array_fget(v_snd_3974_, v___x_4004_);
                                    lean_dec(v_snd_3974_);
                                    v_n_3954_ = v___x_4003_;
                                    v_i_3955_ = v___x_4005_;
                                    state = 41;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_str_3979_);
                        v___x_4006_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__88;
                        v___x_4007_ = lean_string_dec_eq(v_str_3978_, v___x_4006_);
                        lean_dec_ref(v_str_3978_);
                        if v___x_4007_ == 0 {
                            lean_dec(v_snd_3974_);
                            lean_del_object(v___x_3586_);
                            v___x_4008_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4008_, 0, v_r_3942_);
                            return v___x_4008_;
                        } else {
                            v___x_4009_ = lean_array_get_size(v_snd_3974_);
                            v___x_4010_ = lean_unsigned_to_nat(1);
                            v___x_4011_ = lean_nat_dec_eq(v___x_4009_, v___x_4010_);
                            if v___x_4011_ == 0 {
                                lean_dec(v_snd_3974_);
                                lean_del_object(v___x_3586_);
                                v___x_4012_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4012_, 0, v_r_3942_);
                                return v___x_4012_;
                            } else {
                                v___x_4013_ = lean_array_fget(v_snd_3974_, v___x_3915_);
                                lean_dec(v_snd_3974_);
                                v_x_3964_ = v___x_4013_;
                                state = 42;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_str_3979_);
                    lean_del_object(v___x_3586_);
                    v___x_4014_ = l_Lean_Elab_Tactic_Omega_groundNat_x3f___closed__9;
                    v___x_4015_ = lean_string_dec_eq(v_str_3978_, v___x_4014_);
                    lean_dec_ref(v_str_3978_);
                    if v___x_4015_ == 0 {
                        lean_del_object(v___x_3976_);
                        lean_dec(v_snd_3974_);
                        v___x_4016_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4016_, 0, v_r_3942_);
                        return v___x_4016_;
                    } else {
                        v___x_4017_ = lean_array_get_size(v_snd_3974_);
                        v___x_4018_ = lean_unsigned_to_nat(6);
                        v___x_4019_ = lean_nat_dec_eq(v___x_4017_, v___x_4018_);
                        if v___x_4019_ == 0 {
                            lean_del_object(v___x_3976_);
                            lean_dec(v_snd_3974_);
                            v___x_4020_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4020_, 0, v_r_3942_);
                            return v___x_4020_;
                        } else {
                            v___x_4021_ = lean_unsigned_to_nat(4);
                            v___x_4022_ = lean_array_fget(v_snd_3974_, v___x_4021_);
                            v___x_4023_ = lean_unsigned_to_nat(5);
                            v___x_4024_ = lean_array_fget(v_snd_3974_, v___x_4023_);
                            lean_dec(v_snd_3974_);
                            v___x_4025_ =
                                l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__90;
                            v___x_4026_ = l_Lean_Expr_const___override(v___x_4025_, v_us_3919_);
                            v___x_4027_ = l_Lean_mkAppB(v___x_4026_, v___x_4022_, v___x_4024_);
                            v___x_4028_ =
                                l_List_elem___at___00Lean_Elab_Tactic_Omega_analyzeAtom_spec__0(
                                    v___x_4027_,
                                    v_r_3942_,
                                );
                            if v___x_4028_ == 0 {
                                if v_isShared_3977_ == 0 {
                                    lean_ctor_set_tag(v___x_3976_, 1);
                                    lean_ctor_set(v___x_3976_, 1, v_r_3942_);
                                    lean_ctor_set(v___x_3976_, 0, v___x_4027_);
                                    v___x_4030_ = v___x_3976_;
                                    state = 44;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 2, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4027_);
                                    lean_ctor_set(v_reuseFailAlloc_4032_, 1, v_r_3942_);
                                    v___x_4030_ = v_reuseFailAlloc_4032_;
                                    state = 44;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_4027_);
                                lean_del_object(v___x_3976_);
                                v___x_4033_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_4033_, 0, v_r_3942_);
                                return v___x_4033_;
                            }
                        }
                    }
                }
            }
            44 => {
                v___x_4031_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4031_, 0, v___x_4030_);
                return v___x_4031_;
            }
            45 => {
                v_str_4087_ = lean_ctor_get(v_fst_3581_, 1);
                lean_inc_ref(v_str_4087_);
                lean_dec_ref_known(v_fst_3581_, 2);
                v___x_4088_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__91;
                v___x_4089_ = lean_string_dec_eq(v_str_4087_, v___x_4088_);
                lean_dec_ref(v_str_4087_);
                if v___x_4089_ == 0 {
                    lean_del_object(v___x_4085_);
                    lean_dec(v_snd_4083_);
                    state = 3;
                    continue;
                } else {
                    v___x_4090_ = lean_array_get_size(v_snd_4083_);
                    v___x_4091_ = lean_unsigned_to_nat(5);
                    v___x_4092_ = lean_nat_dec_eq(v___x_4090_, v___x_4091_);
                    if v___x_4092_ == 0 {
                        lean_del_object(v___x_4085_);
                        lean_dec(v_snd_4083_);
                        state = 3;
                        continue;
                    } else {
                        v___x_4093_ = lean_unsigned_to_nat(0);
                        v___x_4094_ = lean_array_fget(v_snd_4083_, v___x_4093_);
                        v___x_4095_ = lean_box(0);
                        v___x_4096_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2_once
                            ),
                            _init_l_Lean_Elab_Tactic_Omega_atomsList___redArg___closed__2,
                        );
                        v___x_4097_ = lean_expr_eqv(v___x_4094_, v___x_4096_);
                        if v___x_4097_ == 0 {
                            lean_dec(v___x_4094_);
                            lean_del_object(v___x_4085_);
                            lean_dec(v_snd_4083_);
                            v___x_4098_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_4098_, 0, v___x_4095_);
                            return v___x_4098_;
                        } else {
                            v___x_4099_ = lean_unsigned_to_nat(1);
                            v___x_4100_ = lean_array_fget(v_snd_4083_, v___x_4099_);
                            v___x_4101_ = lean_unsigned_to_nat(2);
                            v___x_4102_ = lean_array_fget(v_snd_4083_, v___x_4101_);
                            v___x_4103_ = lean_unsigned_to_nat(3);
                            v___x_4104_ = lean_array_fget(v_snd_4083_, v___x_4103_);
                            v___x_4105_ = lean_unsigned_to_nat(4);
                            v___x_4106_ = lean_array_fget(v_snd_4083_, v___x_4105_);
                            lean_dec(v_snd_4083_);
                            v___x_4107_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94_once
                                ),
                                _init_l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___closed__94,
                            );
                            v___x_4108_ = l_Lean_mkApp5(
                                v___x_4107_,
                                v___x_4094_,
                                v___x_4100_,
                                v___x_4102_,
                                v___x_4104_,
                                v___x_4106_,
                            );
                            if v_isShared_4086_ == 0 {
                                lean_ctor_set_tag(v___x_4085_, 1);
                                lean_ctor_set(v___x_4085_, 1, v___x_4095_);
                                lean_ctor_set(v___x_4085_, 0, v___x_4108_);
                                v___x_4110_ = v___x_4085_;
                                state = 46;
                                continue;
                            } else {
                                v_reuseFailAlloc_4112_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4108_);
                                lean_ctor_set(v_reuseFailAlloc_4112_, 1, v___x_4095_);
                                v___x_4110_ = v_reuseFailAlloc_4112_;
                                state = 46;
                                continue;
                            }
                        }
                    }
                }
            }
            46 => {
                v___x_4111_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4111_, 0, v___x_4110_);
                return v___x_4111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg___boxed(
    mut v_e_4115_: *mut LeanObject,
    mut v_a_4116_: *mut LeanObject,
    mut v_a_4117_: *mut LeanObject,
    mut v_a_4118_: *mut LeanObject,
    mut v_a_4119_: *mut LeanObject,
    mut v_a_4120_: *mut LeanObject,
    mut v_a_4121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4122_: *mut LeanObject = core::ptr::null_mut();
    v_res_4122_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
        v_e_4115_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_, v_a_4120_,
    );
    lean_dec(v_a_4120_);
    lean_dec_ref(v_a_4119_);
    lean_dec(v_a_4118_);
    lean_dec_ref(v_a_4117_);
    lean_dec_ref(v_a_4116_);
    return v_res_4122_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom(
    mut v_e_4123_: *mut LeanObject,
    mut v_a_4124_: *mut LeanObject,
    mut v_a_4125_: *mut LeanObject,
    mut v_a_4126_: *mut LeanObject,
    mut v_a_4127_: u8,
    mut v_a_4128_: *mut LeanObject,
    mut v_a_4129_: *mut LeanObject,
    mut v_a_4130_: *mut LeanObject,
    mut v_a_4131_: *mut LeanObject,
    mut v_a_4132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    v___x_4134_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
        v_e_4123_, v_a_4126_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_,
    );
    return v___x_4134_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_analyzeAtom___boxed(
    mut v_e_4135_: *mut LeanObject,
    mut v_a_4136_: *mut LeanObject,
    mut v_a_4137_: *mut LeanObject,
    mut v_a_4138_: *mut LeanObject,
    mut v_a_4139_: *mut LeanObject,
    mut v_a_4140_: *mut LeanObject,
    mut v_a_4141_: *mut LeanObject,
    mut v_a_4142_: *mut LeanObject,
    mut v_a_4143_: *mut LeanObject,
    mut v_a_4144_: *mut LeanObject,
    mut v_a_4145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4146_: u8 = 0;
    let mut v_res_4147_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4146_ = (lean_unbox(v_a_4139_) as u8);
    v_res_4147_ = l_Lean_Elab_Tactic_Omega_analyzeAtom(
        v_e_4135_,
        v_a_4136_,
        v_a_4137_,
        v_a_4138_,
        v_a_boxed_4146_,
        v_a_4140_,
        v_a_4141_,
        v_a_4142_,
        v_a_4143_,
        v_a_4144_,
    );
    lean_dec(v_a_4144_);
    lean_dec_ref(v_a_4143_);
    lean_dec(v_a_4142_);
    lean_dec_ref(v_a_4141_);
    lean_dec(v_a_4140_);
    lean_dec_ref(v_a_4138_);
    lean_dec(v_a_4137_);
    lean_dec(v_a_4136_);
    return v_res_4147_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(
    mut v_a_4148_: *mut LeanObject,
    mut v_x_4149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4149_) == 0 {
                    v___x_4150_ = lean_box(0);
                    return v___x_4150_;
                } else {
                    v_key_4151_ = lean_ctor_get(v_x_4149_, 0);
                    v_value_4152_ = lean_ctor_get(v_x_4149_, 1);
                    v_tail_4153_ = lean_ctor_get(v_x_4149_, 2);
                    v___x_4154_ = lean_expr_eqv(v_key_4151_, v_a_4148_);
                    if v___x_4154_ == 0 {
                        v_x_4149_ = v_tail_4153_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_4152_);
                        v___x_4156_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4156_, 0, v_value_4152_);
                        return v___x_4156_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg___boxed(
    mut v_a_4157_: *mut LeanObject,
    mut v_x_4158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4159_: *mut LeanObject = core::ptr::null_mut();
    v_res_4159_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_4157_, v_x_4158_);
    lean_dec(v_x_4158_);
    lean_dec_ref(v_a_4157_);
    return v_res_4159_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(
    mut v_m_4160_: *mut LeanObject,
    mut v_a_4161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: u64 = 0;
    let mut v___x_4165_: u64 = 0;
    let mut v___x_4166_: u64 = 0;
    let mut v_fold_4167_: u64 = 0;
    let mut v___x_4168_: u64 = 0;
    let mut v___x_4169_: u64 = 0;
    let mut v___x_4170_: u64 = 0;
    let mut v___x_4171_: usize = 0;
    let mut v___x_4172_: usize = 0;
    let mut v___x_4173_: usize = 0;
    let mut v___x_4174_: usize = 0;
    let mut v___x_4175_: usize = 0;
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_4162_ = lean_ctor_get(v_m_4160_, 1);
    v___x_4163_ = lean_array_get_size(v_buckets_4162_);
    v___x_4164_ = l_Lean_Expr_hash(v_a_4161_);
    v___x_4165_ = 32u64;
    v___x_4166_ = lean_uint64_shift_right(v___x_4164_, v___x_4165_);
    v_fold_4167_ = lean_uint64_xor(v___x_4164_, v___x_4166_);
    v___x_4168_ = 16u64;
    v___x_4169_ = lean_uint64_shift_right(v_fold_4167_, v___x_4168_);
    v___x_4170_ = lean_uint64_xor(v_fold_4167_, v___x_4169_);
    v___x_4171_ = lean_uint64_to_usize(v___x_4170_);
    v___x_4172_ = lean_usize_of_nat(v___x_4163_);
    v___x_4173_ = 1usize;
    v___x_4174_ = lean_usize_sub(v___x_4172_, v___x_4173_);
    v___x_4175_ = lean_usize_land(v___x_4171_, v___x_4174_);
    v___x_4176_ = lean_array_uget_borrowed(v_buckets_4162_, v___x_4175_);
    v___x_4177_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_4161_, v___x_4176_);
    return v___x_4177_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg___boxed(
    mut v_m_4178_: *mut LeanObject,
    mut v_a_4179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4180_: *mut LeanObject = core::ptr::null_mut();
    v_res_4180_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_4178_, v_a_4179_);
    lean_dec_ref(v_a_4179_);
    lean_dec_ref(v_m_4178_);
    return v_res_4180_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(
    mut v_a_4181_: *mut LeanObject,
    mut v_x_4182_: *mut LeanObject,
) -> u8 {
    let mut v___x_4183_: u8 = 0;
    let mut v_key_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4182_) == 0 {
                    v___x_4183_ = 0;
                    return v___x_4183_;
                } else {
                    v_key_4184_ = lean_ctor_get(v_x_4182_, 0);
                    v_tail_4185_ = lean_ctor_get(v_x_4182_, 2);
                    v___x_4186_ = lean_expr_eqv(v_key_4184_, v_a_4181_);
                    if v___x_4186_ == 0 {
                        v_x_4182_ = v_tail_4185_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4186_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg___boxed(
    mut v_a_4188_: *mut LeanObject,
    mut v_x_4189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4190_: u8 = 0;
    let mut v_r_4191_: *mut LeanObject = core::ptr::null_mut();
    v_res_4190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_4188_, v_x_4189_);
    lean_dec(v_x_4189_);
    lean_dec_ref(v_a_4188_);
    v_r_4191_ = lean_box((v_res_4190_) as usize);
    return v_r_4191_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(
    mut v_x_4192_: *mut LeanObject,
    mut v_x_4193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: u64 = 0;
    let mut v___x_4202_: u64 = 0;
    let mut v___x_4203_: u64 = 0;
    let mut v_fold_4204_: u64 = 0;
    let mut v___x_4205_: u64 = 0;
    let mut v___x_4206_: u64 = 0;
    let mut v___x_4207_: u64 = 0;
    let mut v___x_4208_: usize = 0;
    let mut v___x_4209_: usize = 0;
    let mut v___x_4210_: usize = 0;
    let mut v___x_4211_: usize = 0;
    let mut v___x_4212_: usize = 0;
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4193_) == 0 {
                    return v_x_4192_;
                } else {
                    v_key_4194_ = lean_ctor_get(v_x_4193_, 0);
                    v_value_4195_ = lean_ctor_get(v_x_4193_, 1);
                    v_tail_4196_ = lean_ctor_get(v_x_4193_, 2);
                    v_isSharedCheck_4219_ = (!lean_is_exclusive(v_x_4193_)) as u8;
                    if v_isSharedCheck_4219_ == 0 {
                        v___x_4198_ = v_x_4193_;
                        v_isShared_4199_ = v_isSharedCheck_4219_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4196_);
                        lean_inc(v_value_4195_);
                        lean_inc(v_key_4194_);
                        lean_dec(v_x_4193_);
                        v___x_4198_ = lean_box(0);
                        v_isShared_4199_ = v_isSharedCheck_4219_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4200_ = lean_array_get_size(v_x_4192_);
                v___x_4201_ = l_Lean_Expr_hash(v_key_4194_);
                v___x_4202_ = 32u64;
                v___x_4203_ = lean_uint64_shift_right(v___x_4201_, v___x_4202_);
                v_fold_4204_ = lean_uint64_xor(v___x_4201_, v___x_4203_);
                v___x_4205_ = 16u64;
                v___x_4206_ = lean_uint64_shift_right(v_fold_4204_, v___x_4205_);
                v___x_4207_ = lean_uint64_xor(v_fold_4204_, v___x_4206_);
                v___x_4208_ = lean_uint64_to_usize(v___x_4207_);
                v___x_4209_ = lean_usize_of_nat(v___x_4200_);
                v___x_4210_ = 1usize;
                v___x_4211_ = lean_usize_sub(v___x_4209_, v___x_4210_);
                v___x_4212_ = lean_usize_land(v___x_4208_, v___x_4211_);
                v___x_4213_ = lean_array_uget_borrowed(v_x_4192_, v___x_4212_);
                lean_inc(v___x_4213_);
                if v_isShared_4199_ == 0 {
                    lean_ctor_set(v___x_4198_, 2, v___x_4213_);
                    v___x_4215_ = v___x_4198_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 0, v_key_4194_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 1, v_value_4195_);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 2, v___x_4213_);
                    v___x_4215_ = v_reuseFailAlloc_4218_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4216_ = lean_array_uset(v_x_4192_, v___x_4212_, v___x_4215_);
                v_x_4192_ = v___x_4216_;
                v_x_4193_ = v_tail_4196_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(
    mut v_i_4220_: *mut LeanObject,
    mut v_source_4221_: *mut LeanObject,
    mut v_target_4222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: u8 = 0;
    let mut v_es_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4223_ = lean_array_get_size(v_source_4221_);
                v___x_4224_ = lean_nat_dec_lt(v_i_4220_, v___x_4223_);
                if v___x_4224_ == 0 {
                    lean_dec_ref(v_source_4221_);
                    lean_dec(v_i_4220_);
                    return v_target_4222_;
                } else {
                    v_es_4225_ = lean_array_fget(v_source_4221_, v_i_4220_);
                    v___x_4226_ = lean_box(0);
                    v_source_4227_ = lean_array_fset(v_source_4221_, v_i_4220_, v___x_4226_);
                    v_target_4228_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_target_4222_, v_es_4225_);
                    v___x_4229_ = lean_unsigned_to_nat(1);
                    v___x_4230_ = lean_nat_add(v_i_4220_, v___x_4229_);
                    lean_dec(v_i_4220_);
                    v_i_4220_ = v___x_4230_;
                    v_source_4221_ = v_source_4227_;
                    v_target_4222_ = v_target_4228_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(
    mut v_data_4232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    v___x_4233_ = lean_array_get_size(v_data_4232_);
    v___x_4234_ = lean_unsigned_to_nat(2);
    v_nbuckets_4235_ = lean_nat_mul(v___x_4233_, v___x_4234_);
    v___x_4236_ = lean_unsigned_to_nat(0);
    v___x_4237_ = lean_box(0);
    v___x_4238_ = lean_mk_array(v_nbuckets_4235_, v___x_4237_);
    v___x_4239_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v___x_4236_, v_data_4232_, v___x_4238_);
    return v___x_4239_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(
    mut v_a_4240_: *mut LeanObject,
    mut v_b_4241_: *mut LeanObject,
    mut v_x_4242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4249_: u8 = 0;
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4242_) == 0 {
                    lean_dec(v_b_4241_);
                    lean_dec_ref(v_a_4240_);
                    return v_x_4242_;
                } else {
                    v_key_4243_ = lean_ctor_get(v_x_4242_, 0);
                    v_value_4244_ = lean_ctor_get(v_x_4242_, 1);
                    v_tail_4245_ = lean_ctor_get(v_x_4242_, 2);
                    v_isSharedCheck_4257_ = (!lean_is_exclusive(v_x_4242_)) as u8;
                    if v_isSharedCheck_4257_ == 0 {
                        v___x_4247_ = v_x_4242_;
                        v_isShared_4248_ = v_isSharedCheck_4257_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4245_);
                        lean_inc(v_value_4244_);
                        lean_inc(v_key_4243_);
                        lean_dec(v_x_4242_);
                        v___x_4247_ = lean_box(0);
                        v_isShared_4248_ = v_isSharedCheck_4257_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4249_ = lean_expr_eqv(v_key_4243_, v_a_4240_);
                if v___x_4249_ == 0 {
                    v___x_4250_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_4240_, v_b_4241_, v_tail_4245_);
                    if v_isShared_4248_ == 0 {
                        lean_ctor_set(v___x_4247_, 2, v___x_4250_);
                        v___x_4252_ = v___x_4247_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4253_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4253_, 0, v_key_4243_);
                        lean_ctor_set(v_reuseFailAlloc_4253_, 1, v_value_4244_);
                        lean_ctor_set(v_reuseFailAlloc_4253_, 2, v___x_4250_);
                        v___x_4252_ = v_reuseFailAlloc_4253_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_4244_);
                    lean_dec(v_key_4243_);
                    if v_isShared_4248_ == 0 {
                        lean_ctor_set(v___x_4247_, 1, v_b_4241_);
                        lean_ctor_set(v___x_4247_, 0, v_a_4240_);
                        v___x_4255_ = v___x_4247_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4240_);
                        lean_ctor_set(v_reuseFailAlloc_4256_, 1, v_b_4241_);
                        lean_ctor_set(v_reuseFailAlloc_4256_, 2, v_tail_4245_);
                        v___x_4255_ = v_reuseFailAlloc_4256_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4252_;
            }
            3 => {
                return v___x_4255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(
    mut v_m_4258_: *mut LeanObject,
    mut v_a_4259_: *mut LeanObject,
    mut v_b_4260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4265_: u8 = 0;
    let mut v___x_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: u64 = 0;
    let mut v___x_4268_: u64 = 0;
    let mut v___x_4269_: u64 = 0;
    let mut v_fold_4270_: u64 = 0;
    let mut v___x_4271_: u64 = 0;
    let mut v___x_4272_: u64 = 0;
    let mut v___x_4273_: u64 = 0;
    let mut v___x_4274_: usize = 0;
    let mut v___x_4275_: usize = 0;
    let mut v___x_4276_: usize = 0;
    let mut v___x_4277_: usize = 0;
    let mut v___x_4278_: usize = 0;
    let mut v_bkt_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: u8 = 0;
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v_val_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4261_ = lean_ctor_get(v_m_4258_, 0);
                v_buckets_4262_ = lean_ctor_get(v_m_4258_, 1);
                v_isSharedCheck_4305_ = (!lean_is_exclusive(v_m_4258_)) as u8;
                if v_isSharedCheck_4305_ == 0 {
                    v___x_4264_ = v_m_4258_;
                    v_isShared_4265_ = v_isSharedCheck_4305_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_4262_);
                    lean_inc(v_size_4261_);
                    lean_dec(v_m_4258_);
                    v___x_4264_ = lean_box(0);
                    v_isShared_4265_ = v_isSharedCheck_4305_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4266_ = lean_array_get_size(v_buckets_4262_);
                v___x_4267_ = l_Lean_Expr_hash(v_a_4259_);
                v___x_4268_ = 32u64;
                v___x_4269_ = lean_uint64_shift_right(v___x_4267_, v___x_4268_);
                v_fold_4270_ = lean_uint64_xor(v___x_4267_, v___x_4269_);
                v___x_4271_ = 16u64;
                v___x_4272_ = lean_uint64_shift_right(v_fold_4270_, v___x_4271_);
                v___x_4273_ = lean_uint64_xor(v_fold_4270_, v___x_4272_);
                v___x_4274_ = lean_uint64_to_usize(v___x_4273_);
                v___x_4275_ = lean_usize_of_nat(v___x_4266_);
                v___x_4276_ = 1usize;
                v___x_4277_ = lean_usize_sub(v___x_4275_, v___x_4276_);
                v___x_4278_ = lean_usize_land(v___x_4274_, v___x_4277_);
                v_bkt_4279_ = lean_array_uget_borrowed(v_buckets_4262_, v___x_4278_);
                v___x_4280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_4259_, v_bkt_4279_);
                if v___x_4280_ == 0 {
                    v___x_4281_ = lean_unsigned_to_nat(1);
                    v_size_x27_4282_ = lean_nat_add(v_size_4261_, v___x_4281_);
                    lean_dec(v_size_4261_);
                    lean_inc(v_bkt_4279_);
                    v___x_4283_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_4283_, 0, v_a_4259_);
                    lean_ctor_set(v___x_4283_, 1, v_b_4260_);
                    lean_ctor_set(v___x_4283_, 2, v_bkt_4279_);
                    v_buckets_x27_4284_ =
                        lean_array_uset(v_buckets_4262_, v___x_4278_, v___x_4283_);
                    v___x_4285_ = lean_unsigned_to_nat(4);
                    v___x_4286_ = lean_nat_mul(v_size_x27_4282_, v___x_4285_);
                    v___x_4287_ = lean_unsigned_to_nat(3);
                    v___x_4288_ = lean_nat_div(v___x_4286_, v___x_4287_);
                    lean_dec(v___x_4286_);
                    v___x_4289_ = lean_array_get_size(v_buckets_x27_4284_);
                    v___x_4290_ = lean_nat_dec_le(v___x_4288_, v___x_4289_);
                    lean_dec(v___x_4288_);
                    if v___x_4290_ == 0 {
                        v_val_4291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_buckets_x27_4284_);
                        if v_isShared_4265_ == 0 {
                            lean_ctor_set(v___x_4264_, 1, v_val_4291_);
                            lean_ctor_set(v___x_4264_, 0, v_size_x27_4282_);
                            v___x_4293_ = v___x_4264_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4294_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4294_, 0, v_size_x27_4282_);
                            lean_ctor_set(v_reuseFailAlloc_4294_, 1, v_val_4291_);
                            v___x_4293_ = v_reuseFailAlloc_4294_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_4265_ == 0 {
                            lean_ctor_set(v___x_4264_, 1, v_buckets_x27_4284_);
                            lean_ctor_set(v___x_4264_, 0, v_size_x27_4282_);
                            v___x_4296_ = v___x_4264_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_size_x27_4282_);
                            lean_ctor_set(v_reuseFailAlloc_4297_, 1, v_buckets_x27_4284_);
                            v___x_4296_ = v_reuseFailAlloc_4297_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_4279_);
                    v___x_4298_ = lean_box(0);
                    v_buckets_x27_4299_ =
                        lean_array_uset(v_buckets_4262_, v___x_4278_, v___x_4298_);
                    v___x_4300_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_4259_, v_b_4260_, v_bkt_4279_);
                    v___x_4301_ = lean_array_uset(v_buckets_x27_4299_, v___x_4278_, v___x_4300_);
                    if v_isShared_4265_ == 0 {
                        lean_ctor_set(v___x_4264_, 1, v___x_4301_);
                        v___x_4303_ = v___x_4264_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4304_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4304_, 0, v_size_4261_);
                        lean_ctor_set(v_reuseFailAlloc_4304_, 1, v___x_4301_);
                        v___x_4303_ = v_reuseFailAlloc_4304_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4293_;
            }
            3 => {
                return v___x_4296_;
            }
            4 => {
                return v___x_4303_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(
    mut v_msgData_4306_: *mut LeanObject,
    mut v___y_4307_: *mut LeanObject,
    mut v___y_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    v___x_4312_ = lean_st_ref_get(v___y_4310_);
    v_env_4313_ = lean_ctor_get(v___x_4312_, 0);
    lean_inc_ref(v_env_4313_);
    lean_dec(v___x_4312_);
    v___x_4314_ = lean_st_ref_get(v___y_4308_);
    v_mctx_4315_ = lean_ctor_get(v___x_4314_, 0);
    lean_inc_ref(v_mctx_4315_);
    lean_dec(v___x_4314_);
    v_lctx_4316_ = lean_ctor_get(v___y_4307_, 2);
    v_options_4317_ = lean_ctor_get(v___y_4309_, 2);
    lean_inc_ref(v_options_4317_);
    lean_inc_ref(v_lctx_4316_);
    v___x_4318_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4318_, 0, v_env_4313_);
    lean_ctor_set(v___x_4318_, 1, v_mctx_4315_);
    lean_ctor_set(v___x_4318_, 2, v_lctx_4316_);
    lean_ctor_set(v___x_4318_, 3, v_options_4317_);
    v___x_4319_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4319_, 0, v___x_4318_);
    lean_ctor_set(v___x_4319_, 1, v_msgData_4306_);
    v___x_4320_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4320_, 0, v___x_4319_);
    return v___x_4320_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8___boxed(
    mut v_msgData_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4327_: *mut LeanObject = core::ptr::null_mut();
    v_res_4327_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msgData_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
    lean_dec(v___y_4325_);
    lean_dec_ref(v___y_4324_);
    lean_dec(v___y_4323_);
    lean_dec_ref(v___y_4322_);
    return v_res_4327_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0()
-> f64 {
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: f64 = 0.0;
    v___x_4328_ = lean_unsigned_to_nat(0);
    v___x_4329_ = lean_float_of_nat(v___x_4328_);
    return v___x_4329_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(
    mut v_cls_4333_: *mut LeanObject,
    mut v_msg_4334_: *mut LeanObject,
    mut v___y_4335_: *mut LeanObject,
    mut v___y_4336_: *mut LeanObject,
    mut v___y_4337_: *mut LeanObject,
    mut v___y_4338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4345_: u8 = 0;
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v_tid_4359_: u64 = 0;
    let mut v_traces_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4363_: u8 = 0;
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4365_: f64 = 0.0;
    let mut v___x_4366_: u8 = 0;
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut v_isSharedCheck_4385_: u8 = 0;
    let mut v_isSharedCheck_4386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4340_ = lean_ctor_get(v___y_4337_, 5);
                v___x_4341_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4_spec__8(v_msg_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
                v_a_4342_ = lean_ctor_get(v___x_4341_, 0);
                v_isSharedCheck_4386_ = (!lean_is_exclusive(v___x_4341_)) as u8;
                if v_isSharedCheck_4386_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    v_isShared_4345_ = v_isSharedCheck_4386_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4342_);
                    lean_dec(v___x_4341_);
                    v___x_4344_ = lean_box(0);
                    v_isShared_4345_ = v_isSharedCheck_4386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4346_ = lean_st_ref_take(v___y_4338_);
                v_traceState_4347_ = lean_ctor_get(v___x_4346_, 4);
                v_env_4348_ = lean_ctor_get(v___x_4346_, 0);
                v_nextMacroScope_4349_ = lean_ctor_get(v___x_4346_, 1);
                v_ngen_4350_ = lean_ctor_get(v___x_4346_, 2);
                v_auxDeclNGen_4351_ = lean_ctor_get(v___x_4346_, 3);
                v_cache_4352_ = lean_ctor_get(v___x_4346_, 5);
                v_messages_4353_ = lean_ctor_get(v___x_4346_, 6);
                v_infoState_4354_ = lean_ctor_get(v___x_4346_, 7);
                v_snapshotTasks_4355_ = lean_ctor_get(v___x_4346_, 8);
                v_isSharedCheck_4385_ = (!lean_is_exclusive(v___x_4346_)) as u8;
                if v_isSharedCheck_4385_ == 0 {
                    v___x_4357_ = v___x_4346_;
                    v_isShared_4358_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4355_);
                    lean_inc(v_infoState_4354_);
                    lean_inc(v_messages_4353_);
                    lean_inc(v_cache_4352_);
                    lean_inc(v_traceState_4347_);
                    lean_inc(v_auxDeclNGen_4351_);
                    lean_inc(v_ngen_4350_);
                    lean_inc(v_nextMacroScope_4349_);
                    lean_inc(v_env_4348_);
                    lean_dec(v___x_4346_);
                    v___x_4357_ = lean_box(0);
                    v_isShared_4358_ = v_isSharedCheck_4385_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4359_ = lean_ctor_get_uint64(
                    v_traceState_4347_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4360_ = lean_ctor_get(v_traceState_4347_, 0);
                v_isSharedCheck_4384_ = (!lean_is_exclusive(v_traceState_4347_)) as u8;
                if v_isSharedCheck_4384_ == 0 {
                    v___x_4362_ = v_traceState_4347_;
                    v_isShared_4363_ = v_isSharedCheck_4384_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4360_);
                    lean_dec(v_traceState_4347_);
                    v___x_4362_ = lean_box(0);
                    v_isShared_4363_ = v_isSharedCheck_4384_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4364_ = lean_box(0);
                v___x_4365_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__0);
                v___x_4366_ = 0;
                v___x_4367_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__1;
                v___x_4368_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4368_, 0, v_cls_4333_);
                lean_ctor_set(v___x_4368_, 1, v___x_4364_);
                lean_ctor_set(v___x_4368_, 2, v___x_4367_);
                lean_ctor_set_float(
                    v___x_4368_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4365_,
                );
                lean_ctor_set_float(
                    v___x_4368_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4365_,
                );
                lean_ctor_set_uint8(
                    v___x_4368_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4366_,
                );
                v___x_4369_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___closed__2;
                v___x_4370_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4370_, 0, v___x_4368_);
                lean_ctor_set(v___x_4370_, 1, v_a_4342_);
                lean_ctor_set(v___x_4370_, 2, v___x_4369_);
                lean_inc(v_ref_4340_);
                v___x_4371_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4371_, 0, v_ref_4340_);
                lean_ctor_set(v___x_4371_, 1, v___x_4370_);
                v___x_4372_ = l_Lean_PersistentArray_push___redArg(v_traces_4360_, v___x_4371_);
                if v_isShared_4363_ == 0 {
                    lean_ctor_set(v___x_4362_, 0, v___x_4372_);
                    v___x_4374_ = v___x_4362_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4372_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4383_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4359_,
                    );
                    v___x_4374_ = v_reuseFailAlloc_4383_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4358_ == 0 {
                    lean_ctor_set(v___x_4357_, 4, v___x_4374_);
                    v___x_4376_ = v___x_4357_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4382_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_env_4348_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_nextMacroScope_4349_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 2, v_ngen_4350_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 3, v_auxDeclNGen_4351_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 4, v___x_4374_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 5, v_cache_4352_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 6, v_messages_4353_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 7, v_infoState_4354_);
                    lean_ctor_set(v_reuseFailAlloc_4382_, 8, v_snapshotTasks_4355_);
                    v___x_4376_ = v_reuseFailAlloc_4382_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4377_ = lean_st_ref_set(v___y_4338_, v___x_4376_);
                v___x_4378_ = lean_box(0);
                if v_isShared_4345_ == 0 {
                    lean_ctor_set(v___x_4344_, 0, v___x_4378_);
                    v___x_4380_ = v___x_4344_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4381_, 0, v___x_4378_);
                    v___x_4380_ = v_reuseFailAlloc_4381_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg___boxed(
    mut v_cls_4387_: *mut LeanObject,
    mut v_msg_4388_: *mut LeanObject,
    mut v___y_4389_: *mut LeanObject,
    mut v___y_4390_: *mut LeanObject,
    mut v___y_4391_: *mut LeanObject,
    mut v___y_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4394_: *mut LeanObject = core::ptr::null_mut();
    v_res_4394_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(
        v_cls_4387_,
        v_msg_4388_,
        v___y_4389_,
        v___y_4390_,
        v___y_4391_,
        v___y_4392_,
    );
    lean_dec(v___y_4392_);
    lean_dec_ref(v___y_4391_);
    lean_dec(v___y_4390_);
    lean_dec_ref(v___y_4389_);
    return v_res_4394_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(
    mut v_x_4395_: *mut LeanObject,
    mut v_x_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
    mut v___y_4400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4408_: u8 = 0;
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_isSharedCheck_4423_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4395_) == 0 {
                    v___x_4402_ = l_List_reverse___redArg(v_x_4396_);
                    v___x_4403_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4403_, 0, v___x_4402_);
                    return v___x_4403_;
                } else {
                    v_head_4404_ = lean_ctor_get(v_x_4395_, 0);
                    v_tail_4405_ = lean_ctor_get(v_x_4395_, 1);
                    v_isSharedCheck_4423_ = (!lean_is_exclusive(v_x_4395_)) as u8;
                    if v_isSharedCheck_4423_ == 0 {
                        v___x_4407_ = v_x_4395_;
                        v_isShared_4408_ = v_isSharedCheck_4423_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4405_);
                        lean_inc(v_head_4404_);
                        lean_dec(v_x_4395_);
                        v___x_4407_ = lean_box(0);
                        v_isShared_4408_ = v_isSharedCheck_4423_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v___y_4400_);
                lean_inc_ref(v___y_4399_);
                lean_inc(v___y_4398_);
                lean_inc_ref(v___y_4397_);
                v___x_4409_ = lean_infer_type(
                    v_head_4404_,
                    v___y_4397_,
                    v___y_4398_,
                    v___y_4399_,
                    v___y_4400_,
                );
                if lean_obj_tag(v___x_4409_) == 0 {
                    v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
                    lean_inc(v_a_4410_);
                    lean_dec_ref_known(v___x_4409_, 1);
                    if v_isShared_4408_ == 0 {
                        lean_ctor_set(v___x_4407_, 1, v_x_4396_);
                        lean_ctor_set(v___x_4407_, 0, v_a_4410_);
                        v___x_4412_ = v___x_4407_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4410_);
                        lean_ctor_set(v_reuseFailAlloc_4414_, 1, v_x_4396_);
                        v___x_4412_ = v_reuseFailAlloc_4414_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4407_);
                    lean_dec(v_tail_4405_);
                    lean_dec(v_x_4396_);
                    v_a_4415_ = lean_ctor_get(v___x_4409_, 0);
                    v_isSharedCheck_4422_ = (!lean_is_exclusive(v___x_4409_)) as u8;
                    if v_isSharedCheck_4422_ == 0 {
                        v___x_4417_ = v___x_4409_;
                        v_isShared_4418_ = v_isSharedCheck_4422_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4415_);
                        lean_dec(v___x_4409_);
                        v___x_4417_ = lean_box(0);
                        v_isShared_4418_ = v_isSharedCheck_4422_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_x_4395_ = v_tail_4405_;
                v_x_4396_ = v___x_4412_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4418_ == 0 {
                    v___x_4420_ = v___x_4417_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
                    v___x_4420_ = v_reuseFailAlloc_4421_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg___boxed(
    mut v_x_4424_: *mut LeanObject,
    mut v_x_4425_: *mut LeanObject,
    mut v___y_4426_: *mut LeanObject,
    mut v___y_4427_: *mut LeanObject,
    mut v___y_4428_: *mut LeanObject,
    mut v___y_4429_: *mut LeanObject,
    mut v___y_4430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4431_: *mut LeanObject = core::ptr::null_mut();
    v_res_4431_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(
        v_x_4424_,
        v_x_4425_,
        v___y_4426_,
        v___y_4427_,
        v___y_4428_,
        v___y_4429_,
    );
    lean_dec(v___y_4429_);
    lean_dec_ref(v___y_4428_);
    lean_dec(v___y_4427_);
    lean_dec_ref(v___y_4426_);
    return v_res_4431_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(
    mut v_a_4432_: *mut LeanObject,
    mut v_a_4433_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4445_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4432_) == 0 {
                    v___x_4434_ = l_List_reverse___redArg(v_a_4433_);
                    return v___x_4434_;
                } else {
                    v_head_4435_ = lean_ctor_get(v_a_4432_, 0);
                    v_tail_4436_ = lean_ctor_get(v_a_4432_, 1);
                    v_isSharedCheck_4445_ = (!lean_is_exclusive(v_a_4432_)) as u8;
                    if v_isSharedCheck_4445_ == 0 {
                        v___x_4438_ = v_a_4432_;
                        v_isShared_4439_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4436_);
                        lean_inc(v_head_4435_);
                        lean_dec(v_a_4432_);
                        v___x_4438_ = lean_box(0);
                        v_isShared_4439_ = v_isSharedCheck_4445_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4440_ = l_Lean_MessageData_ofExpr(v_head_4435_);
                if v_isShared_4439_ == 0 {
                    lean_ctor_set(v___x_4438_, 1, v_a_4433_);
                    lean_ctor_set(v___x_4438_, 0, v___x_4440_);
                    v___x_4442_ = v___x_4438_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4440_);
                    lean_ctor_set(v_reuseFailAlloc_4444_, 1, v_a_4433_);
                    v___x_4442_ = v_reuseFailAlloc_4444_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4432_ = v_tail_4436_;
                v_a_4433_ = v___x_4442_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4() -> *mut LeanObject {
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    v___x_4452_ = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
    v___x_4453_ = l_Lean_Elab_Tactic_Omega_lookup___closed__3;
    v___x_4454_ = l_Lean_Name_append(v___x_4453_, v___x_4452_);
    return v___x_4454_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6() -> *mut LeanObject {
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    v___x_4456_ = l_Lean_Elab_Tactic_Omega_lookup___closed__5;
    v___x_4457_ = l_Lean_stringToMessageData(v___x_4456_);
    return v___x_4457_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8() -> *mut LeanObject {
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut LeanObject = core::ptr::null_mut();
    v___x_4459_ = l_Lean_Elab_Tactic_Omega_lookup___closed__7;
    v___x_4460_ = l_Lean_stringToMessageData(v___x_4459_);
    return v___x_4460_;
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_lookup(
    mut v_e_4461_: *mut LeanObject,
    mut v_a_4462_: *mut LeanObject,
    mut v_a_4463_: *mut LeanObject,
    mut v_a_4464_: *mut LeanObject,
    mut v_a_4465_: u8,
    mut v_a_4466_: *mut LeanObject,
    mut v_a_4467_: *mut LeanObject,
    mut v_a_4468_: *mut LeanObject,
    mut v_a_4469_: *mut LeanObject,
    mut v_a_4470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4477_: u8 = 0;
    let mut v___y_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4493_: u8 = 0;
    let mut v___x_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4499_: u8 = 0;
    let mut v___y_4500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4507_: u8 = 0;
    let mut v_a_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: u8 = 0;
    let mut v___x_4513_: u8 = 0;
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4525_: u8 = 0;
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4529_: u8 = 0;
    let mut v_a_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4533_: u8 = 0;
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4537_: u8 = 0;
    let mut v_a_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: u8 = 0;
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4555_: u8 = 0;
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4559_: u8 = 0;
    let mut v_val_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4563_: u8 = 0;
    let mut v___x_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4569_: u8 = 0;
    let mut v_isSharedCheck_4570_: u8 = 0;
    let mut v_a_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4574_: u8 = 0;
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4472_ = lean_st_ref_get(v_a_4463_);
                v___x_4473_ = l_Lean_Meta_Canonicalizer_canon(
                    v_e_4461_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_,
                );
                if lean_obj_tag(v___x_4473_) == 0 {
                    v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
                    v_isSharedCheck_4570_ = (!lean_is_exclusive(v___x_4473_)) as u8;
                    if v_isSharedCheck_4570_ == 0 {
                        v___x_4476_ = v___x_4473_;
                        v_isShared_4477_ = v_isSharedCheck_4570_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4474_);
                        lean_dec(v___x_4473_);
                        v___x_4476_ = lean_box(0);
                        v_isShared_4477_ = v_isSharedCheck_4570_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4472_);
                    v_a_4571_ = lean_ctor_get(v___x_4473_, 0);
                    v_isSharedCheck_4578_ = (!lean_is_exclusive(v___x_4473_)) as u8;
                    if v_isSharedCheck_4578_ == 0 {
                        v___x_4573_ = v___x_4473_;
                        v_isShared_4574_ = v_isSharedCheck_4578_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4571_);
                        lean_dec(v___x_4473_);
                        v___x_4573_ = lean_box(0);
                        v_isShared_4574_ = v_isSharedCheck_4578_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4490_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v___x_4472_, v_a_4474_);
                lean_dec(v___x_4472_);
                if lean_obj_tag(v___x_4490_) == 0 {
                    v_options_4491_ = lean_ctor_get(v_a_4469_, 2);
                    v_inheritedTraceOptions_4492_ = lean_ctor_get(v_a_4469_, 13);
                    v_hasTrace_4493_ = lean_ctor_get_uint8(
                        v_options_4491_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    v___x_4494_ = l_Lean_Elab_Tactic_Omega_lookup___closed__1;
                    if v_hasTrace_4493_ == 0 {
                        v___y_4496_ = v_a_4462_;
                        v___y_4497_ = v_a_4463_;
                        v___y_4498_ = v_a_4464_;
                        v___y_4499_ = v_a_4465_;
                        v___y_4500_ = v_a_4466_;
                        v___y_4501_ = v_a_4467_;
                        v___y_4502_ = v_a_4468_;
                        v___y_4503_ = v_a_4469_;
                        v___y_4504_ = v_a_4470_;
                        state = 4;
                        continue;
                    } else {
                        v___x_4546_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_lookup___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Omega_lookup___closed__4_once
                            ),
                            _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4,
                        );
                        v___x_4547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4492_,
                            v_options_4491_,
                            v___x_4546_,
                        );
                        if v___x_4547_ == 0 {
                            v___y_4496_ = v_a_4462_;
                            v___y_4497_ = v_a_4463_;
                            v___y_4498_ = v_a_4464_;
                            v___y_4499_ = v_a_4465_;
                            v___y_4500_ = v_a_4466_;
                            v___y_4501_ = v_a_4467_;
                            v___y_4502_ = v_a_4468_;
                            v___y_4503_ = v_a_4469_;
                            v___y_4504_ = v_a_4470_;
                            state = 4;
                            continue;
                        } else {
                            v___x_4548_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_lookup___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Tactic_Omega_lookup___closed__8_once
                                ),
                                _init_l_Lean_Elab_Tactic_Omega_lookup___closed__8,
                            );
                            lean_inc(v_a_4474_);
                            v___x_4549_ = l_Lean_MessageData_ofExpr(v_a_4474_);
                            v___x_4550_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_4550_, 0, v___x_4548_);
                            lean_ctor_set(v___x_4550_, 1, v___x_4549_);
                            v___x_4551_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_4494_, v___x_4550_, v_a_4467_, v_a_4468_, v_a_4469_, v_a_4470_);
                            if lean_obj_tag(v___x_4551_) == 0 {
                                lean_dec_ref_known(v___x_4551_, 1);
                                v___y_4496_ = v_a_4462_;
                                v___y_4497_ = v_a_4463_;
                                v___y_4498_ = v_a_4464_;
                                v___y_4499_ = v_a_4465_;
                                v___y_4500_ = v_a_4466_;
                                v___y_4501_ = v_a_4467_;
                                v___y_4502_ = v_a_4468_;
                                v___y_4503_ = v_a_4469_;
                                v___y_4504_ = v_a_4470_;
                                state = 4;
                                continue;
                            } else {
                                lean_del_object(v___x_4476_);
                                lean_dec(v_a_4474_);
                                v_a_4552_ = lean_ctor_get(v___x_4551_, 0);
                                v_isSharedCheck_4559_ = (!lean_is_exclusive(v___x_4551_)) as u8;
                                if v_isSharedCheck_4559_ == 0 {
                                    v___x_4554_ = v___x_4551_;
                                    v_isShared_4555_ = v_isSharedCheck_4559_;
                                    state = 11;
                                    continue;
                                } else {
                                    lean_inc(v_a_4552_);
                                    lean_dec(v___x_4551_);
                                    v___x_4554_ = lean_box(0);
                                    v_isShared_4555_ = v_isSharedCheck_4559_;
                                    state = 11;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4476_);
                    lean_dec(v_a_4474_);
                    v_val_4560_ = lean_ctor_get(v___x_4490_, 0);
                    v_isSharedCheck_4569_ = (!lean_is_exclusive(v___x_4490_)) as u8;
                    if v_isSharedCheck_4569_ == 0 {
                        v___x_4562_ = v___x_4490_;
                        v_isShared_4563_ = v_isSharedCheck_4569_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_val_4560_);
                        lean_dec(v___x_4490_);
                        v___x_4562_ = lean_box(0);
                        v_isShared_4563_ = v_isSharedCheck_4569_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4481_ = lean_st_ref_take(v___y_4480_);
                v_size_4482_ = lean_ctor_get(v___x_4481_, 0);
                lean_inc_n(v_size_4482_, 2);
                v___x_4483_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v___x_4481_, v_a_4474_, v_size_4482_);
                v___x_4484_ = lean_st_ref_set(v___y_4480_, v___x_4483_);
                v___x_4485_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4485_, 0, v___y_4479_);
                v___x_4486_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4486_, 0, v_size_4482_);
                lean_ctor_set(v___x_4486_, 1, v___x_4485_);
                if v_isShared_4477_ == 0 {
                    lean_ctor_set(v___x_4476_, 0, v___x_4486_);
                    v___x_4488_ = v___x_4476_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4486_);
                    v___x_4488_ = v_reuseFailAlloc_4489_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4488_;
            }
            4 => {
                lean_inc(v_a_4474_);
                v___x_4505_ = l_Lean_Elab_Tactic_Omega_analyzeAtom___redArg(
                    v_a_4474_,
                    v___y_4498_,
                    v___y_4501_,
                    v___y_4502_,
                    v___y_4503_,
                    v___y_4504_,
                );
                if lean_obj_tag(v___x_4505_) == 0 {
                    v_options_4506_ = lean_ctor_get(v___y_4503_, 2);
                    v_hasTrace_4507_ = lean_ctor_get_uint8(
                        v_options_4506_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4507_ == 0 {
                        v_a_4508_ = lean_ctor_get(v___x_4505_, 0);
                        lean_inc(v_a_4508_);
                        lean_dec_ref_known(v___x_4505_, 1);
                        v___y_4479_ = v_a_4508_;
                        v___y_4480_ = v___y_4497_;
                        state = 2;
                        continue;
                    } else {
                        v_a_4509_ = lean_ctor_get(v___x_4505_, 0);
                        lean_inc(v_a_4509_);
                        lean_dec_ref_known(v___x_4505_, 1);
                        v_inheritedTraceOptions_4510_ = lean_ctor_get(v___y_4503_, 13);
                        v___x_4511_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Omega_lookup___closed__4),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Tactic_Omega_lookup___closed__4_once
                            ),
                            _init_l_Lean_Elab_Tactic_Omega_lookup___closed__4,
                        );
                        v___x_4512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4510_,
                            v_options_4506_,
                            v___x_4511_,
                        );
                        if v___x_4512_ == 0 {
                            v___y_4479_ = v_a_4509_;
                            v___y_4480_ = v___y_4497_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4513_ = l_List_isEmpty___redArg(v_a_4509_);
                            if v___x_4513_ == 0 {
                                if v___x_4512_ == 0 {
                                    v___y_4479_ = v_a_4509_;
                                    v___y_4480_ = v___y_4497_;
                                    state = 2;
                                    continue;
                                } else {
                                    v___x_4514_ = lean_box(0);
                                    lean_inc(v_a_4509_);
                                    v___x_4515_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(v_a_4509_, v___x_4514_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
                                    if lean_obj_tag(v___x_4515_) == 0 {
                                        v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
                                        lean_inc(v_a_4516_);
                                        lean_dec_ref_known(v___x_4515_, 1);
                                        v___x_4517_ = lean_obj_once(
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Elab_Tactic_Omega_lookup___closed__6
                                            ),
                                            core::ptr::addr_of_mut!(
                                                l_Lean_Elab_Tactic_Omega_lookup___closed__6_once
                                            ),
                                            _init_l_Lean_Elab_Tactic_Omega_lookup___closed__6,
                                        );
                                        v___x_4518_ = l_List_mapTR_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__3(v_a_4516_, v___x_4514_);
                                        v___x_4519_ = l_Lean_MessageData_ofList(v___x_4518_);
                                        v___x_4520_ = lean_alloc_ctor(7, 2, (0) as u32);
                                        lean_ctor_set(v___x_4520_, 0, v___x_4517_);
                                        lean_ctor_set(v___x_4520_, 1, v___x_4519_);
                                        v___x_4521_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(v___x_4494_, v___x_4520_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
                                        if lean_obj_tag(v___x_4521_) == 0 {
                                            lean_dec_ref_known(v___x_4521_, 1);
                                            v___y_4479_ = v_a_4509_;
                                            v___y_4480_ = v___y_4497_;
                                            state = 2;
                                            continue;
                                        } else {
                                            lean_dec(v_a_4509_);
                                            lean_del_object(v___x_4476_);
                                            lean_dec(v_a_4474_);
                                            v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
                                            v_isSharedCheck_4529_ =
                                                (!lean_is_exclusive(v___x_4521_)) as u8;
                                            if v_isSharedCheck_4529_ == 0 {
                                                v___x_4524_ = v___x_4521_;
                                                v_isShared_4525_ = v_isSharedCheck_4529_;
                                                state = 5;
                                                continue;
                                            } else {
                                                lean_inc(v_a_4522_);
                                                lean_dec(v___x_4521_);
                                                v___x_4524_ = lean_box(0);
                                                v_isShared_4525_ = v_isSharedCheck_4529_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_4509_);
                                        lean_del_object(v___x_4476_);
                                        lean_dec(v_a_4474_);
                                        v_a_4530_ = lean_ctor_get(v___x_4515_, 0);
                                        v_isSharedCheck_4537_ =
                                            (!lean_is_exclusive(v___x_4515_)) as u8;
                                        if v_isSharedCheck_4537_ == 0 {
                                            v___x_4532_ = v___x_4515_;
                                            v_isShared_4533_ = v_isSharedCheck_4537_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4530_);
                                            lean_dec(v___x_4515_);
                                            v___x_4532_ = lean_box(0);
                                            v_isShared_4533_ = v_isSharedCheck_4537_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___y_4479_ = v_a_4509_;
                                v___y_4480_ = v___y_4497_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4476_);
                    lean_dec(v_a_4474_);
                    v_a_4538_ = lean_ctor_get(v___x_4505_, 0);
                    v_isSharedCheck_4545_ = (!lean_is_exclusive(v___x_4505_)) as u8;
                    if v_isSharedCheck_4545_ == 0 {
                        v___x_4540_ = v___x_4505_;
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4538_);
                        lean_dec(v___x_4505_);
                        v___x_4540_ = lean_box(0);
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4525_ == 0 {
                    v___x_4527_ = v___x_4524_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
                    v___x_4527_ = v_reuseFailAlloc_4528_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4527_;
            }
            7 => {
                if v_isShared_4533_ == 0 {
                    v___x_4535_ = v___x_4532_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
                    v___x_4535_ = v_reuseFailAlloc_4536_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4535_;
            }
            9 => {
                if v_isShared_4541_ == 0 {
                    v___x_4543_ = v___x_4540_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
                    v___x_4543_ = v_reuseFailAlloc_4544_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4543_;
            }
            11 => {
                if v_isShared_4555_ == 0 {
                    v___x_4557_ = v___x_4554_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
                    v___x_4557_ = v_reuseFailAlloc_4558_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4557_;
            }
            13 => {
                v___x_4564_ = lean_box(0);
                v___x_4565_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4565_, 0, v_val_4560_);
                lean_ctor_set(v___x_4565_, 1, v___x_4564_);
                if v_isShared_4563_ == 0 {
                    lean_ctor_set_tag(v___x_4562_, 0);
                    lean_ctor_set(v___x_4562_, 0, v___x_4565_);
                    v___x_4567_ = v___x_4562_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4568_, 0, v___x_4565_);
                    v___x_4567_ = v_reuseFailAlloc_4568_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4567_;
            }
            15 => {
                if v_isShared_4574_ == 0 {
                    v___x_4576_ = v___x_4573_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
                    v___x_4576_ = v_reuseFailAlloc_4577_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Omega_lookup___boxed(
    mut v_e_4579_: *mut LeanObject,
    mut v_a_4580_: *mut LeanObject,
    mut v_a_4581_: *mut LeanObject,
    mut v_a_4582_: *mut LeanObject,
    mut v_a_4583_: *mut LeanObject,
    mut v_a_4584_: *mut LeanObject,
    mut v_a_4585_: *mut LeanObject,
    mut v_a_4586_: *mut LeanObject,
    mut v_a_4587_: *mut LeanObject,
    mut v_a_4588_: *mut LeanObject,
    mut v_a_4589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_4590_: u8 = 0;
    let mut v_res_4591_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_4590_ = (lean_unbox(v_a_4583_) as u8);
    v_res_4591_ = l_Lean_Elab_Tactic_Omega_lookup(
        v_e_4579_,
        v_a_4580_,
        v_a_4581_,
        v_a_4582_,
        v_a_boxed_4590_,
        v_a_4584_,
        v_a_4585_,
        v_a_4586_,
        v_a_4587_,
        v_a_4588_,
    );
    lean_dec(v_a_4588_);
    lean_dec_ref(v_a_4587_);
    lean_dec(v_a_4586_);
    lean_dec_ref(v_a_4585_);
    lean_dec(v_a_4584_);
    lean_dec_ref(v_a_4582_);
    lean_dec(v_a_4581_);
    lean_dec(v_a_4580_);
    return v_res_4591_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(
    mut v_00_u03b2_4592_: *mut LeanObject,
    mut v_m_4593_: *mut LeanObject,
    mut v_a_4594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4595_: *mut LeanObject = core::ptr::null_mut();
    v___x_4595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___redArg(v_m_4593_, v_a_4594_);
    return v___x_4595_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0___boxed(
    mut v_00_u03b2_4596_: *mut LeanObject,
    mut v_m_4597_: *mut LeanObject,
    mut v_a_4598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4599_: *mut LeanObject = core::ptr::null_mut();
    v_res_4599_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0(v_00_u03b2_4596_, v_m_4597_, v_a_4598_);
    lean_dec_ref(v_a_4598_);
    lean_dec_ref(v_m_4597_);
    return v_res_4599_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1(
    mut v_00_u03b2_4600_: *mut LeanObject,
    mut v_m_4601_: *mut LeanObject,
    mut v_a_4602_: *mut LeanObject,
    mut v_b_4603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    v___x_4604_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1___redArg(v_m_4601_, v_a_4602_, v_b_4603_);
    return v___x_4604_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(
    mut v_x_4605_: *mut LeanObject,
    mut v_x_4606_: *mut LeanObject,
    mut v___y_4607_: *mut LeanObject,
    mut v___y_4608_: *mut LeanObject,
    mut v___y_4609_: *mut LeanObject,
    mut v___y_4610_: u8,
    mut v___y_4611_: *mut LeanObject,
    mut v___y_4612_: *mut LeanObject,
    mut v___y_4613_: *mut LeanObject,
    mut v___y_4614_: *mut LeanObject,
    mut v___y_4615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    v___x_4617_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___redArg(
        v_x_4605_,
        v_x_4606_,
        v___y_4612_,
        v___y_4613_,
        v___y_4614_,
        v___y_4615_,
    );
    return v___x_4617_;
}
pub unsafe fn l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2___boxed(
    mut v_x_4618_: *mut LeanObject,
    mut v_x_4619_: *mut LeanObject,
    mut v___y_4620_: *mut LeanObject,
    mut v___y_4621_: *mut LeanObject,
    mut v___y_4622_: *mut LeanObject,
    mut v___y_4623_: *mut LeanObject,
    mut v___y_4624_: *mut LeanObject,
    mut v___y_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_42932__boxed_4630_: u8 = 0;
    let mut v_res_4631_: *mut LeanObject = core::ptr::null_mut();
    v___y_42932__boxed_4630_ = (lean_unbox(v___y_4623_) as u8);
    v_res_4631_ = l_List_mapM_loop___at___00Lean_Elab_Tactic_Omega_lookup_spec__2(
        v_x_4618_,
        v_x_4619_,
        v___y_4620_,
        v___y_4621_,
        v___y_4622_,
        v___y_42932__boxed_4630_,
        v___y_4624_,
        v___y_4625_,
        v___y_4626_,
        v___y_4627_,
        v___y_4628_,
    );
    lean_dec(v___y_4628_);
    lean_dec_ref(v___y_4627_);
    lean_dec(v___y_4626_);
    lean_dec_ref(v___y_4625_);
    lean_dec(v___y_4624_);
    lean_dec_ref(v___y_4622_);
    lean_dec(v___y_4621_);
    lean_dec(v___y_4620_);
    return v_res_4631_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(
    mut v_cls_4632_: *mut LeanObject,
    mut v_msg_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
    mut v___y_4637_: u8,
    mut v___y_4638_: *mut LeanObject,
    mut v___y_4639_: *mut LeanObject,
    mut v___y_4640_: *mut LeanObject,
    mut v___y_4641_: *mut LeanObject,
    mut v___y_4642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    v___x_4644_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___redArg(
        v_cls_4632_,
        v_msg_4633_,
        v___y_4639_,
        v___y_4640_,
        v___y_4641_,
        v___y_4642_,
    );
    return v___x_4644_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4___boxed(
    mut v_cls_4645_: *mut LeanObject,
    mut v_msg_4646_: *mut LeanObject,
    mut v___y_4647_: *mut LeanObject,
    mut v___y_4648_: *mut LeanObject,
    mut v___y_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
    mut v___y_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
    mut v___y_4655_: *mut LeanObject,
    mut v___y_4656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_42968__boxed_4657_: u8 = 0;
    let mut v_res_4658_: *mut LeanObject = core::ptr::null_mut();
    v___y_42968__boxed_4657_ = (lean_unbox(v___y_4650_) as u8);
    v_res_4658_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Omega_lookup_spec__4(
        v_cls_4645_,
        v_msg_4646_,
        v___y_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_42968__boxed_4657_,
        v___y_4651_,
        v___y_4652_,
        v___y_4653_,
        v___y_4654_,
        v___y_4655_,
    );
    lean_dec(v___y_4655_);
    lean_dec_ref(v___y_4654_);
    lean_dec(v___y_4653_);
    lean_dec_ref(v___y_4652_);
    lean_dec(v___y_4651_);
    lean_dec_ref(v___y_4649_);
    lean_dec(v___y_4648_);
    lean_dec(v___y_4647_);
    return v_res_4658_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(
    mut v_00_u03b2_4659_: *mut LeanObject,
    mut v_a_4660_: *mut LeanObject,
    mut v_x_4661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    v___x_4662_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___redArg(v_a_4660_, v_x_4661_);
    return v___x_4662_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0___boxed(
    mut v_00_u03b2_4663_: *mut LeanObject,
    mut v_a_4664_: *mut LeanObject,
    mut v_x_4665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4666_: *mut LeanObject = core::ptr::null_mut();
    v_res_4666_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_Tactic_Omega_lookup_spec__0_spec__0(v_00_u03b2_4663_, v_a_4664_, v_x_4665_);
    lean_dec(v_x_4665_);
    lean_dec_ref(v_a_4664_);
    return v_res_4666_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(
    mut v_00_u03b2_4667_: *mut LeanObject,
    mut v_a_4668_: *mut LeanObject,
    mut v_x_4669_: *mut LeanObject,
) -> u8 {
    let mut v___x_4670_: u8 = 0;
    v___x_4670_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___redArg(v_a_4668_, v_x_4669_);
    return v___x_4670_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2___boxed(
    mut v_00_u03b2_4671_: *mut LeanObject,
    mut v_a_4672_: *mut LeanObject,
    mut v_x_4673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4674_: u8 = 0;
    let mut v_r_4675_: *mut LeanObject = core::ptr::null_mut();
    v_res_4674_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__2(v_00_u03b2_4671_, v_a_4672_, v_x_4673_);
    lean_dec(v_x_4673_);
    lean_dec_ref(v_a_4672_);
    v_r_4675_ = lean_box((v_res_4674_) as usize);
    return v_r_4675_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3(
    mut v_00_u03b2_4676_: *mut LeanObject,
    mut v_data_4677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    v___x_4678_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3___redArg(v_data_4677_);
    return v___x_4678_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4(
    mut v_00_u03b2_4679_: *mut LeanObject,
    mut v_a_4680_: *mut LeanObject,
    mut v_b_4681_: *mut LeanObject,
    mut v_x_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    v___x_4683_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__4___redArg(v_a_4680_, v_b_4681_, v_x_4682_);
    return v___x_4683_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4(
    mut v_00_u03b2_4684_: *mut LeanObject,
    mut v_i_4685_: *mut LeanObject,
    mut v_source_4686_: *mut LeanObject,
    mut v_target_4687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4688_: *mut LeanObject = core::ptr::null_mut();
    v___x_4688_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4___redArg(v_i_4685_, v_source_4686_, v_target_4687_);
    return v___x_4688_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9(
    mut v_00_u03b2_4689_: *mut LeanObject,
    mut v_x_4690_: *mut LeanObject,
    mut v_x_4691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4692_: *mut LeanObject = core::ptr::null_mut();
    v___x_4692_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Elab_Tactic_Omega_lookup_spec__1_spec__3_spec__4_spec__9___redArg(v_x_4690_, v_x_4691_);
    return v___x_4692_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Canonicalizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Canonicalizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Omega_OmegaM(builtin);
}
