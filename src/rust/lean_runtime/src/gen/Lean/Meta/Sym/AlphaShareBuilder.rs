// Lean compiler output
// Module: Lean.Meta.Sym.AlphaShareBuilder
// Imports: Lean.Meta.Sym.SymM
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_ReaderT_read___boxed, l_instInhabitedForall___redArg___lam__0___boxed,
    l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_bvar___override, l_Lean_Expr_const___override,
    l_Lean_Expr_forallE___override, l_Lean_Expr_fvar___override, l_Lean_Expr_lam___override,
    l_Lean_Expr_letE___override, l_Lean_Expr_lit___override, l_Lean_Expr_mdata___override,
    l_Lean_Expr_mvar___override, l_Lean_Expr_proj___override, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareCommon::{
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq,
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed,
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash,
    l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, l_Lean_Meta_Sym_instInhabitedSymM,
    l_Lean_Meta_Sym_isDebugEnabled___boxed, runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
pub static l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [95, 95, 100, 117, 109, 109, 121, 95, 95, 0]};
static mut l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__0_value) as *mut LeanObject,9304292590189383094 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0_value: LeanStringObject<32> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 32,
        m_capacity: 32,
        m_length: 31,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 65, 108, 112, 104, 97,
            83, 104, 97, 114, 101, 66, 117, 105, 108, 100, 101, 114, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 116, 101, 114,
            110, 97, 108, 46, 83, 121, 109, 46, 97, 115, 115, 101, 114, 116, 83, 104, 97, 114, 101,
            100, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2_value: LeanStringObject<46> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 46,
        m_capacity: 46,
        m_length: 45,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 112, 114, 101, 118, 46,
            101, 120, 112, 114, 32, 101, 10, 10, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_Internal_Sym_share1___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_isDebugEnabled___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_instMonadShareCommonSymM___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5_value
) as *mut LeanObject;
pub static l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6_value
) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0_value: LeanStringObject<44> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 73, 110, 116, 101, 114,
            110, 97, 108, 46, 66, 117, 105, 108, 100, 101, 114, 46, 97, 115, 115, 101, 114, 116,
            83, 104, 97, 114, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1_value: LeanStringObject<121> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 121,
        m_capacity: 121,
        m_length: 116,
        m_data: [
            97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111,
            110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101,
            97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 65, 108, 112, 104, 97, 83, 104,
            97, 114, 101, 66, 117, 105, 108, 100, 101, 114, 46, 51, 52, 48, 49, 53, 55, 52, 48, 48,
            53, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 57, 46, 48, 32, 41,
            46, 115, 101, 116, 46, 99, 111, 110, 116, 97, 105, 110, 115, 32, 226, 159, 168, 101,
            226, 159, 169, 10, 10, 0,
        ],
    };
static mut l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value:
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
    m_fun: l_Lean_Meta_Sym_Internal_Builder_share1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value:
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
    m_fun: l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1_value
) as *mut LeanObject;
pub static mut l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_updateAppS_x21___redArg___closed__0_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 65, 112, 112,
            83, 33, 0,
        ],
    };
static mut l_Lean_Expr_updateAppS_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateAppS_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_updateAppS_x21___redArg___closed__1_value: LeanStringObject<21> =
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
            97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 101, 120, 112, 101, 99, 116,
            101, 100, 0,
        ],
    };
static mut l_Lean_Expr_updateAppS_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateAppS_x21___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Expr_updateAppS_x21___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_updateAppS_x21___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Expr_updateMDataS_x21___redArg___closed__0_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 77, 68, 97,
            116, 97, 83, 33, 0,
        ],
    };
static mut l_Lean_Expr_updateMDataS_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateMDataS_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_updateMDataS_x21___redArg___closed__1_value: LeanStringObject<15> =
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
            109, 100, 97, 116, 97, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Expr_updateMDataS_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateMDataS_x21___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_updateMDataS_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_updateProjS_x21___redArg___closed__0_value: LeanStringObject<23> =
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
            76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 80, 114, 111,
            106, 83, 33, 0,
        ],
    };
static mut l_Lean_Expr_updateProjS_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateProjS_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_updateProjS_x21___redArg___closed__1_value: LeanStringObject<14> =
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
            112, 114, 111, 106, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Expr_updateProjS_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateProjS_x21___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Expr_updateProjS_x21___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_updateProjS_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_updateForallS_x21___redArg___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 70, 111, 114,
            97, 108, 108, 83, 33, 0,
        ],
    };
static mut l_Lean_Expr_updateForallS_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateForallS_x21___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Expr_updateForallS_x21___redArg___closed__1_value: LeanStringObject<16> =
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
            102, 111, 114, 97, 108, 108, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Expr_updateForallS_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateForallS_x21___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Expr_updateForallS_x21___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_updateForallS_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_updateLambdaS_x21___redArg___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 76, 97, 109,
            98, 100, 97, 83, 33, 0,
        ],
    };
static mut l_Lean_Expr_updateLambdaS_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateLambdaS_x21___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Expr_updateLambdaS_x21___redArg___closed__1_value: LeanStringObject<16> =
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
            108, 97, 109, 98, 100, 97, 32, 101, 120, 112, 101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Expr_updateLambdaS_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateLambdaS_x21___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_updateLambdaS_x21___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Expr_updateLetS_x21___redArg___closed__0_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            76, 101, 97, 110, 46, 69, 120, 112, 114, 46, 117, 112, 100, 97, 116, 101, 76, 101, 116,
            83, 33, 0,
        ],
    };
static mut l_Lean_Expr_updateLetS_x21___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateLetS_x21___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Expr_updateLetS_x21___redArg___closed__1_value: LeanStringObject<24> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 24,
        m_capacity: 24,
        m_length: 23,
        m_data: [
            108, 101, 116, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 101, 120, 112,
            101, 99, 116, 101, 100, 0,
        ],
    };
static mut l_Lean_Expr_updateLetS_x21___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Expr_updateLetS_x21___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Expr_updateLetS_x21___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Expr_updateLetS_x21___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0(
    mut v_share1_1984_: *mut LeanObject,
    mut v_inst_1985_: *mut LeanObject,
    mut v_e_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    v___x_1987_ = lean_apply_1(v_share1_1984_, v_e_1986_);
    v___x_1988_ = lean_apply_2(v_inst_1985_, lean_box(0), v___x_1987_);
    return v___x_1988_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1(
    mut v_assertShared_1989_: *mut LeanObject,
    mut v_inst_1990_: *mut LeanObject,
    mut v_e_1991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    v___x_1992_ = lean_apply_1(v_assertShared_1989_, v_e_1991_);
    v___x_1993_ = lean_apply_2(v_inst_1990_, lean_box(0), v___x_1992_);
    return v___x_1993_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg(
    mut v_inst_1994_: *mut LeanObject,
    mut v_inst_1995_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_share1_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___f_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_share1_1996_ = lean_ctor_get(v_inst_1995_, 0);
                v_assertShared_1997_ = lean_ctor_get(v_inst_1995_, 1);
                v_isDebugEnabled_1998_ = lean_ctor_get(v_inst_1995_, 2);
                v_isSharedCheck_2008_ = (!lean_is_exclusive(v_inst_1995_)) as u8;
                if v_isSharedCheck_2008_ == 0 {
                    v___x_2000_ = v_inst_1995_;
                    v_isShared_2001_ = v_isSharedCheck_2008_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_isDebugEnabled_1998_);
                    lean_inc(v_assertShared_1997_);
                    lean_inc(v_share1_1996_);
                    lean_dec(v_inst_1995_);
                    v___x_2000_ = lean_box(0);
                    v_isShared_2001_ = v_isSharedCheck_2008_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_inst_1994_, 2);
                v___f_2002_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2002_, 0, v_share1_1996_);
                lean_closure_set(v___f_2002_, 1, v_inst_1994_);
                v___f_2003_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2003_, 0, v_assertShared_1997_);
                lean_closure_set(v___f_2003_, 1, v_inst_1994_);
                v___x_2004_ = lean_apply_2(v_inst_1994_, lean_box(0), v_isDebugEnabled_1998_);
                if v_isShared_2001_ == 0 {
                    lean_ctor_set(v___x_2000_, 2, v___x_2004_);
                    lean_ctor_set(v___x_2000_, 1, v___f_2003_);
                    lean_ctor_set(v___x_2000_, 0, v___f_2002_);
                    v___x_2006_ = v___x_2000_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___f_2002_);
                    lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___f_2003_);
                    lean_ctor_set(v_reuseFailAlloc_2007_, 2, v___x_2004_);
                    v___x_2006_ = v_reuseFailAlloc_2007_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2006_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift(
    mut v_m_2009_: *mut LeanObject,
    mut v_n_2010_: *mut LeanObject,
    mut v_inst_2011_: *mut LeanObject,
    mut v_inst_2012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_share1_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2018_: u8 = 0;
    let mut v___f_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_share1_2013_ = lean_ctor_get(v_inst_2012_, 0);
                v_assertShared_2014_ = lean_ctor_get(v_inst_2012_, 1);
                v_isDebugEnabled_2015_ = lean_ctor_get(v_inst_2012_, 2);
                v_isSharedCheck_2025_ = (!lean_is_exclusive(v_inst_2012_)) as u8;
                if v_isSharedCheck_2025_ == 0 {
                    v___x_2017_ = v_inst_2012_;
                    v_isShared_2018_ = v_isSharedCheck_2025_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_isDebugEnabled_2015_);
                    lean_inc(v_assertShared_2014_);
                    lean_inc(v_share1_2013_);
                    lean_dec(v_inst_2012_);
                    v___x_2017_ = lean_box(0);
                    v_isShared_2018_ = v_isSharedCheck_2025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_n(v_inst_2011_, 2);
                v___f_2019_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__0
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2019_, 0, v_share1_2013_);
                lean_closure_set(v___f_2019_, 1, v_inst_2011_);
                v___f_2020_ = lean_alloc_closure(
                    l_Lean_Meta_Sym_Internal_instMonadShareCommonOfMonadLift___redArg___lam__1
                        as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2020_, 0, v_assertShared_2014_);
                lean_closure_set(v___f_2020_, 1, v_inst_2011_);
                v___x_2021_ = lean_apply_2(v_inst_2011_, lean_box(0), v_isDebugEnabled_2015_);
                if v_isShared_2018_ == 0 {
                    lean_ctor_set(v___x_2017_, 2, v___x_2021_);
                    lean_ctor_set(v___x_2017_, 1, v___f_2020_);
                    lean_ctor_set(v___x_2017_, 0, v___f_2019_);
                    v___x_2023_ = v___x_2017_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___f_2019_);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 1, v___f_2020_);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 2, v___x_2021_);
                    v___x_2023_ = v_reuseFailAlloc_2024_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2023_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2()
-> *mut LeanObject {
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    v___x_2029_ = lean_box(0);
    v___x_2030_ =
        l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__1;
    v___x_2031_ = l_Lean_mkConst(v___x_2030_, v___x_2029_);
    return v___x_2031_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy()
-> *mut LeanObject {
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    v___x_2032_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2_once), _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy___closed__2);
    return v___x_2032_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_2033_: *mut LeanObject,
    mut v_x_2034_: *mut LeanObject,
    mut v_x_2035_: *mut LeanObject,
    mut v_x_2036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2041_: u8 = 0;
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: u8 = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2062_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2037_ = lean_ctor_get(v_x_2033_, 0);
                v_vs_2038_ = lean_ctor_get(v_x_2033_, 1);
                v_isSharedCheck_2062_ = (!lean_is_exclusive(v_x_2033_)) as u8;
                if v_isSharedCheck_2062_ == 0 {
                    v___x_2040_ = v_x_2033_;
                    v_isShared_2041_ = v_isSharedCheck_2062_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2038_);
                    lean_inc(v_ks_2037_);
                    lean_dec(v_x_2033_);
                    v___x_2040_ = lean_box(0);
                    v_isShared_2041_ = v_isSharedCheck_2062_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2042_ = lean_array_get_size(v_ks_2037_);
                v___x_2043_ = lean_nat_dec_lt(v_x_2034_, v___x_2042_);
                if v___x_2043_ == 0 {
                    lean_dec(v_x_2034_);
                    v___x_2044_ = lean_array_push(v_ks_2037_, v_x_2035_);
                    v___x_2045_ = lean_array_push(v_vs_2038_, v_x_2036_);
                    if v_isShared_2041_ == 0 {
                        lean_ctor_set(v___x_2040_, 1, v___x_2045_);
                        lean_ctor_set(v___x_2040_, 0, v___x_2044_);
                        v___x_2047_ = v___x_2040_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2044_);
                        lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2045_);
                        v___x_2047_ = v_reuseFailAlloc_2048_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2049_ = lean_array_fget_borrowed(v_ks_2037_, v_x_2034_);
                    lean_inc(v_k_x27_2049_);
                    lean_inc_ref(v_x_2035_);
                    v___x_2050_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_x_2035_,
                            v_k_x27_2049_,
                        );
                    if v___x_2050_ == 0 {
                        if v_isShared_2041_ == 0 {
                            v___x_2052_ = v___x_2040_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_ks_2037_);
                            lean_ctor_set(v_reuseFailAlloc_2056_, 1, v_vs_2038_);
                            v___x_2052_ = v_reuseFailAlloc_2056_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2057_ = lean_array_fset(v_ks_2037_, v_x_2034_, v_x_2035_);
                        v___x_2058_ = lean_array_fset(v_vs_2038_, v_x_2034_, v_x_2036_);
                        lean_dec(v_x_2034_);
                        if v_isShared_2041_ == 0 {
                            lean_ctor_set(v___x_2040_, 1, v___x_2058_);
                            lean_ctor_set(v___x_2040_, 0, v___x_2057_);
                            v___x_2060_ = v___x_2040_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2061_, 0, v___x_2057_);
                            lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2058_);
                            v___x_2060_ = v_reuseFailAlloc_2061_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2047_;
            }
            3 => {
                v___x_2053_ = lean_unsigned_to_nat(1);
                v___x_2054_ = lean_nat_add(v_x_2034_, v___x_2053_);
                lean_dec(v_x_2034_);
                v_x_2033_ = v___x_2052_;
                v_x_2034_ = v___x_2054_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(
    mut v_n_2063_: *mut LeanObject,
    mut v_k_2064_: *mut LeanObject,
    mut v_v_2065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    v___x_2066_ = lean_unsigned_to_nat(0);
    v___x_2067_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_n_2063_, v___x_2066_, v_k_2064_, v_v_2065_);
    return v___x_2067_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_2068_: usize = 0;
    let mut v___x_2069_: usize = 0;
    let mut v___x_2070_: usize = 0;
    v___x_2068_ = 5usize;
    v___x_2069_ = 1usize;
    v___x_2070_ = lean_usize_shift_left(v___x_2069_, v___x_2068_);
    return v___x_2070_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_2071_: usize = 0;
    let mut v___x_2072_: usize = 0;
    let mut v___x_2073_: usize = 0;
    v___x_2071_ = 1usize;
    v___x_2072_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__0);
    v___x_2073_ = lean_usize_sub(v___x_2072_, v___x_2071_);
    return v___x_2073_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    v___x_2074_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2074_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(
    mut v_x_2075_: *mut LeanObject,
    mut v_x_2076_: usize,
    mut v_x_2077_: usize,
    mut v_x_2078_: *mut LeanObject,
    mut v_x_2079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: usize = 0;
    let mut v___x_2082_: usize = 0;
    let mut v___x_2083_: usize = 0;
    let mut v___x_2084_: usize = 0;
    let mut v_j_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: u8 = 0;
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v_v_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2104_: u8 = 0;
    let mut v___x_2105_: u8 = 0;
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2111_: u8 = 0;
    let mut v_node_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2115_: u8 = 0;
    let mut v___x_2116_: usize = 0;
    let mut v___x_2117_: usize = 0;
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2122_: u8 = 0;
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2124_: u8 = 0;
    let mut v_unused_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2130_: u8 = 0;
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2135_: u8 = 0;
    let mut v_ks_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: usize = 0;
    let mut v___x_2142_: u8 = 0;
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: u8 = 0;
    let mut v_reuseFailAlloc_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2075_) == 0 {
                    v_es_2080_ = lean_ctor_get(v_x_2075_, 0);
                    v___x_2081_ = 5usize;
                    v___x_2082_ = 1usize;
                    v___x_2083_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
                    v___x_2084_ = lean_usize_land(v_x_2076_, v___x_2083_);
                    v_j_2085_ = lean_usize_to_nat(v___x_2084_);
                    v___x_2086_ = lean_array_get_size(v_es_2080_);
                    v___x_2087_ = lean_nat_dec_lt(v_j_2085_, v___x_2086_);
                    if v___x_2087_ == 0 {
                        lean_dec(v_j_2085_);
                        lean_dec(v_x_2079_);
                        lean_dec_ref(v_x_2078_);
                        return v_x_2075_;
                    } else {
                        lean_inc_ref(v_es_2080_);
                        v_isSharedCheck_2124_ = (!lean_is_exclusive(v_x_2075_)) as u8;
                        if v_isSharedCheck_2124_ == 0 {
                            v_unused_2125_ = lean_ctor_get(v_x_2075_, 0);
                            lean_dec(v_unused_2125_);
                            v___x_2089_ = v_x_2075_;
                            v_isShared_2090_ = v_isSharedCheck_2124_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2075_);
                            v___x_2089_ = lean_box(0);
                            v_isShared_2090_ = v_isSharedCheck_2124_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2126_ = lean_ctor_get(v_x_2075_, 0);
                    v_vs_2127_ = lean_ctor_get(v_x_2075_, 1);
                    v_isSharedCheck_2147_ = (!lean_is_exclusive(v_x_2075_)) as u8;
                    if v_isSharedCheck_2147_ == 0 {
                        v___x_2129_ = v_x_2075_;
                        v_isShared_2130_ = v_isSharedCheck_2147_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2127_);
                        lean_inc(v_ks_2126_);
                        lean_dec(v_x_2075_);
                        v___x_2129_ = lean_box(0);
                        v_isShared_2130_ = v_isSharedCheck_2147_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2091_ = lean_array_fget(v_es_2080_, v_j_2085_);
                v___x_2092_ = lean_box(0);
                v_xs_x27_2093_ = lean_array_fset(v_es_2080_, v_j_2085_, v___x_2092_);
                match lean_obj_tag(v_v_2091_) {
                    0 => {
                        v_key_2100_ = lean_ctor_get(v_v_2091_, 0);
                        v_val_2101_ = lean_ctor_get(v_v_2091_, 1);
                        v_isSharedCheck_2111_ = (!lean_is_exclusive(v_v_2091_)) as u8;
                        if v_isSharedCheck_2111_ == 0 {
                            v___x_2103_ = v_v_2091_;
                            v_isShared_2104_ = v_isSharedCheck_2111_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2101_);
                            lean_inc(v_key_2100_);
                            lean_dec(v_v_2091_);
                            v___x_2103_ = lean_box(0);
                            v_isShared_2104_ = v_isSharedCheck_2111_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2112_ = lean_ctor_get(v_v_2091_, 0);
                        v_isSharedCheck_2122_ = (!lean_is_exclusive(v_v_2091_)) as u8;
                        if v_isSharedCheck_2122_ == 0 {
                            v___x_2114_ = v_v_2091_;
                            v_isShared_2115_ = v_isSharedCheck_2122_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2112_);
                            lean_dec(v_v_2091_);
                            v___x_2114_ = lean_box(0);
                            v_isShared_2115_ = v_isSharedCheck_2122_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2123_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2123_, 0, v_x_2078_);
                        lean_ctor_set(v___x_2123_, 1, v_x_2079_);
                        v___y_2095_ = v___x_2123_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2096_ = lean_array_fset(v_xs_x27_2093_, v_j_2085_, v___y_2095_);
                lean_dec(v_j_2085_);
                if v_isShared_2090_ == 0 {
                    lean_ctor_set(v___x_2089_, 0, v___x_2096_);
                    v___x_2098_ = v___x_2089_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2096_);
                    v___x_2098_ = v_reuseFailAlloc_2099_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2098_;
            }
            4 => {
                lean_inc(v_key_2100_);
                lean_inc_ref(v_x_2078_);
                v___x_2105_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                    v_x_2078_,
                    v_key_2100_,
                );
                if v___x_2105_ == 0 {
                    lean_del_object(v___x_2103_);
                    v___x_2106_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2100_,
                        v_val_2101_,
                        v_x_2078_,
                        v_x_2079_,
                    );
                    v___x_2107_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2107_, 0, v___x_2106_);
                    v___y_2095_ = v___x_2107_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2101_);
                    lean_dec(v_key_2100_);
                    if v_isShared_2104_ == 0 {
                        lean_ctor_set(v___x_2103_, 1, v_x_2079_);
                        lean_ctor_set(v___x_2103_, 0, v_x_2078_);
                        v___x_2109_ = v___x_2103_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2110_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_x_2078_);
                        lean_ctor_set(v_reuseFailAlloc_2110_, 1, v_x_2079_);
                        v___x_2109_ = v_reuseFailAlloc_2110_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2095_ = v___x_2109_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2116_ = lean_usize_shift_right(v_x_2076_, v___x_2081_);
                v___x_2117_ = lean_usize_add(v_x_2077_, v___x_2082_);
                v___x_2118_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_node_2112_, v___x_2116_, v___x_2117_, v_x_2078_, v_x_2079_);
                if v_isShared_2115_ == 0 {
                    lean_ctor_set(v___x_2114_, 0, v___x_2118_);
                    v___x_2120_ = v___x_2114_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2121_, 0, v___x_2118_);
                    v___x_2120_ = v_reuseFailAlloc_2121_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2095_ = v___x_2120_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2130_ == 0 {
                    v___x_2132_ = v___x_2129_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_ks_2126_);
                    lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_vs_2127_);
                    v___x_2132_ = v_reuseFailAlloc_2146_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2133_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v___x_2132_, v_x_2078_, v_x_2079_);
                v___x_2141_ = 7usize;
                v___x_2142_ = lean_usize_dec_le(v___x_2141_, v_x_2077_);
                if v___x_2142_ == 0 {
                    v___x_2143_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2133_);
                    v___x_2144_ = lean_unsigned_to_nat(4);
                    v___x_2145_ = lean_nat_dec_lt(v___x_2143_, v___x_2144_);
                    lean_dec(v___x_2143_);
                    v___y_2135_ = v___x_2145_;
                    state = 10;
                    continue;
                } else {
                    v___y_2135_ = v___x_2142_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2135_ == 0 {
                    v_ks_2136_ = lean_ctor_get(v_newNode_2133_, 0);
                    lean_inc_ref(v_ks_2136_);
                    v_vs_2137_ = lean_ctor_get(v_newNode_2133_, 1);
                    lean_inc_ref(v_vs_2137_);
                    lean_dec_ref(v_newNode_2133_);
                    v___x_2138_ = lean_unsigned_to_nat(0);
                    v___x_2139_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__2);
                    v___x_2140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_x_2077_, v_ks_2136_, v_vs_2137_, v___x_2138_, v___x_2139_);
                    lean_dec_ref(v_vs_2137_);
                    lean_dec_ref(v_ks_2136_);
                    return v___x_2140_;
                } else {
                    return v_newNode_2133_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(
    mut v_depth_2148_: usize,
    mut v_keys_2149_: *mut LeanObject,
    mut v_vals_2150_: *mut LeanObject,
    mut v_i_2151_: *mut LeanObject,
    mut v_entries_2152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: u8 = 0;
    let mut v_k_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u64 = 0;
    let mut v_h_2158_: usize = 0;
    let mut v___x_2159_: usize = 0;
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: usize = 0;
    let mut v___x_2162_: usize = 0;
    let mut v___x_2163_: usize = 0;
    let mut v_h_2164_: usize = 0;
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2153_ = lean_array_get_size(v_keys_2149_);
                v___x_2154_ = lean_nat_dec_lt(v_i_2151_, v___x_2153_);
                if v___x_2154_ == 0 {
                    lean_dec(v_i_2151_);
                    return v_entries_2152_;
                } else {
                    v_k_2155_ = lean_array_fget_borrowed(v_keys_2149_, v_i_2151_);
                    v_v_2156_ = lean_array_fget_borrowed(v_vals_2150_, v_i_2151_);
                    v___x_2157_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                            v_k_2155_,
                        );
                    v_h_2158_ = lean_uint64_to_usize(v___x_2157_);
                    v___x_2159_ = 5usize;
                    v___x_2160_ = lean_unsigned_to_nat(1);
                    v___x_2161_ = 1usize;
                    v___x_2162_ = lean_usize_sub(v_depth_2148_, v___x_2161_);
                    v___x_2163_ = lean_usize_mul(v___x_2159_, v___x_2162_);
                    v_h_2164_ = lean_usize_shift_right(v_h_2158_, v___x_2163_);
                    v___x_2165_ = lean_nat_add(v_i_2151_, v___x_2160_);
                    lean_dec(v_i_2151_);
                    lean_inc(v_v_2156_);
                    lean_inc(v_k_2155_);
                    v___x_2166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_entries_2152_, v_h_2164_, v_depth_2148_, v_k_2155_, v_v_2156_);
                    v_i_2151_ = v___x_2165_;
                    v_entries_2152_ = v___x_2166_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_depth_2168_: *mut LeanObject,
    mut v_keys_2169_: *mut LeanObject,
    mut v_vals_2170_: *mut LeanObject,
    mut v_i_2171_: *mut LeanObject,
    mut v_entries_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2173_: usize = 0;
    let mut v_res_2174_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2173_ = lean_unbox_usize(v_depth_2168_);
    lean_dec(v_depth_2168_);
    v_res_2174_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_boxed_2173_, v_keys_2169_, v_vals_2170_, v_i_2171_, v_entries_2172_);
    lean_dec_ref(v_vals_2170_);
    lean_dec_ref(v_keys_2169_);
    return v_res_2174_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___boxed(
    mut v_x_2175_: *mut LeanObject,
    mut v_x_2176_: *mut LeanObject,
    mut v_x_2177_: *mut LeanObject,
    mut v_x_2178_: *mut LeanObject,
    mut v_x_2179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2171__boxed_2180_: usize = 0;
    let mut v_x_2172__boxed_2181_: usize = 0;
    let mut v_res_2182_: *mut LeanObject = core::ptr::null_mut();
    v_x_2171__boxed_2180_ = lean_unbox_usize(v_x_2176_);
    lean_dec(v_x_2176_);
    v_x_2172__boxed_2181_ = lean_unbox_usize(v_x_2177_);
    lean_dec(v_x_2177_);
    v_res_2182_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_2175_, v_x_2171__boxed_2180_, v_x_2172__boxed_2181_, v_x_2178_, v_x_2179_);
    return v_res_2182_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(
    mut v_x_2183_: *mut LeanObject,
    mut v_x_2184_: *mut LeanObject,
    mut v_x_2185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2186_: u64 = 0;
    let mut v___x_2187_: usize = 0;
    let mut v___x_2188_: usize = 0;
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    v___x_2186_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_2184_);
    v___x_2187_ = lean_uint64_to_usize(v___x_2186_);
    v___x_2188_ = 1usize;
    v___x_2189_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_2183_, v___x_2187_, v___x_2188_, v_x_2184_, v_x_2185_);
    return v___x_2189_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(
    mut v_keys_2190_: *mut LeanObject,
    mut v_i_2191_: *mut LeanObject,
    mut v_k_2192_: *mut LeanObject,
    mut v_k_u2080_2193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: u8 = 0;
    let mut v_k_x27_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: u8 = 0;
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2194_ = lean_array_get_size(v_keys_2190_);
                v___x_2195_ = lean_nat_dec_lt(v_i_2191_, v___x_2194_);
                if v___x_2195_ == 0 {
                    lean_dec_ref(v_k_2192_);
                    lean_dec(v_i_2191_);
                    lean_inc_ref(v_k_u2080_2193_);
                    return v_k_u2080_2193_;
                } else {
                    v_k_x27_2196_ = lean_array_fget_borrowed(v_keys_2190_, v_i_2191_);
                    lean_inc(v_k_x27_2196_);
                    lean_inc_ref(v_k_2192_);
                    v___x_2197_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_k_2192_,
                            v_k_x27_2196_,
                        );
                    if v___x_2197_ == 0 {
                        v___x_2198_ = lean_unsigned_to_nat(1);
                        v___x_2199_ = lean_nat_add(v_i_2191_, v___x_2198_);
                        lean_dec(v_i_2191_);
                        v_i_2191_ = v___x_2199_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_2192_);
                        lean_dec(v_i_2191_);
                        lean_inc(v_k_x27_2196_);
                        return v_k_x27_2196_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg___boxed(
    mut v_keys_2201_: *mut LeanObject,
    mut v_i_2202_: *mut LeanObject,
    mut v_k_2203_: *mut LeanObject,
    mut v_k_u2080_2204_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2205_: *mut LeanObject = core::ptr::null_mut();
    v_res_2205_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_2201_, v_i_2202_, v_k_2203_, v_k_u2080_2204_);
    lean_dec_ref(v_k_u2080_2204_);
    lean_dec_ref(v_keys_2201_);
    return v_res_2205_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(
    mut v_x_2206_: *mut LeanObject,
    mut v_x_2207_: usize,
    mut v_x_2208_: *mut LeanObject,
    mut v_x_2209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: usize = 0;
    let mut v___x_2213_: usize = 0;
    let mut v___x_2214_: usize = 0;
    let mut v_j_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v_node_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: usize = 0;
    let mut v_ks_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2206_) == 0 {
                    v_es_2210_ = lean_ctor_get(v_x_2206_, 0);
                    lean_inc_ref(v_es_2210_);
                    lean_dec_ref_known(v_x_2206_, 1);
                    v___x_2211_ = lean_box(2);
                    v___x_2212_ = 5usize;
                    v___x_2213_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
                    v___x_2214_ = lean_usize_land(v_x_2207_, v___x_2213_);
                    v_j_2215_ = lean_usize_to_nat(v___x_2214_);
                    v___x_2216_ = lean_array_get(v___x_2211_, v_es_2210_, v_j_2215_);
                    lean_dec(v_j_2215_);
                    lean_dec_ref(v_es_2210_);
                    match lean_obj_tag(v___x_2216_) {
                        0 => {
                            v_key_2217_ = lean_ctor_get(v___x_2216_, 0);
                            lean_inc_n(v_key_2217_, 2);
                            lean_dec_ref_known(v___x_2216_, 2);
                            v___x_2218_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                                    v_x_2208_,
                                    v_key_2217_,
                                );
                            if v___x_2218_ == 0 {
                                lean_dec(v_key_2217_);
                                lean_inc_ref(v_x_2209_);
                                return v_x_2209_;
                            } else {
                                return v_key_2217_;
                            }
                        }
                        1 => {
                            v_node_2219_ = lean_ctor_get(v___x_2216_, 0);
                            lean_inc(v_node_2219_);
                            lean_dec_ref_known(v___x_2216_, 1);
                            v___x_2220_ = lean_usize_shift_right(v_x_2207_, v___x_2212_);
                            v_x_2206_ = v_node_2219_;
                            v_x_2207_ = v___x_2220_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_x_2208_);
                            lean_inc_ref(v_x_2209_);
                            return v_x_2209_;
                        }
                    }
                } else {
                    v_ks_2222_ = lean_ctor_get(v_x_2206_, 0);
                    lean_inc_ref(v_ks_2222_);
                    lean_dec_ref_known(v_x_2206_, 2);
                    v___x_2223_ = lean_unsigned_to_nat(0);
                    v___x_2224_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_ks_2222_, v___x_2223_, v_x_2208_, v_x_2209_);
                    lean_dec_ref(v_ks_2222_);
                    return v___x_2224_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg___boxed(
    mut v_x_2225_: *mut LeanObject,
    mut v_x_2226_: *mut LeanObject,
    mut v_x_2227_: *mut LeanObject,
    mut v_x_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2365__boxed_2229_: usize = 0;
    let mut v_res_2230_: *mut LeanObject = core::ptr::null_mut();
    v_x_2365__boxed_2229_ = lean_unbox_usize(v_x_2226_);
    lean_dec(v_x_2226_);
    v_res_2230_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_2225_, v_x_2365__boxed_2229_, v_x_2227_, v_x_2228_);
    lean_dec_ref(v_x_2228_);
    return v_res_2230_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Sym_share1___redArg(
    mut v_e_2231_: *mut LeanObject,
    mut v_a_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u64 = 0;
    let mut v___x_2238_: usize = 0;
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2253_: u8 = 0;
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2256_: u8 = 0;
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2234_ = lean_st_ref_get(v_a_2232_);
                v_share_2235_ = lean_ctor_get(v___x_2234_, 0);
                lean_inc_ref(v_share_2235_);
                lean_dec(v___x_2234_);
                v___x_2236_ =
                    l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
                v___x_2237_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(
                    v_e_2231_,
                );
                v___x_2238_ = lean_uint64_to_usize(v___x_2237_);
                lean_inc_ref(v_e_2231_);
                v___x_2239_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_2235_, v___x_2238_, v_e_2231_, v___x_2236_);
                v___x_2240_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v___x_2239_,
                        v___x_2236_,
                    );
                if v___x_2240_ == 0 {
                    lean_dec_ref(v_e_2231_);
                    v___x_2241_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2241_, 0, v___x_2239_);
                    return v___x_2241_;
                } else {
                    lean_dec_ref(v___x_2239_);
                    v___x_2242_ = lean_st_ref_take(v_a_2232_);
                    v_share_2243_ = lean_ctor_get(v___x_2242_, 0);
                    v_maxFVar_2244_ = lean_ctor_get(v___x_2242_, 1);
                    v_proofInstInfo_2245_ = lean_ctor_get(v___x_2242_, 2);
                    v_inferType_2246_ = lean_ctor_get(v___x_2242_, 3);
                    v_getLevel_2247_ = lean_ctor_get(v___x_2242_, 4);
                    v_congrInfo_2248_ = lean_ctor_get(v___x_2242_, 5);
                    v_defEqI_2249_ = lean_ctor_get(v___x_2242_, 6);
                    v_extensions_2250_ = lean_ctor_get(v___x_2242_, 7);
                    v_issues_2251_ = lean_ctor_get(v___x_2242_, 8);
                    v_canon_2252_ = lean_ctor_get(v___x_2242_, 9);
                    v_debug_2253_ = lean_ctor_get_uint8(
                        v___x_2242_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_isSharedCheck_2264_ = (!lean_is_exclusive(v___x_2242_)) as u8;
                    if v_isSharedCheck_2264_ == 0 {
                        v___x_2255_ = v___x_2242_;
                        v_isShared_2256_ = v_isSharedCheck_2264_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_canon_2252_);
                        lean_inc(v_issues_2251_);
                        lean_inc(v_extensions_2250_);
                        lean_inc(v_defEqI_2249_);
                        lean_inc(v_congrInfo_2248_);
                        lean_inc(v_getLevel_2247_);
                        lean_inc(v_inferType_2246_);
                        lean_inc(v_proofInstInfo_2245_);
                        lean_inc(v_maxFVar_2244_);
                        lean_inc(v_share_2243_);
                        lean_dec(v___x_2242_);
                        v___x_2255_ = lean_box(0);
                        v_isShared_2256_ = v_isSharedCheck_2264_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2257_ = lean_box(0);
                lean_inc_ref(v_e_2231_);
                v___x_2258_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_share_2243_, v_e_2231_, v___x_2257_);
                if v_isShared_2256_ == 0 {
                    lean_ctor_set(v___x_2255_, 0, v___x_2258_);
                    v___x_2260_ = v___x_2255_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 0, v___x_2258_);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_maxFVar_2244_);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 2, v_proofInstInfo_2245_);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 3, v_inferType_2246_);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 4, v_getLevel_2247_);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 5, v_congrInfo_2248_);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 6, v_defEqI_2249_);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 7, v_extensions_2250_);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 8, v_issues_2251_);
                    lean_ctor_set(v_reuseFailAlloc_2263_, 9, v_canon_2252_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2263_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_2253_,
                    );
                    v___x_2260_ = v_reuseFailAlloc_2263_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2261_ = lean_st_ref_set(v_a_2232_, v___x_2260_);
                v___x_2262_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2262_, 0, v_e_2231_);
                return v___x_2262_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Sym_share1___redArg___boxed(
    mut v_e_2265_: *mut LeanObject,
    mut v_a_2266_: *mut LeanObject,
    mut v_a_2267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2268_: *mut LeanObject = core::ptr::null_mut();
    v_res_2268_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_2265_, v_a_2266_);
    lean_dec(v_a_2266_);
    return v_res_2268_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Sym_share1(
    mut v_e_2269_: *mut LeanObject,
    mut v_a_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
    mut v_a_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
    mut v_a_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    v___x_2277_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v_e_2269_, v_a_2271_);
    return v___x_2277_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Sym_share1___boxed(
    mut v_e_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2286_: *mut LeanObject = core::ptr::null_mut();
    v_res_2286_ = l_Lean_Meta_Sym_Internal_Sym_share1(
        v_e_2278_, v_a_2279_, v_a_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_,
    );
    lean_dec(v_a_2284_);
    lean_dec_ref(v_a_2283_);
    lean_dec(v_a_2282_);
    lean_dec_ref(v_a_2281_);
    lean_dec(v_a_2280_);
    lean_dec_ref(v_a_2279_);
    return v_res_2286_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(
    mut v_00_u03b2_2287_: *mut LeanObject,
    mut v_x_2288_: *mut LeanObject,
    mut v_x_2289_: usize,
    mut v_x_2290_: *mut LeanObject,
    mut v_x_2291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    v___x_2292_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_x_2288_, v_x_2289_, v_x_2290_, v_x_2291_);
    return v___x_2292_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___boxed(
    mut v_00_u03b2_2293_: *mut LeanObject,
    mut v_x_2294_: *mut LeanObject,
    mut v_x_2295_: *mut LeanObject,
    mut v_x_2296_: *mut LeanObject,
    mut v_x_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2455__boxed_2298_: usize = 0;
    let mut v_res_2299_: *mut LeanObject = core::ptr::null_mut();
    v_x_2455__boxed_2298_ = lean_unbox_usize(v_x_2295_);
    lean_dec(v_x_2295_);
    v_res_2299_ =
        l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0(
            v_00_u03b2_2293_,
            v_x_2294_,
            v_x_2455__boxed_2298_,
            v_x_2296_,
            v_x_2297_,
        );
    lean_dec_ref(v_x_2297_);
    return v_res_2299_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1(
    mut v_00_u03b2_2300_: *mut LeanObject,
    mut v_x_2301_: *mut LeanObject,
    mut v_x_2302_: *mut LeanObject,
    mut v_x_2303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    v___x_2304_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(
            v_x_2301_, v_x_2302_, v_x_2303_,
        );
    return v___x_2304_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(
    mut v_00_u03b2_2305_: *mut LeanObject,
    mut v_keys_2306_: *mut LeanObject,
    mut v_vals_2307_: *mut LeanObject,
    mut v_heq_2308_: *mut LeanObject,
    mut v_i_2309_: *mut LeanObject,
    mut v_k_2310_: *mut LeanObject,
    mut v_k_u2080_2311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    v___x_2312_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___redArg(v_keys_2306_, v_i_2309_, v_k_2310_, v_k_u2080_2311_);
    return v___x_2312_;
}
pub unsafe fn l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0___boxed(
    mut v_00_u03b2_2313_: *mut LeanObject,
    mut v_keys_2314_: *mut LeanObject,
    mut v_vals_2315_: *mut LeanObject,
    mut v_heq_2316_: *mut LeanObject,
    mut v_i_2317_: *mut LeanObject,
    mut v_k_2318_: *mut LeanObject,
    mut v_k_u2080_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2320_: *mut LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lean_PersistentHashMap_findKeyDAtAux___at___00Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0_spec__0(v_00_u03b2_2313_, v_keys_2314_, v_vals_2315_, v_heq_2316_, v_i_2317_, v_k_2318_, v_k_u2080_2319_);
    lean_dec_ref(v_k_u2080_2319_);
    lean_dec_ref(v_vals_2315_);
    lean_dec_ref(v_keys_2314_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(
    mut v_00_u03b2_2321_: *mut LeanObject,
    mut v_x_2322_: *mut LeanObject,
    mut v_x_2323_: usize,
    mut v_x_2324_: usize,
    mut v_x_2325_: *mut LeanObject,
    mut v_x_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg(v_x_2322_, v_x_2323_, v_x_2324_, v_x_2325_, v_x_2326_);
    return v___x_2327_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___boxed(
    mut v_00_u03b2_2328_: *mut LeanObject,
    mut v_x_2329_: *mut LeanObject,
    mut v_x_2330_: *mut LeanObject,
    mut v_x_2331_: *mut LeanObject,
    mut v_x_2332_: *mut LeanObject,
    mut v_x_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2479__boxed_2334_: usize = 0;
    let mut v_x_2480__boxed_2335_: usize = 0;
    let mut v_res_2336_: *mut LeanObject = core::ptr::null_mut();
    v_x_2479__boxed_2334_ = lean_unbox_usize(v_x_2330_);
    lean_dec(v_x_2330_);
    v_x_2480__boxed_2335_ = lean_unbox_usize(v_x_2331_);
    lean_dec(v_x_2331_);
    v_res_2336_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2(v_00_u03b2_2328_, v_x_2329_, v_x_2479__boxed_2334_, v_x_2480__boxed_2335_, v_x_2332_, v_x_2333_);
    return v_res_2336_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2337_: *mut LeanObject,
    mut v_n_2338_: *mut LeanObject,
    mut v_k_2339_: *mut LeanObject,
    mut v_v_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    v___x_2341_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3___redArg(v_n_2338_, v_k_2339_, v_v_2340_);
    return v___x_2341_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2342_: *mut LeanObject,
    mut v_depth_2343_: usize,
    mut v_keys_2344_: *mut LeanObject,
    mut v_vals_2345_: *mut LeanObject,
    mut v_heq_2346_: *mut LeanObject,
    mut v_i_2347_: *mut LeanObject,
    mut v_entries_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
    v___x_2349_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___redArg(v_depth_2343_, v_keys_2344_, v_vals_2345_, v_i_2347_, v_entries_2348_);
    return v___x_2349_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b2_2350_: *mut LeanObject,
    mut v_depth_2351_: *mut LeanObject,
    mut v_keys_2352_: *mut LeanObject,
    mut v_vals_2353_: *mut LeanObject,
    mut v_heq_2354_: *mut LeanObject,
    mut v_i_2355_: *mut LeanObject,
    mut v_entries_2356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2357_: usize = 0;
    let mut v_res_2358_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2357_ = lean_unbox_usize(v_depth_2351_);
    lean_dec(v_depth_2351_);
    v_res_2358_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__4(v_00_u03b2_2350_, v_depth_boxed_2357_, v_keys_2352_, v_vals_2353_, v_heq_2354_, v_i_2355_, v_entries_2356_);
    lean_dec_ref(v_vals_2353_);
    lean_dec_ref(v_keys_2352_);
    return v_res_2358_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2359_: *mut LeanObject,
    mut v_x_2360_: *mut LeanObject,
    mut v_x_2361_: *mut LeanObject,
    mut v_x_2362_: *mut LeanObject,
    mut v_x_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    v___x_2364_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2360_, v_x_2361_, v_x_2362_, v_x_2363_);
    return v___x_2364_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    v___x_2365_ = l_Lean_Meta_Sym_instInhabitedSymM(lean_box(0));
    return v___x_2365_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(
    mut v_msg_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
    mut v___y_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756__overap_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    v___x_2374_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___closed__0,
    );
    v___x_756__overap_2375_ = lean_panic_fn_borrowed(v___x_2374_, v_msg_2366_);
    lean_inc(v___y_2372_);
    lean_inc_ref(v___y_2371_);
    lean_inc(v___y_2370_);
    lean_inc_ref(v___y_2369_);
    lean_inc(v___y_2368_);
    lean_inc_ref(v___y_2367_);
    v___x_2376_ = lean_apply_7(
        v___x_756__overap_2375_,
        v___y_2367_,
        v___y_2368_,
        v___y_2369_,
        v___y_2370_,
        v___y_2371_,
        v___y_2372_,
        lean_box(0),
    );
    return v___x_2376_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0___boxed(
    mut v_msg_2377_: *mut LeanObject,
    mut v___y_2378_: *mut LeanObject,
    mut v___y_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2385_: *mut LeanObject = core::ptr::null_mut();
    v_res_2385_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(
        v_msg_2377_,
        v___y_2378_,
        v___y_2379_,
        v___y_2380_,
        v___y_2381_,
        v___y_2382_,
        v___y_2383_,
    );
    lean_dec(v___y_2383_);
    lean_dec_ref(v___y_2382_);
    lean_dec(v___y_2381_);
    lean_dec_ref(v___y_2380_);
    lean_dec(v___y_2379_);
    lean_dec_ref(v___y_2378_);
    return v_res_2385_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3() -> *mut LeanObject {
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    v___x_2389_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__2;
    v___x_2390_ = lean_unsigned_to_nat(2);
    v___x_2391_ = lean_unsigned_to_nat(42);
    v___x_2392_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__1;
    v___x_2393_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0;
    v___x_2394_ = l_mkPanicMessageWithDecl(
        v___x_2393_,
        v___x_2392_,
        v___x_2391_,
        v___x_2390_,
        v___x_2389_,
    );
    return v___x_2394_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Sym_assertShared(
    mut v_e_2395_: *mut LeanObject,
    mut v_a_2396_: *mut LeanObject,
    mut v_a_2397_: *mut LeanObject,
    mut v_a_2398_: *mut LeanObject,
    mut v_a_2399_: *mut LeanObject,
    mut v_a_2400_: *mut LeanObject,
    mut v_a_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: u64 = 0;
    let mut v___x_2407_: usize = 0;
    let mut v___x_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: u8 = 0;
    v___x_2403_ = lean_st_ref_get(v_a_2397_);
    v_share_2404_ = lean_ctor_get(v___x_2403_, 0);
    lean_inc_ref(v_share_2404_);
    lean_dec(v___x_2403_);
    v___x_2405_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
    v___x_2406_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_2395_);
    v___x_2407_ = lean_uint64_to_usize(v___x_2406_);
    lean_inc_ref(v_e_2395_);
    v___x_2408_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_share_2404_, v___x_2407_, v_e_2395_, v___x_2405_);
    v___x_2409_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2408_,
        v_e_2395_,
    );
    lean_dec_ref(v_e_2395_);
    lean_dec_ref(v___x_2408_);
    if v___x_2409_ == 0 {
        let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
        v___x_2410_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3),
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3_once),
            _init_l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__3,
        );
        v___x_2411_ = l_panic___at___00Lean_Meta_Sym_Internal_Sym_assertShared_spec__0(
            v___x_2410_,
            v_a_2396_,
            v_a_2397_,
            v_a_2398_,
            v_a_2399_,
            v_a_2400_,
            v_a_2401_,
        );
        return v___x_2411_;
    } else {
        let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
        v___x_2412_ = lean_box(0);
        v___x_2413_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2413_, 0, v___x_2412_);
        return v___x_2413_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Sym_assertShared___boxed(
    mut v_e_2414_: *mut LeanObject,
    mut v_a_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
    mut v_a_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
    mut v_a_2421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2422_: *mut LeanObject = core::ptr::null_mut();
    v_res_2422_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
        v_e_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_,
    );
    lean_dec(v_a_2420_);
    lean_dec_ref(v_a_2419_);
    lean_dec(v_a_2418_);
    lean_dec_ref(v_a_2417_);
    lean_dec(v_a_2416_);
    lean_dec_ref(v_a_2415_);
    return v_res_2422_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2() -> *mut LeanObject
{
    let mut v___f_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    v___f_2433_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__1;
    v___f_2434_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__0;
    v___x_2435_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___f_2434_, v___f_2433_);
    return v___x_2435_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(
    mut v_k_2436_: *mut LeanObject,
    mut v_a_2437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2450_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2459_: u8 = 0;
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2474_: u8 = 0;
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2477_: u8 = 0;
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2483_: u8 = 0;
    let mut v_unused_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2439_ = lean_st_ref_take(v_a_2437_);
                v_share_2440_ = lean_ctor_get(v___x_2439_, 0);
                v_maxFVar_2441_ = lean_ctor_get(v___x_2439_, 1);
                v_proofInstInfo_2442_ = lean_ctor_get(v___x_2439_, 2);
                v_inferType_2443_ = lean_ctor_get(v___x_2439_, 3);
                v_getLevel_2444_ = lean_ctor_get(v___x_2439_, 4);
                v_congrInfo_2445_ = lean_ctor_get(v___x_2439_, 5);
                v_defEqI_2446_ = lean_ctor_get(v___x_2439_, 6);
                v_extensions_2447_ = lean_ctor_get(v___x_2439_, 7);
                v_issues_2448_ = lean_ctor_get(v___x_2439_, 8);
                v_canon_2449_ = lean_ctor_get(v___x_2439_, 9);
                v_debug_2450_ = lean_ctor_get_uint8(
                    v___x_2439_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2486_ = (!lean_is_exclusive(v___x_2439_)) as u8;
                if v_isSharedCheck_2486_ == 0 {
                    v___x_2452_ = v___x_2439_;
                    v_isShared_2453_ = v_isSharedCheck_2486_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_2449_);
                    lean_inc(v_issues_2448_);
                    lean_inc(v_extensions_2447_);
                    lean_inc(v_defEqI_2446_);
                    lean_inc(v_congrInfo_2445_);
                    lean_inc(v_getLevel_2444_);
                    lean_inc(v_inferType_2443_);
                    lean_inc(v_proofInstInfo_2442_);
                    lean_inc(v_maxFVar_2441_);
                    lean_inc(v_share_2440_);
                    lean_dec(v___x_2439_);
                    v___x_2452_ = lean_box(0);
                    v_isShared_2453_ = v_isSharedCheck_2486_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2454_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2,
                );
                if v_isShared_2453_ == 0 {
                    lean_ctor_set(v___x_2452_, 0, v___x_2454_);
                    v___x_2456_ = v___x_2452_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2454_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_maxFVar_2441_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 2, v_proofInstInfo_2442_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 3, v_inferType_2443_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 4, v_getLevel_2444_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 5, v_congrInfo_2445_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 6, v_defEqI_2446_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 7, v_extensions_2447_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 8, v_issues_2448_);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 9, v_canon_2449_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2485_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_2450_,
                    );
                    v___x_2456_ = v_reuseFailAlloc_2485_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2457_ = lean_st_ref_set(v_a_2437_, v___x_2456_);
                v___x_2458_ = lean_st_ref_get(v_a_2437_);
                v_debug_2459_ = lean_ctor_get_uint8(
                    v___x_2458_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_2458_);
                v___x_2460_ = lean_box((v_debug_2459_) as usize);
                v___x_2461_ = lean_apply_2(v_k_2436_, v___x_2460_, v_share_2440_);
                v_fst_2462_ = lean_ctor_get(v___x_2461_, 0);
                lean_inc(v_fst_2462_);
                v_snd_2463_ = lean_ctor_get(v___x_2461_, 1);
                lean_inc(v_snd_2463_);
                lean_dec_ref(v___x_2461_);
                v___x_2464_ = lean_st_ref_take(v_a_2437_);
                v_maxFVar_2465_ = lean_ctor_get(v___x_2464_, 1);
                v_proofInstInfo_2466_ = lean_ctor_get(v___x_2464_, 2);
                v_inferType_2467_ = lean_ctor_get(v___x_2464_, 3);
                v_getLevel_2468_ = lean_ctor_get(v___x_2464_, 4);
                v_congrInfo_2469_ = lean_ctor_get(v___x_2464_, 5);
                v_defEqI_2470_ = lean_ctor_get(v___x_2464_, 6);
                v_extensions_2471_ = lean_ctor_get(v___x_2464_, 7);
                v_issues_2472_ = lean_ctor_get(v___x_2464_, 8);
                v_canon_2473_ = lean_ctor_get(v___x_2464_, 9);
                v_debug_2474_ = lean_ctor_get_uint8(
                    v___x_2464_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2483_ = (!lean_is_exclusive(v___x_2464_)) as u8;
                if v_isSharedCheck_2483_ == 0 {
                    v_unused_2484_ = lean_ctor_get(v___x_2464_, 0);
                    lean_dec(v_unused_2484_);
                    v___x_2476_ = v___x_2464_;
                    v_isShared_2477_ = v_isSharedCheck_2483_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_canon_2473_);
                    lean_inc(v_issues_2472_);
                    lean_inc(v_extensions_2471_);
                    lean_inc(v_defEqI_2470_);
                    lean_inc(v_congrInfo_2469_);
                    lean_inc(v_getLevel_2468_);
                    lean_inc(v_inferType_2467_);
                    lean_inc(v_proofInstInfo_2466_);
                    lean_inc(v_maxFVar_2465_);
                    lean_dec(v___x_2464_);
                    v___x_2476_ = lean_box(0);
                    v_isShared_2477_ = v_isSharedCheck_2483_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2477_ == 0 {
                    lean_ctor_set(v___x_2476_, 0, v_snd_2463_);
                    v___x_2479_ = v___x_2476_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2482_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 0, v_snd_2463_);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 1, v_maxFVar_2465_);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 2, v_proofInstInfo_2466_);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 3, v_inferType_2467_);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 4, v_getLevel_2468_);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 5, v_congrInfo_2469_);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 6, v_defEqI_2470_);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 7, v_extensions_2471_);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 8, v_issues_2472_);
                    lean_ctor_set(v_reuseFailAlloc_2482_, 9, v_canon_2473_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2482_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_2474_,
                    );
                    v___x_2479_ = v_reuseFailAlloc_2482_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2480_ = lean_st_ref_set(v_a_2437_, v___x_2479_);
                v___x_2481_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2481_, 0, v_fst_2462_);
                return v___x_2481_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___boxed(
    mut v_k_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2490_: *mut LeanObject = core::ptr::null_mut();
    v_res_2490_ = l_Lean_Meta_Sym_Internal_liftBuilderM___redArg(v_k_2487_, v_a_2488_);
    lean_dec(v_a_2488_);
    return v_res_2490_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_liftBuilderM(
    mut v_00_u03b1_2491_: *mut LeanObject,
    mut v_k_2492_: *mut LeanObject,
    mut v_a_2493_: *mut LeanObject,
    mut v_a_2494_: *mut LeanObject,
    mut v_a_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2511_: u8 = 0;
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2520_: u8 = 0;
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inferType_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_getLevel_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqI_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_extensions_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_issues_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canon_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_2535_: u8 = 0;
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2538_: u8 = 0;
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2544_: u8 = 0;
    let mut v_unused_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2500_ = lean_st_ref_take(v_a_2494_);
                v_share_2501_ = lean_ctor_get(v___x_2500_, 0);
                v_maxFVar_2502_ = lean_ctor_get(v___x_2500_, 1);
                v_proofInstInfo_2503_ = lean_ctor_get(v___x_2500_, 2);
                v_inferType_2504_ = lean_ctor_get(v___x_2500_, 3);
                v_getLevel_2505_ = lean_ctor_get(v___x_2500_, 4);
                v_congrInfo_2506_ = lean_ctor_get(v___x_2500_, 5);
                v_defEqI_2507_ = lean_ctor_get(v___x_2500_, 6);
                v_extensions_2508_ = lean_ctor_get(v___x_2500_, 7);
                v_issues_2509_ = lean_ctor_get(v___x_2500_, 8);
                v_canon_2510_ = lean_ctor_get(v___x_2500_, 9);
                v_debug_2511_ = lean_ctor_get_uint8(
                    v___x_2500_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2547_ = (!lean_is_exclusive(v___x_2500_)) as u8;
                if v_isSharedCheck_2547_ == 0 {
                    v___x_2513_ = v___x_2500_;
                    v_isShared_2514_ = v_isSharedCheck_2547_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_canon_2510_);
                    lean_inc(v_issues_2509_);
                    lean_inc(v_extensions_2508_);
                    lean_inc(v_defEqI_2507_);
                    lean_inc(v_congrInfo_2506_);
                    lean_inc(v_getLevel_2505_);
                    lean_inc(v_inferType_2504_);
                    lean_inc(v_proofInstInfo_2503_);
                    lean_inc(v_maxFVar_2502_);
                    lean_inc(v_share_2501_);
                    lean_dec(v___x_2500_);
                    v___x_2513_ = lean_box(0);
                    v_isShared_2514_ = v_isSharedCheck_2547_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2515_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2_once
                    ),
                    _init_l_Lean_Meta_Sym_Internal_liftBuilderM___redArg___closed__2,
                );
                if v_isShared_2514_ == 0 {
                    lean_ctor_set(v___x_2513_, 0, v___x_2515_);
                    v___x_2517_ = v___x_2513_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2515_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 1, v_maxFVar_2502_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 2, v_proofInstInfo_2503_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 3, v_inferType_2504_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 4, v_getLevel_2505_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 5, v_congrInfo_2506_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 6, v_defEqI_2507_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 7, v_extensions_2508_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 8, v_issues_2509_);
                    lean_ctor_set(v_reuseFailAlloc_2546_, 9, v_canon_2510_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2546_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_2511_,
                    );
                    v___x_2517_ = v_reuseFailAlloc_2546_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2518_ = lean_st_ref_set(v_a_2494_, v___x_2517_);
                v___x_2519_ = lean_st_ref_get(v_a_2494_);
                v_debug_2520_ = lean_ctor_get_uint8(
                    v___x_2519_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                lean_dec(v___x_2519_);
                v___x_2521_ = lean_box((v_debug_2520_) as usize);
                v___x_2522_ = lean_apply_2(v_k_2492_, v___x_2521_, v_share_2501_);
                v_fst_2523_ = lean_ctor_get(v___x_2522_, 0);
                lean_inc(v_fst_2523_);
                v_snd_2524_ = lean_ctor_get(v___x_2522_, 1);
                lean_inc(v_snd_2524_);
                lean_dec_ref(v___x_2522_);
                v___x_2525_ = lean_st_ref_take(v_a_2494_);
                v_maxFVar_2526_ = lean_ctor_get(v___x_2525_, 1);
                v_proofInstInfo_2527_ = lean_ctor_get(v___x_2525_, 2);
                v_inferType_2528_ = lean_ctor_get(v___x_2525_, 3);
                v_getLevel_2529_ = lean_ctor_get(v___x_2525_, 4);
                v_congrInfo_2530_ = lean_ctor_get(v___x_2525_, 5);
                v_defEqI_2531_ = lean_ctor_get(v___x_2525_, 6);
                v_extensions_2532_ = lean_ctor_get(v___x_2525_, 7);
                v_issues_2533_ = lean_ctor_get(v___x_2525_, 8);
                v_canon_2534_ = lean_ctor_get(v___x_2525_, 9);
                v_debug_2535_ = lean_ctor_get_uint8(
                    v___x_2525_,
                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_2544_ = (!lean_is_exclusive(v___x_2525_)) as u8;
                if v_isSharedCheck_2544_ == 0 {
                    v_unused_2545_ = lean_ctor_get(v___x_2525_, 0);
                    lean_dec(v_unused_2545_);
                    v___x_2537_ = v___x_2525_;
                    v_isShared_2538_ = v_isSharedCheck_2544_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_canon_2534_);
                    lean_inc(v_issues_2533_);
                    lean_inc(v_extensions_2532_);
                    lean_inc(v_defEqI_2531_);
                    lean_inc(v_congrInfo_2530_);
                    lean_inc(v_getLevel_2529_);
                    lean_inc(v_inferType_2528_);
                    lean_inc(v_proofInstInfo_2527_);
                    lean_inc(v_maxFVar_2526_);
                    lean_dec(v___x_2525_);
                    v___x_2537_ = lean_box(0);
                    v_isShared_2538_ = v_isSharedCheck_2544_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2538_ == 0 {
                    lean_ctor_set(v___x_2537_, 0, v_snd_2524_);
                    v___x_2540_ = v___x_2537_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_snd_2524_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_maxFVar_2526_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 2, v_proofInstInfo_2527_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 3, v_inferType_2528_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 4, v_getLevel_2529_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 5, v_congrInfo_2530_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 6, v_defEqI_2531_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 7, v_extensions_2532_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 8, v_issues_2533_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 9, v_canon_2534_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2543_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_debug_2535_,
                    );
                    v___x_2540_ = v_reuseFailAlloc_2543_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2541_ = lean_st_ref_set(v_a_2494_, v___x_2540_);
                v___x_2542_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2542_, 0, v_fst_2523_);
                return v___x_2542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_liftBuilderM___boxed(
    mut v_00_u03b1_2548_: *mut LeanObject,
    mut v_k_2549_: *mut LeanObject,
    mut v_a_2550_: *mut LeanObject,
    mut v_a_2551_: *mut LeanObject,
    mut v_a_2552_: *mut LeanObject,
    mut v_a_2553_: *mut LeanObject,
    mut v_a_2554_: *mut LeanObject,
    mut v_a_2555_: *mut LeanObject,
    mut v_a_2556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2557_: *mut LeanObject = core::ptr::null_mut();
    v_res_2557_ = l_Lean_Meta_Sym_Internal_liftBuilderM(
        v_00_u03b1_2548_,
        v_k_2549_,
        v_a_2550_,
        v_a_2551_,
        v_a_2552_,
        v_a_2553_,
        v_a_2554_,
        v_a_2555_,
    );
    lean_dec(v_a_2555_);
    lean_dec_ref(v_a_2554_);
    lean_dec(v_a_2553_);
    lean_dec_ref(v_a_2552_);
    lean_dec(v_a_2551_);
    lean_dec_ref(v_a_2550_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Builder_share1___redArg(
    mut v_e_2558_: *mut LeanObject,
    mut v_a_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: u64 = 0;
    let mut v___x_2562_: usize = 0;
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: u8 = 0;
    v___x_2560_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy;
    v___x_2561_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_e_2558_);
    v___x_2562_ = lean_uint64_to_usize(v___x_2561_);
    lean_inc_ref(v_e_2558_);
    lean_inc_ref(v_a_2559_);
    v___x_2563_ = l_Lean_PersistentHashMap_findKeyDAux___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__0___redArg(v_a_2559_, v___x_2562_, v_e_2558_, v___x_2560_);
    v___x_2564_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_2563_,
        v___x_2560_,
    );
    if v___x_2564_ == 0 {
        let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_2558_);
        v___x_2565_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2565_, 0, v___x_2563_);
        lean_ctor_set(v___x_2565_, 1, v_a_2559_);
        return v___x_2565_;
    } else {
        let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_2563_);
        v___x_2566_ = lean_box(0);
        lean_inc_ref(v_e_2558_);
        v___x_2567_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1___redArg(v_a_2559_, v_e_2558_, v___x_2566_);
        v___x_2568_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2568_, 0, v_e_2558_);
        lean_ctor_set(v___x_2568_, 1, v___x_2567_);
        return v___x_2568_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Builder_share1(
    mut v_e_2569_: *mut LeanObject,
    mut v_a_2570_: u8,
    mut v_a_2571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    v___x_2572_ = l_Lean_Meta_Sym_Internal_Builder_share1___redArg(v_e_2569_, v_a_2571_);
    return v___x_2572_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Builder_share1___boxed(
    mut v_e_2573_: *mut LeanObject,
    mut v_a_2574_: *mut LeanObject,
    mut v_a_2575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2576_: u8 = 0;
    let mut v_res_2577_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2576_ = (lean_unbox(v_a_2574_) as u8);
    v_res_2577_ = l_Lean_Meta_Sym_Internal_Builder_share1(v_e_2573_, v_a_boxed_2576_, v_a_2575_);
    return v_res_2577_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(
    mut v_msg_2585_: *mut LeanObject,
    mut v___y_2586_: u8,
    mut v___y_2587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692__overap_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    v___f_2588_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0;
    v___f_2589_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1;
    v___f_2590_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2;
    v___f_2591_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3;
    v___f_2592_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4;
    v___f_2593_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5;
    v___f_2594_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6;
    v___x_2595_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2595_, 0, v___f_2588_);
    lean_ctor_set(v___x_2595_, 1, v___f_2589_);
    v___x_2596_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2596_, 0, v___x_2595_);
    lean_ctor_set(v___x_2596_, 1, v___f_2590_);
    lean_ctor_set(v___x_2596_, 2, v___f_2591_);
    lean_ctor_set(v___x_2596_, 3, v___f_2592_);
    lean_ctor_set(v___x_2596_, 4, v___f_2593_);
    v___x_2597_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2597_, 0, v___x_2596_);
    lean_ctor_set(v___x_2597_, 1, v___f_2594_);
    lean_inc_ref_n(v___x_2597_, 6);
    v___f_2598_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2598_, 0, v___x_2597_);
    v___f_2599_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2599_, 0, v___x_2597_);
    v___f_2600_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2600_, 0, v___x_2597_);
    v___f_2601_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2601_, 0, v___x_2597_);
    v___x_2602_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2602_, 0, lean_box(0));
    lean_closure_set(v___x_2602_, 1, lean_box(0));
    lean_closure_set(v___x_2602_, 2, v___x_2597_);
    v___x_2603_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2603_, 0, v___x_2602_);
    lean_ctor_set(v___x_2603_, 1, v___f_2598_);
    v___x_2604_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_2604_, 0, lean_box(0));
    lean_closure_set(v___x_2604_, 1, lean_box(0));
    lean_closure_set(v___x_2604_, 2, v___x_2597_);
    v___x_2605_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2605_, 0, v___x_2603_);
    lean_ctor_set(v___x_2605_, 1, v___x_2604_);
    lean_ctor_set(v___x_2605_, 2, v___f_2599_);
    lean_ctor_set(v___x_2605_, 3, v___f_2600_);
    lean_ctor_set(v___x_2605_, 4, v___f_2601_);
    v___x_2606_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2606_, 0, lean_box(0));
    lean_closure_set(v___x_2606_, 1, lean_box(0));
    lean_closure_set(v___x_2606_, 2, v___x_2597_);
    v___x_2607_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2607_, 0, v___x_2605_);
    lean_ctor_set(v___x_2607_, 1, v___x_2606_);
    v___x_2608_ = lean_box(0);
    v___x_2609_ = l_instInhabitedOfMonad___redArg(v___x_2607_, v___x_2608_);
    v___f_2610_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2610_, 0, v___x_2609_);
    v___x_692__overap_2611_ = lean_panic_fn_borrowed(v___f_2610_, v_msg_2585_);
    lean_dec_ref(v___f_2610_);
    v___x_2612_ = lean_box((v___y_2586_) as usize);
    v___x_2613_ = lean_apply_2(v___x_692__overap_2611_, v___x_2612_, v___y_2587_);
    return v___x_2613_;
}
pub unsafe fn l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___boxed(
    mut v_msg_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_825__boxed_2617_: u8 = 0;
    let mut v_res_2618_: *mut LeanObject = core::ptr::null_mut();
    v___y_825__boxed_2617_ = (lean_unbox(v___y_2615_) as u8);
    v_res_2618_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(
        v_msg_2614_,
        v___y_825__boxed_2617_,
        v___y_2616_,
    );
    return v_res_2618_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(
    mut v_keys_2619_: *mut LeanObject,
    mut v_i_2620_: *mut LeanObject,
    mut v_k_2621_: *mut LeanObject,
) -> u8 {
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: u8 = 0;
    let mut v_k_x27_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: u8 = 0;
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2622_ = lean_array_get_size(v_keys_2619_);
                v___x_2623_ = lean_nat_dec_lt(v_i_2620_, v___x_2622_);
                if v___x_2623_ == 0 {
                    lean_dec_ref(v_k_2621_);
                    lean_dec(v_i_2620_);
                    return v___x_2623_;
                } else {
                    v_k_x27_2624_ = lean_array_fget_borrowed(v_keys_2619_, v_i_2620_);
                    lean_inc(v_k_x27_2624_);
                    lean_inc_ref(v_k_2621_);
                    v___x_2625_ =
                        l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                            v_k_2621_,
                            v_k_x27_2624_,
                        );
                    if v___x_2625_ == 0 {
                        v___x_2626_ = lean_unsigned_to_nat(1);
                        v___x_2627_ = lean_nat_add(v_i_2620_, v___x_2626_);
                        lean_dec(v_i_2620_);
                        v_i_2620_ = v___x_2627_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_2621_);
                        lean_dec(v_i_2620_);
                        return v___x_2625_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_keys_2629_: *mut LeanObject,
    mut v_i_2630_: *mut LeanObject,
    mut v_k_2631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2632_: u8 = 0;
    let mut v_r_2633_: *mut LeanObject = core::ptr::null_mut();
    v_res_2632_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_2629_, v_i_2630_, v_k_2631_);
    lean_dec_ref(v_keys_2629_);
    v_r_2633_ = lean_box((v_res_2632_) as usize);
    return v_r_2633_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(
    mut v_x_2634_: *mut LeanObject,
    mut v_x_2635_: usize,
    mut v_x_2636_: *mut LeanObject,
) -> u8 {
    let mut v_es_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: usize = 0;
    let mut v___x_2640_: usize = 0;
    let mut v___x_2641_: usize = 0;
    let mut v_j_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: u8 = 0;
    let mut v_node_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: usize = 0;
    let mut v___x_2649_: u8 = 0;
    let mut v_ks_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2634_) == 0 {
                    v_es_2637_ = lean_ctor_get(v_x_2634_, 0);
                    lean_inc_ref(v_es_2637_);
                    lean_dec_ref_known(v_x_2634_, 1);
                    v___x_2638_ = lean_box(2);
                    v___x_2639_ = 5usize;
                    v___x_2640_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_Internal_Sym_share1_spec__1_spec__2___redArg___closed__1);
                    v___x_2641_ = lean_usize_land(v_x_2635_, v___x_2640_);
                    v_j_2642_ = lean_usize_to_nat(v___x_2641_);
                    v___x_2643_ = lean_array_get(v___x_2638_, v_es_2637_, v_j_2642_);
                    lean_dec(v_j_2642_);
                    lean_dec_ref(v_es_2637_);
                    match lean_obj_tag(v___x_2643_) {
                        0 => {
                            v_key_2644_ = lean_ctor_get(v___x_2643_, 0);
                            lean_inc(v_key_2644_);
                            lean_dec_ref_known(v___x_2643_, 2);
                            v___x_2645_ =
                                l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaEq(
                                    v_x_2636_,
                                    v_key_2644_,
                                );
                            return v___x_2645_;
                        }
                        1 => {
                            v_node_2646_ = lean_ctor_get(v___x_2643_, 0);
                            lean_inc(v_node_2646_);
                            lean_dec_ref_known(v___x_2643_, 1);
                            v___x_2647_ = lean_usize_shift_right(v_x_2635_, v___x_2639_);
                            v_x_2634_ = v_node_2646_;
                            v_x_2635_ = v___x_2647_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            lean_dec_ref(v_x_2636_);
                            v___x_2649_ = 0;
                            return v___x_2649_;
                        }
                    }
                } else {
                    v_ks_2650_ = lean_ctor_get(v_x_2634_, 0);
                    lean_inc_ref(v_ks_2650_);
                    lean_dec_ref_known(v_x_2634_, 2);
                    v___x_2651_ = lean_unsigned_to_nat(0);
                    v___x_2652_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_ks_2650_, v___x_2651_, v_x_2636_);
                    lean_dec_ref(v_ks_2650_);
                    return v___x_2652_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg___boxed(
    mut v_x_2653_: *mut LeanObject,
    mut v_x_2654_: *mut LeanObject,
    mut v_x_2655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_907__boxed_2656_: usize = 0;
    let mut v_res_2657_: u8 = 0;
    let mut v_r_2658_: *mut LeanObject = core::ptr::null_mut();
    v_x_907__boxed_2656_ = lean_unbox_usize(v_x_2654_);
    lean_dec(v_x_2654_);
    v_res_2657_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_2653_, v_x_907__boxed_2656_, v_x_2655_);
    v_r_2658_ = lean_box((v_res_2657_) as usize);
    return v_r_2658_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(
    mut v_x_2659_: *mut LeanObject,
    mut v_x_2660_: *mut LeanObject,
) -> u8 {
    let mut v___x_2661_: u64 = 0;
    let mut v___x_2662_: usize = 0;
    let mut v___x_2663_: u8 = 0;
    v___x_2661_ = l___private_Lean_Meta_Sym_AlphaShareCommon_0__Lean_Meta_Sym_alphaHash(v_x_2660_);
    v___x_2662_ = lean_uint64_to_usize(v___x_2661_);
    v___x_2663_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_2659_, v___x_2662_, v_x_2660_);
    return v___x_2663_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg___boxed(
    mut v_x_2664_: *mut LeanObject,
    mut v_x_2665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2666_: u8 = 0;
    let mut v_r_2667_: *mut LeanObject = core::ptr::null_mut();
    v_res_2666_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_2664_, v_x_2665_);
    v_r_2667_ = lean_box((v_res_2666_) as usize);
    return v_r_2667_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2() -> *mut LeanObject {
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    v___x_2670_ = l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__1;
    v___x_2671_ = lean_unsigned_to_nat(2);
    v___x_2672_ = lean_unsigned_to_nat(74);
    v___x_2673_ = l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__0;
    v___x_2674_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0;
    v___x_2675_ = l_mkPanicMessageWithDecl(
        v___x_2674_,
        v___x_2673_,
        v___x_2672_,
        v___x_2671_,
        v___x_2670_,
    );
    return v___x_2675_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Builder_assertShared(
    mut v_e_2676_: *mut LeanObject,
    mut v_a_2677_: u8,
    mut v_a_2678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2679_: u8 = 0;
    lean_inc_ref(v_a_2678_);
    v___x_2679_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_a_2678_, v_e_2676_);
    if v___x_2679_ == 0 {
        let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
        v___x_2680_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2_once),
            _init_l_Lean_Meta_Sym_Internal_Builder_assertShared___closed__2,
        );
        v___x_2681_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1(
            v___x_2680_,
            v_a_2677_,
            v_a_2678_,
        );
        return v___x_2681_;
    } else {
        let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
        v___x_2682_ = lean_box(0);
        v___x_2683_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2683_, 0, v___x_2682_);
        lean_ctor_set(v___x_2683_, 1, v_a_2678_);
        return v___x_2683_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_Builder_assertShared___boxed(
    mut v_e_2684_: *mut LeanObject,
    mut v_a_2685_: *mut LeanObject,
    mut v_a_2686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2687_: u8 = 0;
    let mut v_res_2688_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2687_ = (lean_unbox(v_a_2685_) as u8);
    v_res_2688_ =
        l_Lean_Meta_Sym_Internal_Builder_assertShared(v_e_2684_, v_a_boxed_2687_, v_a_2686_);
    return v_res_2688_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(
    mut v_00_u03b2_2689_: *mut LeanObject,
    mut v_x_2690_: *mut LeanObject,
    mut v_x_2691_: *mut LeanObject,
) -> u8 {
    let mut v___x_2692_: u8 = 0;
    v___x_2692_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___redArg(v_x_2690_, v_x_2691_);
    return v___x_2692_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0___boxed(
    mut v_00_u03b2_2693_: *mut LeanObject,
    mut v_x_2694_: *mut LeanObject,
    mut v_x_2695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2696_: u8 = 0;
    let mut v_r_2697_: *mut LeanObject = core::ptr::null_mut();
    v_res_2696_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0(v_00_u03b2_2693_, v_x_2694_, v_x_2695_);
    v_r_2697_ = lean_box((v_res_2696_) as usize);
    return v_r_2697_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(
    mut v_00_u03b2_2698_: *mut LeanObject,
    mut v_x_2699_: *mut LeanObject,
    mut v_x_2700_: usize,
    mut v_x_2701_: *mut LeanObject,
) -> u8 {
    let mut v___x_2702_: u8 = 0;
    v___x_2702_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___redArg(v_x_2699_, v_x_2700_, v_x_2701_);
    return v___x_2702_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0___boxed(
    mut v_00_u03b2_2703_: *mut LeanObject,
    mut v_x_2704_: *mut LeanObject,
    mut v_x_2705_: *mut LeanObject,
    mut v_x_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1008__boxed_2707_: usize = 0;
    let mut v_res_2708_: u8 = 0;
    let mut v_r_2709_: *mut LeanObject = core::ptr::null_mut();
    v_x_1008__boxed_2707_ = lean_unbox_usize(v_x_2705_);
    lean_dec(v_x_2705_);
    v_res_2708_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0(v_00_u03b2_2703_, v_x_2704_, v_x_1008__boxed_2707_, v_x_2706_);
    v_r_2709_ = lean_box((v_res_2708_) as usize);
    return v_r_2709_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(
    mut v_00_u03b2_2710_: *mut LeanObject,
    mut v_keys_2711_: *mut LeanObject,
    mut v_vals_2712_: *mut LeanObject,
    mut v_heq_2713_: *mut LeanObject,
    mut v_i_2714_: *mut LeanObject,
    mut v_k_2715_: *mut LeanObject,
) -> u8 {
    let mut v___x_2716_: u8 = 0;
    v___x_2716_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___redArg(v_keys_2711_, v_i_2714_, v_k_2715_);
    return v___x_2716_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_2717_: *mut LeanObject,
    mut v_keys_2718_: *mut LeanObject,
    mut v_vals_2719_: *mut LeanObject,
    mut v_heq_2720_: *mut LeanObject,
    mut v_i_2721_: *mut LeanObject,
    mut v_k_2722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2723_: u8 = 0;
    let mut v_r_2724_: *mut LeanObject = core::ptr::null_mut();
    v_res_2723_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__0_spec__0_spec__2(v_00_u03b2_2717_, v_keys_2718_, v_vals_2719_, v_heq_2720_, v_i_2721_, v_k_2722_);
    lean_dec_ref(v_vals_2719_);
    lean_dec_ref(v_keys_2718_);
    v_r_2724_ = lean_box((v_res_2723_) as usize);
    return v_r_2724_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM()
-> *mut LeanObject {
    let mut v___f_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    v___f_2727_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__0;
    v___f_2728_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__1;
    v___f_2729_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__2;
    v___f_2730_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__3;
    v___f_2731_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__4;
    v___f_2732_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__5;
    v___f_2733_ = l_panic___at___00Lean_Meta_Sym_Internal_Builder_assertShared_spec__1___closed__6;
    v___x_2734_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2734_, 0, v___f_2727_);
    lean_ctor_set(v___x_2734_, 1, v___f_2728_);
    v___x_2735_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2735_, 0, v___x_2734_);
    lean_ctor_set(v___x_2735_, 1, v___f_2729_);
    lean_ctor_set(v___x_2735_, 2, v___f_2730_);
    lean_ctor_set(v___x_2735_, 3, v___f_2731_);
    lean_ctor_set(v___x_2735_, 4, v___f_2732_);
    v___x_2736_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2736_, 0, v___x_2735_);
    lean_ctor_set(v___x_2736_, 1, v___f_2733_);
    lean_inc_ref_n(v___x_2736_, 6);
    v___f_2737_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2737_, 0, v___x_2736_);
    v___f_2738_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2738_, 0, v___x_2736_);
    v___f_2739_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2739_, 0, v___x_2736_);
    v___f_2740_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2740_, 0, v___x_2736_);
    v___x_2741_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2741_, 0, lean_box(0));
    lean_closure_set(v___x_2741_, 1, lean_box(0));
    lean_closure_set(v___x_2741_, 2, v___x_2736_);
    v___x_2742_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2742_, 0, v___x_2741_);
    lean_ctor_set(v___x_2742_, 1, v___f_2737_);
    v___x_2743_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_2743_, 0, lean_box(0));
    lean_closure_set(v___x_2743_, 1, lean_box(0));
    lean_closure_set(v___x_2743_, 2, v___x_2736_);
    v___x_2744_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_2744_, 0, v___x_2742_);
    lean_ctor_set(v___x_2744_, 1, v___x_2743_);
    lean_ctor_set(v___x_2744_, 2, v___f_2738_);
    lean_ctor_set(v___x_2744_, 3, v___f_2739_);
    lean_ctor_set(v___x_2744_, 4, v___f_2740_);
    v___x_2745_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_2745_, 0, lean_box(0));
    lean_closure_set(v___x_2745_, 1, lean_box(0));
    lean_closure_set(v___x_2745_, 2, v___x_2736_);
    v___x_2746_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2746_, 0, v___x_2744_);
    lean_ctor_set(v___x_2746_, 1, v___x_2745_);
    v___x_2747_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__0;
    v___x_2748_ = l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM___closed__1;
    v___x_2749_ = lean_alloc_closure(l_ReaderT_read___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_2749_, 0, lean_box(0));
    lean_closure_set(v___x_2749_, 1, lean_box(0));
    lean_closure_set(v___x_2749_, 2, v___x_2746_);
    v___x_2750_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2750_, 0, v___x_2747_);
    lean_ctor_set(v___x_2750_, 1, v___x_2748_);
    lean_ctor_set(v___x_2750_, 2, v___x_2749_);
    return v___x_2750_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLitS___redArg(
    mut v_inst_2751_: *mut LeanObject,
    mut v_l_2752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_share1_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    v_share1_2753_ = lean_ctor_get(v_inst_2751_, 0);
    lean_inc(v_share1_2753_);
    lean_dec_ref(v_inst_2751_);
    v___x_2754_ = l_Lean_Expr_lit___override(v_l_2752_);
    v___x_2755_ = lean_apply_1(v_share1_2753_, v___x_2754_);
    return v___x_2755_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLitS(
    mut v_m_2756_: *mut LeanObject,
    mut v_inst_2757_: *mut LeanObject,
    mut v_l_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    v___x_2759_ = l_Lean_Meta_Sym_Internal_mkLitS___redArg(v_inst_2757_, v_l_2758_);
    return v___x_2759_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkConstS___redArg(
    mut v_inst_2760_: *mut LeanObject,
    mut v_declName_2761_: *mut LeanObject,
    mut v_us_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_share1_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    v_share1_2763_ = lean_ctor_get(v_inst_2760_, 0);
    lean_inc(v_share1_2763_);
    lean_dec_ref(v_inst_2760_);
    v___x_2764_ = l_Lean_Expr_const___override(v_declName_2761_, v_us_2762_);
    v___x_2765_ = lean_apply_1(v_share1_2763_, v___x_2764_);
    return v___x_2765_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkConstS(
    mut v_m_2766_: *mut LeanObject,
    mut v_inst_2767_: *mut LeanObject,
    mut v_declName_2768_: *mut LeanObject,
    mut v_us_2769_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    v___x_2770_ =
        l_Lean_Meta_Sym_Internal_mkConstS___redArg(v_inst_2767_, v_declName_2768_, v_us_2769_);
    return v___x_2770_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS___redArg(
    mut v_inst_2771_: *mut LeanObject,
    mut v_idx_2772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_share1_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    v_share1_2773_ = lean_ctor_get(v_inst_2771_, 0);
    lean_inc(v_share1_2773_);
    lean_dec_ref(v_inst_2771_);
    v___x_2774_ = l_Lean_Expr_bvar___override(v_idx_2772_);
    v___x_2775_ = lean_apply_1(v_share1_2773_, v___x_2774_);
    return v___x_2775_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkBVarS(
    mut v_m_2776_: *mut LeanObject,
    mut v_inst_2777_: *mut LeanObject,
    mut v_idx_2778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    v___x_2779_ = l_Lean_Meta_Sym_Internal_mkBVarS___redArg(v_inst_2777_, v_idx_2778_);
    return v___x_2779_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkSortS___redArg(
    mut v_inst_2780_: *mut LeanObject,
    mut v_u_2781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_share1_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    v_share1_2782_ = lean_ctor_get(v_inst_2780_, 0);
    lean_inc(v_share1_2782_);
    lean_dec_ref(v_inst_2780_);
    v___x_2783_ = l_Lean_Expr_sort___override(v_u_2781_);
    v___x_2784_ = lean_apply_1(v_share1_2782_, v___x_2783_);
    return v___x_2784_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkSortS(
    mut v_m_2785_: *mut LeanObject,
    mut v_inst_2786_: *mut LeanObject,
    mut v_u_2787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2788_: *mut LeanObject = core::ptr::null_mut();
    v___x_2788_ = l_Lean_Meta_Sym_Internal_mkSortS___redArg(v_inst_2786_, v_u_2787_);
    return v___x_2788_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkFVarS___redArg(
    mut v_inst_2789_: *mut LeanObject,
    mut v_fvarId_2790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_share1_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    v_share1_2791_ = lean_ctor_get(v_inst_2789_, 0);
    lean_inc(v_share1_2791_);
    lean_dec_ref(v_inst_2789_);
    v___x_2792_ = l_Lean_Expr_fvar___override(v_fvarId_2790_);
    v___x_2793_ = lean_apply_1(v_share1_2791_, v___x_2792_);
    return v___x_2793_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkFVarS(
    mut v_m_2794_: *mut LeanObject,
    mut v_inst_2795_: *mut LeanObject,
    mut v_fvarId_2796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    v___x_2797_ = l_Lean_Meta_Sym_Internal_mkFVarS___redArg(v_inst_2795_, v_fvarId_2796_);
    return v___x_2797_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMVarS___redArg(
    mut v_inst_2798_: *mut LeanObject,
    mut v_mvarId_2799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_share1_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    v_share1_2800_ = lean_ctor_get(v_inst_2798_, 0);
    lean_inc(v_share1_2800_);
    lean_dec_ref(v_inst_2798_);
    v___x_2801_ = l_Lean_Expr_mvar___override(v_mvarId_2799_);
    v___x_2802_ = lean_apply_1(v_share1_2800_, v___x_2801_);
    return v___x_2802_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMVarS(
    mut v_m_2803_: *mut LeanObject,
    mut v_inst_2804_: *mut LeanObject,
    mut v_mvarId_2805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    v___x_2806_ = l_Lean_Meta_Sym_Internal_mkMVarS___redArg(v_inst_2804_, v_mvarId_2805_);
    return v___x_2806_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0(
    mut v_d_2807_: *mut LeanObject,
    mut v_e_2808_: *mut LeanObject,
    mut v_share1_2809_: *mut LeanObject,
    mut v_____r_2810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    v___x_2811_ = l_Lean_Expr_mdata___override(v_d_2807_, v_e_2808_);
    v___x_2812_ = lean_apply_1(v_share1_2809_, v___x_2811_);
    return v___x_2812_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1(
    mut v___f_2813_: *mut LeanObject,
    mut v_____r_2814_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    v___x_2815_ = lean_apply_1(v___f_2813_, v_____r_2814_);
    return v___x_2815_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(
    mut v___f_2816_: *mut LeanObject,
    mut v_assertShared_2817_: *mut LeanObject,
    mut v_e_2818_: *mut LeanObject,
    mut v_toBind_2819_: *mut LeanObject,
    mut v___f_2820_: *mut LeanObject,
    mut v_____do__lift_2821_: u8,
) -> *mut LeanObject {
    if v_____do__lift_2821_ == 0 {
        let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2820_);
        lean_dec(v_toBind_2819_);
        lean_dec_ref(v_e_2818_);
        lean_dec(v_assertShared_2817_);
        v___x_2822_ = lean_box(0);
        v___x_2823_ = lean_apply_1(v___f_2816_, v___x_2822_);
        return v___x_2823_;
    } else {
        let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2816_);
        v___x_2824_ = lean_apply_1(v_assertShared_2817_, v_e_2818_);
        v___x_2825_ = lean_apply_4(
            v_toBind_2819_,
            lean_box(0),
            lean_box(0),
            v___x_2824_,
            v___f_2820_,
        );
        return v___x_2825_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed(
    mut v___f_2826_: *mut LeanObject,
    mut v_assertShared_2827_: *mut LeanObject,
    mut v_e_2828_: *mut LeanObject,
    mut v_toBind_2829_: *mut LeanObject,
    mut v___f_2830_: *mut LeanObject,
    mut v_____do__lift_2831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_86__boxed_2832_: u8 = 0;
    let mut v_res_2833_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_86__boxed_2832_ = (lean_unbox(v_____do__lift_2831_) as u8);
    v_res_2833_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2(
        v___f_2826_,
        v_assertShared_2827_,
        v_e_2828_,
        v_toBind_2829_,
        v___f_2830_,
        v_____do__lift_86__boxed_2832_,
    );
    return v_res_2833_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS___redArg(
    mut v_inst_2834_: *mut LeanObject,
    mut v_inst_2835_: *mut LeanObject,
    mut v_d_2836_: *mut LeanObject,
    mut v_e_2837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share1_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2838_ = lean_ctor_get(v_inst_2835_, 1);
    lean_inc_n(v_toBind_2838_, 2);
    lean_dec_ref(v_inst_2835_);
    v_share1_2839_ = lean_ctor_get(v_inst_2834_, 0);
    lean_inc(v_share1_2839_);
    v_assertShared_2840_ = lean_ctor_get(v_inst_2834_, 1);
    lean_inc(v_assertShared_2840_);
    v_isDebugEnabled_2841_ = lean_ctor_get(v_inst_2834_, 2);
    lean_inc(v_isDebugEnabled_2841_);
    lean_dec_ref(v_inst_2834_);
    lean_inc_ref(v_e_2837_);
    v___f_2842_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2842_, 0, v_d_2836_);
    lean_closure_set(v___f_2842_, 1, v_e_2837_);
    lean_closure_set(v___f_2842_, 2, v_share1_2839_);
    lean_inc_ref(v___f_2842_);
    v___f_2843_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2843_, 0, v___f_2842_);
    v___f_2844_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2844_, 0, v___f_2842_);
    lean_closure_set(v___f_2844_, 1, v_assertShared_2840_);
    lean_closure_set(v___f_2844_, 2, v_e_2837_);
    lean_closure_set(v___f_2844_, 3, v_toBind_2838_);
    lean_closure_set(v___f_2844_, 4, v___f_2843_);
    v___x_2845_ = lean_apply_4(
        v_toBind_2838_,
        lean_box(0),
        lean_box(0),
        v_isDebugEnabled_2841_,
        v___f_2844_,
    );
    return v___x_2845_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkMDataS(
    mut v_m_2846_: *mut LeanObject,
    mut v_inst_2847_: *mut LeanObject,
    mut v_inst_2848_: *mut LeanObject,
    mut v_d_2849_: *mut LeanObject,
    mut v_e_2850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    v___x_2851_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(
        v_inst_2847_,
        v_inst_2848_,
        v_d_2849_,
        v_e_2850_,
    );
    return v___x_2851_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0(
    mut v_structName_2852_: *mut LeanObject,
    mut v_idx_2853_: *mut LeanObject,
    mut v_struct_2854_: *mut LeanObject,
    mut v_share1_2855_: *mut LeanObject,
    mut v_____r_2856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    v___x_2857_ = l_Lean_Expr_proj___override(v_structName_2852_, v_idx_2853_, v_struct_2854_);
    v___x_2858_ = lean_apply_1(v_share1_2855_, v___x_2857_);
    return v___x_2858_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(
    mut v___f_2859_: *mut LeanObject,
    mut v_assertShared_2860_: *mut LeanObject,
    mut v_struct_2861_: *mut LeanObject,
    mut v_toBind_2862_: *mut LeanObject,
    mut v___f_2863_: *mut LeanObject,
    mut v_____do__lift_2864_: u8,
) -> *mut LeanObject {
    if v_____do__lift_2864_ == 0 {
        let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2863_);
        lean_dec(v_toBind_2862_);
        lean_dec_ref(v_struct_2861_);
        lean_dec(v_assertShared_2860_);
        v___x_2865_ = lean_box(0);
        v___x_2866_ = lean_apply_1(v___f_2859_, v___x_2865_);
        return v___x_2866_;
    } else {
        let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2859_);
        v___x_2867_ = lean_apply_1(v_assertShared_2860_, v_struct_2861_);
        v___x_2868_ = lean_apply_4(
            v_toBind_2862_,
            lean_box(0),
            lean_box(0),
            v___x_2867_,
            v___f_2863_,
        );
        return v___x_2868_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed(
    mut v___f_2869_: *mut LeanObject,
    mut v_assertShared_2870_: *mut LeanObject,
    mut v_struct_2871_: *mut LeanObject,
    mut v_toBind_2872_: *mut LeanObject,
    mut v___f_2873_: *mut LeanObject,
    mut v_____do__lift_2874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_80__boxed_2875_: u8 = 0;
    let mut v_res_2876_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_80__boxed_2875_ = (lean_unbox(v_____do__lift_2874_) as u8);
    v_res_2876_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2(
        v___f_2869_,
        v_assertShared_2870_,
        v_struct_2871_,
        v_toBind_2872_,
        v___f_2873_,
        v_____do__lift_80__boxed_2875_,
    );
    return v_res_2876_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS___redArg(
    mut v_inst_2877_: *mut LeanObject,
    mut v_inst_2878_: *mut LeanObject,
    mut v_structName_2879_: *mut LeanObject,
    mut v_idx_2880_: *mut LeanObject,
    mut v_struct_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share1_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2882_ = lean_ctor_get(v_inst_2878_, 1);
    lean_inc_n(v_toBind_2882_, 2);
    lean_dec_ref(v_inst_2878_);
    v_share1_2883_ = lean_ctor_get(v_inst_2877_, 0);
    lean_inc(v_share1_2883_);
    v_assertShared_2884_ = lean_ctor_get(v_inst_2877_, 1);
    lean_inc(v_assertShared_2884_);
    v_isDebugEnabled_2885_ = lean_ctor_get(v_inst_2877_, 2);
    lean_inc(v_isDebugEnabled_2885_);
    lean_dec_ref(v_inst_2877_);
    lean_inc_ref(v_struct_2881_);
    v___f_2886_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2886_, 0, v_structName_2879_);
    lean_closure_set(v___f_2886_, 1, v_idx_2880_);
    lean_closure_set(v___f_2886_, 2, v_struct_2881_);
    lean_closure_set(v___f_2886_, 3, v_share1_2883_);
    lean_inc_ref(v___f_2886_);
    v___f_2887_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2887_, 0, v___f_2886_);
    v___f_2888_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkProjS___redArg___lam__2___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2888_, 0, v___f_2886_);
    lean_closure_set(v___f_2888_, 1, v_assertShared_2884_);
    lean_closure_set(v___f_2888_, 2, v_struct_2881_);
    lean_closure_set(v___f_2888_, 3, v_toBind_2882_);
    lean_closure_set(v___f_2888_, 4, v___f_2887_);
    v___x_2889_ = lean_apply_4(
        v_toBind_2882_,
        lean_box(0),
        lean_box(0),
        v_isDebugEnabled_2885_,
        v___f_2888_,
    );
    return v___x_2889_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkProjS(
    mut v_m_2890_: *mut LeanObject,
    mut v_inst_2891_: *mut LeanObject,
    mut v_inst_2892_: *mut LeanObject,
    mut v_structName_2893_: *mut LeanObject,
    mut v_idx_2894_: *mut LeanObject,
    mut v_struct_2895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    v___x_2896_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(
        v_inst_2891_,
        v_inst_2892_,
        v_structName_2893_,
        v_idx_2894_,
        v_struct_2895_,
    );
    return v___x_2896_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0(
    mut v_f_2897_: *mut LeanObject,
    mut v_a_2898_: *mut LeanObject,
    mut v_share1_2899_: *mut LeanObject,
    mut v_____r_2900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    v___x_2901_ = l_Lean_Expr_app___override(v_f_2897_, v_a_2898_);
    v___x_2902_ = lean_apply_1(v_share1_2899_, v___x_2901_);
    return v___x_2902_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2(
    mut v_assertShared_2903_: *mut LeanObject,
    mut v_a_2904_: *mut LeanObject,
    mut v_toBind_2905_: *mut LeanObject,
    mut v___f_2906_: *mut LeanObject,
    mut v_____r_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    v___x_2908_ = lean_apply_1(v_assertShared_2903_, v_a_2904_);
    v___x_2909_ = lean_apply_4(
        v_toBind_2905_,
        lean_box(0),
        lean_box(0),
        v___x_2908_,
        v___f_2906_,
    );
    return v___x_2909_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(
    mut v___f_2910_: *mut LeanObject,
    mut v_assertShared_2911_: *mut LeanObject,
    mut v_a_2912_: *mut LeanObject,
    mut v_toBind_2913_: *mut LeanObject,
    mut v___f_2914_: *mut LeanObject,
    mut v_f_2915_: *mut LeanObject,
    mut v_____do__lift_2916_: u8,
) -> *mut LeanObject {
    if v_____do__lift_2916_ == 0 {
        let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_f_2915_);
        lean_dec(v___f_2914_);
        lean_dec(v_toBind_2913_);
        lean_dec_ref(v_a_2912_);
        lean_dec(v_assertShared_2911_);
        v___x_2917_ = lean_box(0);
        v___x_2918_ = lean_apply_1(v___f_2910_, v___x_2917_);
        return v___x_2918_;
    } else {
        let mut v___f_2919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2910_);
        lean_inc(v_toBind_2913_);
        lean_inc(v_assertShared_2911_);
        v___f_2919_ = lean_alloc_closure(
            l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__2 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_2919_, 0, v_assertShared_2911_);
        lean_closure_set(v___f_2919_, 1, v_a_2912_);
        lean_closure_set(v___f_2919_, 2, v_toBind_2913_);
        lean_closure_set(v___f_2919_, 3, v___f_2914_);
        v___x_2920_ = lean_apply_1(v_assertShared_2911_, v_f_2915_);
        v___x_2921_ = lean_apply_4(
            v_toBind_2913_,
            lean_box(0),
            lean_box(0),
            v___x_2920_,
            v___f_2919_,
        );
        return v___x_2921_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed(
    mut v___f_2922_: *mut LeanObject,
    mut v_assertShared_2923_: *mut LeanObject,
    mut v_a_2924_: *mut LeanObject,
    mut v_toBind_2925_: *mut LeanObject,
    mut v___f_2926_: *mut LeanObject,
    mut v_f_2927_: *mut LeanObject,
    mut v_____do__lift_2928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_105__boxed_2929_: u8 = 0;
    let mut v_res_2930_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_105__boxed_2929_ = (lean_unbox(v_____do__lift_2928_) as u8);
    v_res_2930_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1(
        v___f_2922_,
        v_assertShared_2923_,
        v_a_2924_,
        v_toBind_2925_,
        v___f_2926_,
        v_f_2927_,
        v_____do__lift_105__boxed_2929_,
    );
    return v_res_2930_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___redArg(
    mut v_inst_2931_: *mut LeanObject,
    mut v_inst_2932_: *mut LeanObject,
    mut v_f_2933_: *mut LeanObject,
    mut v_a_2934_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share1_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2935_ = lean_ctor_get(v_inst_2932_, 1);
    lean_inc_n(v_toBind_2935_, 2);
    lean_dec_ref(v_inst_2932_);
    v_share1_2936_ = lean_ctor_get(v_inst_2931_, 0);
    lean_inc(v_share1_2936_);
    v_assertShared_2937_ = lean_ctor_get(v_inst_2931_, 1);
    lean_inc(v_assertShared_2937_);
    v_isDebugEnabled_2938_ = lean_ctor_get(v_inst_2931_, 2);
    lean_inc(v_isDebugEnabled_2938_);
    lean_dec_ref(v_inst_2931_);
    lean_inc_ref(v_a_2934_);
    lean_inc_ref(v_f_2933_);
    v___f_2939_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2939_, 0, v_f_2933_);
    lean_closure_set(v___f_2939_, 1, v_a_2934_);
    lean_closure_set(v___f_2939_, 2, v_share1_2936_);
    lean_inc_ref(v___f_2939_);
    v___f_2940_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2940_, 0, v___f_2939_);
    v___f_2941_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS___redArg___lam__1___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2941_, 0, v___f_2939_);
    lean_closure_set(v___f_2941_, 1, v_assertShared_2937_);
    lean_closure_set(v___f_2941_, 2, v_a_2934_);
    lean_closure_set(v___f_2941_, 3, v_toBind_2935_);
    lean_closure_set(v___f_2941_, 4, v___f_2940_);
    lean_closure_set(v___f_2941_, 5, v_f_2933_);
    v___x_2942_ = lean_apply_4(
        v_toBind_2935_,
        lean_box(0),
        lean_box(0),
        v_isDebugEnabled_2938_,
        v___f_2941_,
    );
    return v___x_2942_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS(
    mut v_m_2943_: *mut LeanObject,
    mut v_inst_2944_: *mut LeanObject,
    mut v_inst_2945_: *mut LeanObject,
    mut v_f_2946_: *mut LeanObject,
    mut v_a_2947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    v___x_2948_ =
        l_Lean_Meta_Sym_Internal_mkAppS___redArg(v_inst_2944_, v_inst_2945_, v_f_2946_, v_a_2947_);
    return v___x_2948_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(
    mut v_x_2949_: *mut LeanObject,
    mut v_t_2950_: *mut LeanObject,
    mut v_b_2951_: *mut LeanObject,
    mut v_bi_2952_: u8,
    mut v_share1_2953_: *mut LeanObject,
    mut v_____r_2954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    v___x_2955_ = l_Lean_Expr_lam___override(v_x_2949_, v_t_2950_, v_b_2951_, v_bi_2952_);
    v___x_2956_ = lean_apply_1(v_share1_2953_, v___x_2955_);
    return v___x_2956_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed(
    mut v_x_2957_: *mut LeanObject,
    mut v_t_2958_: *mut LeanObject,
    mut v_b_2959_: *mut LeanObject,
    mut v_bi_2960_: *mut LeanObject,
    mut v_share1_2961_: *mut LeanObject,
    mut v_____r_2962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_2963_: u8 = 0;
    let mut v_res_2964_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_2963_ = (lean_unbox(v_bi_2960_) as u8);
    v_res_2964_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0(
        v_x_2957_,
        v_t_2958_,
        v_b_2959_,
        v_bi_boxed_2963_,
        v_share1_2961_,
        v_____r_2962_,
    );
    return v_res_2964_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2(
    mut v_assertShared_2965_: *mut LeanObject,
    mut v_b_2966_: *mut LeanObject,
    mut v_toBind_2967_: *mut LeanObject,
    mut v___f_2968_: *mut LeanObject,
    mut v_____r_2969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut LeanObject = core::ptr::null_mut();
    v___x_2970_ = lean_apply_1(v_assertShared_2965_, v_b_2966_);
    v___x_2971_ = lean_apply_4(
        v_toBind_2967_,
        lean_box(0),
        lean_box(0),
        v___x_2970_,
        v___f_2968_,
    );
    return v___x_2971_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(
    mut v___f_2972_: *mut LeanObject,
    mut v_assertShared_2973_: *mut LeanObject,
    mut v_b_2974_: *mut LeanObject,
    mut v_toBind_2975_: *mut LeanObject,
    mut v___f_2976_: *mut LeanObject,
    mut v_t_2977_: *mut LeanObject,
    mut v_____do__lift_2978_: u8,
) -> *mut LeanObject {
    if v_____do__lift_2978_ == 0 {
        let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_t_2977_);
        lean_dec(v___f_2976_);
        lean_dec(v_toBind_2975_);
        lean_dec_ref(v_b_2974_);
        lean_dec(v_assertShared_2973_);
        v___x_2979_ = lean_box(0);
        v___x_2980_ = lean_apply_1(v___f_2972_, v___x_2979_);
        return v___x_2980_;
    } else {
        let mut v___f_2981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2972_);
        lean_inc(v_toBind_2975_);
        lean_inc(v_assertShared_2973_);
        v___f_2981_ = lean_alloc_closure(
            l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_2981_, 0, v_assertShared_2973_);
        lean_closure_set(v___f_2981_, 1, v_b_2974_);
        lean_closure_set(v___f_2981_, 2, v_toBind_2975_);
        lean_closure_set(v___f_2981_, 3, v___f_2976_);
        v___x_2982_ = lean_apply_1(v_assertShared_2973_, v_t_2977_);
        v___x_2983_ = lean_apply_4(
            v_toBind_2975_,
            lean_box(0),
            lean_box(0),
            v___x_2982_,
            v___f_2981_,
        );
        return v___x_2983_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed(
    mut v___f_2984_: *mut LeanObject,
    mut v_assertShared_2985_: *mut LeanObject,
    mut v_b_2986_: *mut LeanObject,
    mut v_toBind_2987_: *mut LeanObject,
    mut v___f_2988_: *mut LeanObject,
    mut v_t_2989_: *mut LeanObject,
    mut v_____do__lift_2990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_106__boxed_2991_: u8 = 0;
    let mut v_res_2992_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_106__boxed_2991_ = (lean_unbox(v_____do__lift_2990_) as u8);
    v_res_2992_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1(
        v___f_2984_,
        v_assertShared_2985_,
        v_b_2986_,
        v_toBind_2987_,
        v___f_2988_,
        v_t_2989_,
        v_____do__lift_106__boxed_2991_,
    );
    return v_res_2992_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(
    mut v_inst_2993_: *mut LeanObject,
    mut v_inst_2994_: *mut LeanObject,
    mut v_x_2995_: *mut LeanObject,
    mut v_bi_2996_: u8,
    mut v_t_2997_: *mut LeanObject,
    mut v_b_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share1_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2999_ = lean_ctor_get(v_inst_2994_, 1);
    lean_inc_n(v_toBind_2999_, 2);
    lean_dec_ref(v_inst_2994_);
    v_share1_3000_ = lean_ctor_get(v_inst_2993_, 0);
    lean_inc(v_share1_3000_);
    v_assertShared_3001_ = lean_ctor_get(v_inst_2993_, 1);
    lean_inc(v_assertShared_3001_);
    v_isDebugEnabled_3002_ = lean_ctor_get(v_inst_2993_, 2);
    lean_inc(v_isDebugEnabled_3002_);
    lean_dec_ref(v_inst_2993_);
    v___x_3003_ = lean_box((v_bi_2996_) as usize);
    lean_inc_ref(v_b_2998_);
    lean_inc_ref(v_t_2997_);
    v___f_3004_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_3004_, 0, v_x_2995_);
    lean_closure_set(v___f_3004_, 1, v_t_2997_);
    lean_closure_set(v___f_3004_, 2, v_b_2998_);
    lean_closure_set(v___f_3004_, 3, v___x_3003_);
    lean_closure_set(v___f_3004_, 4, v_share1_3000_);
    lean_inc_ref(v___f_3004_);
    v___f_3005_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3005_, 0, v___f_3004_);
    v___f_3006_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_3006_, 0, v___f_3004_);
    lean_closure_set(v___f_3006_, 1, v_assertShared_3001_);
    lean_closure_set(v___f_3006_, 2, v_b_2998_);
    lean_closure_set(v___f_3006_, 3, v_toBind_2999_);
    lean_closure_set(v___f_3006_, 4, v___f_3005_);
    lean_closure_set(v___f_3006_, 5, v_t_2997_);
    v___x_3007_ = lean_apply_4(
        v_toBind_2999_,
        lean_box(0),
        lean_box(0),
        v_isDebugEnabled_3002_,
        v___f_3006_,
    );
    return v___x_3007_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___boxed(
    mut v_inst_3008_: *mut LeanObject,
    mut v_inst_3009_: *mut LeanObject,
    mut v_x_3010_: *mut LeanObject,
    mut v_bi_3011_: *mut LeanObject,
    mut v_t_3012_: *mut LeanObject,
    mut v_b_3013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3014_: u8 = 0;
    let mut v_res_3015_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3014_ = (lean_unbox(v_bi_3011_) as u8);
    v_res_3015_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(
        v_inst_3008_,
        v_inst_3009_,
        v_x_3010_,
        v_bi_boxed_3014_,
        v_t_3012_,
        v_b_3013_,
    );
    return v_res_3015_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS(
    mut v_m_3016_: *mut LeanObject,
    mut v_inst_3017_: *mut LeanObject,
    mut v_inst_3018_: *mut LeanObject,
    mut v_x_3019_: *mut LeanObject,
    mut v_bi_3020_: u8,
    mut v_t_3021_: *mut LeanObject,
    mut v_b_3022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    v___x_3023_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(
        v_inst_3017_,
        v_inst_3018_,
        v_x_3019_,
        v_bi_3020_,
        v_t_3021_,
        v_b_3022_,
    );
    return v___x_3023_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLambdaS___boxed(
    mut v_m_3024_: *mut LeanObject,
    mut v_inst_3025_: *mut LeanObject,
    mut v_inst_3026_: *mut LeanObject,
    mut v_x_3027_: *mut LeanObject,
    mut v_bi_3028_: *mut LeanObject,
    mut v_t_3029_: *mut LeanObject,
    mut v_b_3030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3031_: u8 = 0;
    let mut v_res_3032_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3031_ = (lean_unbox(v_bi_3028_) as u8);
    v_res_3032_ = l_Lean_Meta_Sym_Internal_mkLambdaS(
        v_m_3024_,
        v_inst_3025_,
        v_inst_3026_,
        v_x_3027_,
        v_bi_boxed_3031_,
        v_t_3029_,
        v_b_3030_,
    );
    return v_res_3032_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(
    mut v_x_3033_: *mut LeanObject,
    mut v_t_3034_: *mut LeanObject,
    mut v_b_3035_: *mut LeanObject,
    mut v_bi_3036_: u8,
    mut v_share1_3037_: *mut LeanObject,
    mut v_____r_3038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    v___x_3039_ = l_Lean_Expr_forallE___override(v_x_3033_, v_t_3034_, v_b_3035_, v_bi_3036_);
    v___x_3040_ = lean_apply_1(v_share1_3037_, v___x_3039_);
    return v___x_3040_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed(
    mut v_x_3041_: *mut LeanObject,
    mut v_t_3042_: *mut LeanObject,
    mut v_b_3043_: *mut LeanObject,
    mut v_bi_3044_: *mut LeanObject,
    mut v_share1_3045_: *mut LeanObject,
    mut v_____r_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3047_: u8 = 0;
    let mut v_res_3048_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3047_ = (lean_unbox(v_bi_3044_) as u8);
    v_res_3048_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0(
        v_x_3041_,
        v_t_3042_,
        v_b_3043_,
        v_bi_boxed_3047_,
        v_share1_3045_,
        v_____r_3046_,
    );
    return v_res_3048_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___redArg(
    mut v_inst_3049_: *mut LeanObject,
    mut v_inst_3050_: *mut LeanObject,
    mut v_x_3051_: *mut LeanObject,
    mut v_bi_3052_: u8,
    mut v_t_3053_: *mut LeanObject,
    mut v_b_3054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share1_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3055_ = lean_ctor_get(v_inst_3050_, 1);
    lean_inc_n(v_toBind_3055_, 2);
    lean_dec_ref(v_inst_3050_);
    v_share1_3056_ = lean_ctor_get(v_inst_3049_, 0);
    lean_inc(v_share1_3056_);
    v_assertShared_3057_ = lean_ctor_get(v_inst_3049_, 1);
    lean_inc(v_assertShared_3057_);
    v_isDebugEnabled_3058_ = lean_ctor_get(v_inst_3049_, 2);
    lean_inc(v_isDebugEnabled_3058_);
    lean_dec_ref(v_inst_3049_);
    v___x_3059_ = lean_box((v_bi_3052_) as usize);
    lean_inc_ref(v_b_3054_);
    lean_inc_ref(v_t_3053_);
    v___f_3060_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkForallS___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_3060_, 0, v_x_3051_);
    lean_closure_set(v___f_3060_, 1, v_t_3053_);
    lean_closure_set(v___f_3060_, 2, v_b_3054_);
    lean_closure_set(v___f_3060_, 3, v___x_3059_);
    lean_closure_set(v___f_3060_, 4, v_share1_3056_);
    lean_inc_ref(v___f_3060_);
    v___f_3061_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3061_, 0, v___f_3060_);
    v___f_3062_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__1___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_3062_, 0, v___f_3060_);
    lean_closure_set(v___f_3062_, 1, v_assertShared_3057_);
    lean_closure_set(v___f_3062_, 2, v_b_3054_);
    lean_closure_set(v___f_3062_, 3, v_toBind_3055_);
    lean_closure_set(v___f_3062_, 4, v___f_3061_);
    lean_closure_set(v___f_3062_, 5, v_t_3053_);
    v___x_3063_ = lean_apply_4(
        v_toBind_3055_,
        lean_box(0),
        lean_box(0),
        v_isDebugEnabled_3058_,
        v___f_3062_,
    );
    return v___x_3063_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___redArg___boxed(
    mut v_inst_3064_: *mut LeanObject,
    mut v_inst_3065_: *mut LeanObject,
    mut v_x_3066_: *mut LeanObject,
    mut v_bi_3067_: *mut LeanObject,
    mut v_t_3068_: *mut LeanObject,
    mut v_b_3069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3070_: u8 = 0;
    let mut v_res_3071_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3070_ = (lean_unbox(v_bi_3067_) as u8);
    v_res_3071_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(
        v_inst_3064_,
        v_inst_3065_,
        v_x_3066_,
        v_bi_boxed_3070_,
        v_t_3068_,
        v_b_3069_,
    );
    return v_res_3071_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS(
    mut v_m_3072_: *mut LeanObject,
    mut v_inst_3073_: *mut LeanObject,
    mut v_inst_3074_: *mut LeanObject,
    mut v_x_3075_: *mut LeanObject,
    mut v_bi_3076_: u8,
    mut v_t_3077_: *mut LeanObject,
    mut v_b_3078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3079_: *mut LeanObject = core::ptr::null_mut();
    v___x_3079_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(
        v_inst_3073_,
        v_inst_3074_,
        v_x_3075_,
        v_bi_3076_,
        v_t_3077_,
        v_b_3078_,
    );
    return v___x_3079_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkForallS___boxed(
    mut v_m_3080_: *mut LeanObject,
    mut v_inst_3081_: *mut LeanObject,
    mut v_inst_3082_: *mut LeanObject,
    mut v_x_3083_: *mut LeanObject,
    mut v_bi_3084_: *mut LeanObject,
    mut v_t_3085_: *mut LeanObject,
    mut v_b_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3087_: u8 = 0;
    let mut v_res_3088_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3087_ = (lean_unbox(v_bi_3084_) as u8);
    v_res_3088_ = l_Lean_Meta_Sym_Internal_mkForallS(
        v_m_3080_,
        v_inst_3081_,
        v_inst_3082_,
        v_x_3083_,
        v_bi_boxed_3087_,
        v_t_3085_,
        v_b_3086_,
    );
    return v_res_3088_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(
    mut v_x_3089_: *mut LeanObject,
    mut v_t_3090_: *mut LeanObject,
    mut v_v_3091_: *mut LeanObject,
    mut v_b_3092_: *mut LeanObject,
    mut v_nondep_3093_: u8,
    mut v_share1_3094_: *mut LeanObject,
    mut v_____r_3095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    v___x_3096_ =
        l_Lean_Expr_letE___override(v_x_3089_, v_t_3090_, v_v_3091_, v_b_3092_, v_nondep_3093_);
    v___x_3097_ = lean_apply_1(v_share1_3094_, v___x_3096_);
    return v___x_3097_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed(
    mut v_x_3098_: *mut LeanObject,
    mut v_t_3099_: *mut LeanObject,
    mut v_v_3100_: *mut LeanObject,
    mut v_b_3101_: *mut LeanObject,
    mut v_nondep_3102_: *mut LeanObject,
    mut v_share1_3103_: *mut LeanObject,
    mut v_____r_3104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_3105_: u8 = 0;
    let mut v_res_3106_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3105_ = (lean_unbox(v_nondep_3102_) as u8);
    v_res_3106_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0(
        v_x_3098_,
        v_t_3099_,
        v_v_3100_,
        v_b_3101_,
        v_nondep_boxed_3105_,
        v_share1_3103_,
        v_____r_3104_,
    );
    return v_res_3106_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3(
    mut v_assertShared_3107_: *mut LeanObject,
    mut v_v_3108_: *mut LeanObject,
    mut v_toBind_3109_: *mut LeanObject,
    mut v___f_3110_: *mut LeanObject,
    mut v_____r_3111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    v___x_3112_ = lean_apply_1(v_assertShared_3107_, v_v_3108_);
    v___x_3113_ = lean_apply_4(
        v_toBind_3109_,
        lean_box(0),
        lean_box(0),
        v___x_3112_,
        v___f_3110_,
    );
    return v___x_3113_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(
    mut v___f_3114_: *mut LeanObject,
    mut v_assertShared_3115_: *mut LeanObject,
    mut v_b_3116_: *mut LeanObject,
    mut v_toBind_3117_: *mut LeanObject,
    mut v___f_3118_: *mut LeanObject,
    mut v_v_3119_: *mut LeanObject,
    mut v_t_3120_: *mut LeanObject,
    mut v_____do__lift_3121_: u8,
) -> *mut LeanObject {
    if v_____do__lift_3121_ == 0 {
        let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_t_3120_);
        lean_dec_ref(v_v_3119_);
        lean_dec(v___f_3118_);
        lean_dec(v_toBind_3117_);
        lean_dec_ref(v_b_3116_);
        lean_dec(v_assertShared_3115_);
        v___x_3122_ = lean_box(0);
        v___x_3123_ = lean_apply_1(v___f_3114_, v___x_3122_);
        return v___x_3123_;
    } else {
        let mut v___f_3124_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_3114_);
        lean_inc_n(v_toBind_3117_, 2);
        lean_inc_n(v_assertShared_3115_, 2);
        v___f_3124_ = lean_alloc_closure(
            l_Lean_Meta_Sym_Internal_mkLambdaS___redArg___lam__2 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_3124_, 0, v_assertShared_3115_);
        lean_closure_set(v___f_3124_, 1, v_b_3116_);
        lean_closure_set(v___f_3124_, 2, v_toBind_3117_);
        lean_closure_set(v___f_3124_, 3, v___f_3118_);
        v___f_3125_ = lean_alloc_closure(
            l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__3 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_3125_, 0, v_assertShared_3115_);
        lean_closure_set(v___f_3125_, 1, v_v_3119_);
        lean_closure_set(v___f_3125_, 2, v_toBind_3117_);
        lean_closure_set(v___f_3125_, 3, v___f_3124_);
        v___x_3126_ = lean_apply_1(v_assertShared_3115_, v_t_3120_);
        v___x_3127_ = lean_apply_4(
            v_toBind_3117_,
            lean_box(0),
            lean_box(0),
            v___x_3126_,
            v___f_3125_,
        );
        return v___x_3127_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed(
    mut v___f_3128_: *mut LeanObject,
    mut v_assertShared_3129_: *mut LeanObject,
    mut v_b_3130_: *mut LeanObject,
    mut v_toBind_3131_: *mut LeanObject,
    mut v___f_3132_: *mut LeanObject,
    mut v_v_3133_: *mut LeanObject,
    mut v_t_3134_: *mut LeanObject,
    mut v_____do__lift_3135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_123__boxed_3136_: u8 = 0;
    let mut v_res_3137_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_123__boxed_3136_ = (lean_unbox(v_____do__lift_3135_) as u8);
    v_res_3137_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1(
        v___f_3128_,
        v_assertShared_3129_,
        v_b_3130_,
        v_toBind_3131_,
        v___f_3132_,
        v_v_3133_,
        v_t_3134_,
        v_____do__lift_123__boxed_3136_,
    );
    return v_res_3137_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___redArg(
    mut v_inst_3138_: *mut LeanObject,
    mut v_inst_3139_: *mut LeanObject,
    mut v_x_3140_: *mut LeanObject,
    mut v_t_3141_: *mut LeanObject,
    mut v_v_3142_: *mut LeanObject,
    mut v_b_3143_: *mut LeanObject,
    mut v_nondep_3144_: u8,
) -> *mut LeanObject {
    let mut v_toBind_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share1_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3145_ = lean_ctor_get(v_inst_3139_, 1);
    lean_inc_n(v_toBind_3145_, 2);
    lean_dec_ref(v_inst_3139_);
    v_share1_3146_ = lean_ctor_get(v_inst_3138_, 0);
    lean_inc(v_share1_3146_);
    v_assertShared_3147_ = lean_ctor_get(v_inst_3138_, 1);
    lean_inc(v_assertShared_3147_);
    v_isDebugEnabled_3148_ = lean_ctor_get(v_inst_3138_, 2);
    lean_inc(v_isDebugEnabled_3148_);
    lean_dec_ref(v_inst_3138_);
    v___x_3149_ = lean_box((v_nondep_3144_) as usize);
    lean_inc_ref(v_b_3143_);
    lean_inc_ref(v_v_3142_);
    lean_inc_ref(v_t_3141_);
    v___f_3150_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_3150_, 0, v_x_3140_);
    lean_closure_set(v___f_3150_, 1, v_t_3141_);
    lean_closure_set(v___f_3150_, 2, v_v_3142_);
    lean_closure_set(v___f_3150_, 3, v_b_3143_);
    lean_closure_set(v___f_3150_, 4, v___x_3149_);
    lean_closure_set(v___f_3150_, 5, v_share1_3146_);
    lean_inc_ref(v___f_3150_);
    v___f_3151_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3151_, 0, v___f_3150_);
    v___f_3152_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_3152_, 0, v___f_3150_);
    lean_closure_set(v___f_3152_, 1, v_assertShared_3147_);
    lean_closure_set(v___f_3152_, 2, v_b_3143_);
    lean_closure_set(v___f_3152_, 3, v_toBind_3145_);
    lean_closure_set(v___f_3152_, 4, v___f_3151_);
    lean_closure_set(v___f_3152_, 5, v_v_3142_);
    lean_closure_set(v___f_3152_, 6, v_t_3141_);
    v___x_3153_ = lean_apply_4(
        v_toBind_3145_,
        lean_box(0),
        lean_box(0),
        v_isDebugEnabled_3148_,
        v___f_3152_,
    );
    return v___x_3153_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___redArg___boxed(
    mut v_inst_3154_: *mut LeanObject,
    mut v_inst_3155_: *mut LeanObject,
    mut v_x_3156_: *mut LeanObject,
    mut v_t_3157_: *mut LeanObject,
    mut v_v_3158_: *mut LeanObject,
    mut v_b_3159_: *mut LeanObject,
    mut v_nondep_3160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_3161_: u8 = 0;
    let mut v_res_3162_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3161_ = (lean_unbox(v_nondep_3160_) as u8);
    v_res_3162_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
        v_inst_3154_,
        v_inst_3155_,
        v_x_3156_,
        v_t_3157_,
        v_v_3158_,
        v_b_3159_,
        v_nondep_boxed_3161_,
    );
    return v_res_3162_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS(
    mut v_m_3163_: *mut LeanObject,
    mut v_inst_3164_: *mut LeanObject,
    mut v_inst_3165_: *mut LeanObject,
    mut v_x_3166_: *mut LeanObject,
    mut v_t_3167_: *mut LeanObject,
    mut v_v_3168_: *mut LeanObject,
    mut v_b_3169_: *mut LeanObject,
    mut v_nondep_3170_: u8,
) -> *mut LeanObject {
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    v___x_3171_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
        v_inst_3164_,
        v_inst_3165_,
        v_x_3166_,
        v_t_3167_,
        v_v_3168_,
        v_b_3169_,
        v_nondep_3170_,
    );
    return v___x_3171_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkLetS___boxed(
    mut v_m_3172_: *mut LeanObject,
    mut v_inst_3173_: *mut LeanObject,
    mut v_inst_3174_: *mut LeanObject,
    mut v_x_3175_: *mut LeanObject,
    mut v_t_3176_: *mut LeanObject,
    mut v_v_3177_: *mut LeanObject,
    mut v_b_3178_: *mut LeanObject,
    mut v_nondep_3179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_3180_: u8 = 0;
    let mut v_res_3181_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_3180_ = (lean_unbox(v_nondep_3179_) as u8);
    v_res_3181_ = l_Lean_Meta_Sym_Internal_mkLetS(
        v_m_3172_,
        v_inst_3173_,
        v_inst_3174_,
        v_x_3175_,
        v_t_3176_,
        v_v_3177_,
        v_b_3178_,
        v_nondep_boxed_3180_,
    );
    return v_res_3181_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0(
    mut v_x_3182_: *mut LeanObject,
    mut v_t_3183_: *mut LeanObject,
    mut v_v_3184_: *mut LeanObject,
    mut v_b_3185_: *mut LeanObject,
    mut v_share1_3186_: *mut LeanObject,
    mut v_____r_3187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3188_: u8 = 0;
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    v___x_3188_ = 1;
    v___x_3189_ =
        l_Lean_Expr_letE___override(v_x_3182_, v_t_3183_, v_v_3184_, v_b_3185_, v___x_3188_);
    v___x_3190_ = lean_apply_1(v_share1_3186_, v___x_3189_);
    return v___x_3190_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkHaveS___redArg(
    mut v_inst_3191_: *mut LeanObject,
    mut v_inst_3192_: *mut LeanObject,
    mut v_x_3193_: *mut LeanObject,
    mut v_t_3194_: *mut LeanObject,
    mut v_v_3195_: *mut LeanObject,
    mut v_b_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_share1_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assertShared_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDebugEnabled_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3197_ = lean_ctor_get(v_inst_3192_, 1);
    lean_inc_n(v_toBind_3197_, 2);
    lean_dec_ref(v_inst_3192_);
    v_share1_3198_ = lean_ctor_get(v_inst_3191_, 0);
    lean_inc(v_share1_3198_);
    v_assertShared_3199_ = lean_ctor_get(v_inst_3191_, 1);
    lean_inc(v_assertShared_3199_);
    v_isDebugEnabled_3200_ = lean_ctor_get(v_inst_3191_, 2);
    lean_inc(v_isDebugEnabled_3200_);
    lean_dec_ref(v_inst_3191_);
    lean_inc_ref(v_b_3196_);
    lean_inc_ref(v_v_3195_);
    lean_inc_ref(v_t_3194_);
    v___f_3201_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkHaveS___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_3201_, 0, v_x_3193_);
    lean_closure_set(v___f_3201_, 1, v_t_3194_);
    lean_closure_set(v___f_3201_, 2, v_v_3195_);
    lean_closure_set(v___f_3201_, 3, v_b_3196_);
    lean_closure_set(v___f_3201_, 4, v_share1_3198_);
    lean_inc_ref(v___f_3201_);
    v___f_3202_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkMDataS___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3202_, 0, v___f_3201_);
    v___f_3203_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkLetS___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_3203_, 0, v___f_3201_);
    lean_closure_set(v___f_3203_, 1, v_assertShared_3199_);
    lean_closure_set(v___f_3203_, 2, v_b_3196_);
    lean_closure_set(v___f_3203_, 3, v_toBind_3197_);
    lean_closure_set(v___f_3203_, 4, v___f_3202_);
    lean_closure_set(v___f_3203_, 5, v_v_3195_);
    lean_closure_set(v___f_3203_, 6, v_t_3194_);
    v___x_3204_ = lean_apply_4(
        v_toBind_3197_,
        lean_box(0),
        lean_box(0),
        v_isDebugEnabled_3200_,
        v___f_3203_,
    );
    return v___x_3204_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkHaveS(
    mut v_m_3205_: *mut LeanObject,
    mut v_inst_3206_: *mut LeanObject,
    mut v_inst_3207_: *mut LeanObject,
    mut v_x_3208_: *mut LeanObject,
    mut v_t_3209_: *mut LeanObject,
    mut v_v_3210_: *mut LeanObject,
    mut v_b_3211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    v___x_3212_ = l_Lean_Meta_Sym_Internal_mkHaveS___redArg(
        v_inst_3206_,
        v_inst_3207_,
        v_x_3208_,
        v_t_3209_,
        v_v_3210_,
        v_b_3211_,
    );
    return v___x_3212_;
}
pub unsafe fn _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    v___x_3215_ = l_Lean_Expr_updateAppS_x21___redArg___closed__1;
    v___x_3216_ = lean_unsigned_to_nat(25);
    v___x_3217_ = lean_unsigned_to_nat(148);
    v___x_3218_ = l_Lean_Expr_updateAppS_x21___redArg___closed__0;
    v___x_3219_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0;
    v___x_3220_ = l_mkPanicMessageWithDecl(
        v___x_3219_,
        v___x_3218_,
        v___x_3217_,
        v___x_3216_,
        v___x_3215_,
    );
    return v___x_3220_;
}
pub unsafe fn l_Lean_Expr_updateAppS_x21___redArg(
    mut v_inst_3221_: *mut LeanObject,
    mut v_inst_3222_: *mut LeanObject,
    mut v_e_3223_: *mut LeanObject,
    mut v_newFn_3224_: *mut LeanObject,
    mut v_newArg_3225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3227_: u8 = 0;
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: u8 = 0;
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3223_) == 5 {
                    v_fn_3232_ = lean_ctor_get(v_e_3223_, 0);
                    v_arg_3233_ = lean_ctor_get(v_e_3223_, 1);
                    v___x_3234_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fn_3232_,
                            v_newFn_3224_,
                        );
                    if v___x_3234_ == 0 {
                        v___y_3227_ = v___x_3234_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3235_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_arg_3233_,
                                v_newArg_3225_,
                            );
                        v___y_3227_ = v___x_3235_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newArg_3225_);
                    lean_dec_ref(v_newFn_3224_);
                    lean_dec_ref(v_e_3223_);
                    lean_dec_ref(v_inst_3221_);
                    v___x_3236_ = l_Lean_instInhabitedExpr;
                    v___x_3237_ = l_instInhabitedOfMonad___redArg(v_inst_3222_, v___x_3236_);
                    v___x_3238_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Expr_updateAppS_x21___redArg___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Expr_updateAppS_x21___redArg___closed__2_once
                        ),
                        _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2,
                    );
                    v___x_3239_ = l_panic___redArg(v___x_3237_, v___x_3238_);
                    lean_dec(v___x_3237_);
                    return v___x_3239_;
                }
            }
            1 => {
                if v___y_3227_ == 0 {
                    lean_dec_ref(v_e_3223_);
                    v___x_3228_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
                        v_inst_3221_,
                        v_inst_3222_,
                        v_newFn_3224_,
                        v_newArg_3225_,
                    );
                    return v___x_3228_;
                } else {
                    lean_dec_ref(v_newArg_3225_);
                    lean_dec_ref(v_newFn_3224_);
                    lean_dec_ref(v_inst_3221_);
                    v_toApplicative_3229_ = lean_ctor_get(v_inst_3222_, 0);
                    lean_inc_ref(v_toApplicative_3229_);
                    lean_dec_ref(v_inst_3222_);
                    v_toPure_3230_ = lean_ctor_get(v_toApplicative_3229_, 1);
                    lean_inc(v_toPure_3230_);
                    lean_dec_ref(v_toApplicative_3229_);
                    v___x_3231_ = lean_apply_2(v_toPure_3230_, lean_box(0), v_e_3223_);
                    return v___x_3231_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_updateAppS_x21(
    mut v_m_3240_: *mut LeanObject,
    mut v_inst_3241_: *mut LeanObject,
    mut v_inst_3242_: *mut LeanObject,
    mut v_e_3243_: *mut LeanObject,
    mut v_newFn_3244_: *mut LeanObject,
    mut v_newArg_3245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: u8 = 0;
    let mut v___x_3255_: u8 = 0;
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3243_) == 5 {
                    v_fn_3252_ = lean_ctor_get(v_e_3243_, 0);
                    v_arg_3253_ = lean_ctor_get(v_e_3243_, 1);
                    v___x_3254_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fn_3252_,
                            v_newFn_3244_,
                        );
                    if v___x_3254_ == 0 {
                        v___y_3247_ = v___x_3254_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3255_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_arg_3253_,
                                v_newArg_3245_,
                            );
                        v___y_3247_ = v___x_3255_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newArg_3245_);
                    lean_dec_ref(v_newFn_3244_);
                    lean_dec_ref(v_e_3243_);
                    lean_dec_ref(v_inst_3241_);
                    v___x_3256_ = l_Lean_instInhabitedExpr;
                    v___x_3257_ = l_instInhabitedOfMonad___redArg(v_inst_3242_, v___x_3256_);
                    v___x_3258_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Expr_updateAppS_x21___redArg___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Expr_updateAppS_x21___redArg___closed__2_once
                        ),
                        _init_l_Lean_Expr_updateAppS_x21___redArg___closed__2,
                    );
                    v___x_3259_ = l_panic___redArg(v___x_3257_, v___x_3258_);
                    lean_dec(v___x_3257_);
                    return v___x_3259_;
                }
            }
            1 => {
                if v___y_3247_ == 0 {
                    lean_dec_ref(v_e_3243_);
                    v___x_3248_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
                        v_inst_3241_,
                        v_inst_3242_,
                        v_newFn_3244_,
                        v_newArg_3245_,
                    );
                    return v___x_3248_;
                } else {
                    lean_dec_ref(v_newArg_3245_);
                    lean_dec_ref(v_newFn_3244_);
                    lean_dec_ref(v_inst_3241_);
                    v_toApplicative_3249_ = lean_ctor_get(v_inst_3242_, 0);
                    lean_inc_ref(v_toApplicative_3249_);
                    lean_dec_ref(v_inst_3242_);
                    v_toPure_3250_ = lean_ctor_get(v_toApplicative_3249_, 1);
                    lean_inc(v_toPure_3250_);
                    lean_dec_ref(v_toApplicative_3249_);
                    v___x_3251_ = lean_apply_2(v_toPure_3250_, lean_box(0), v_e_3243_);
                    return v___x_3251_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    v___x_3262_ = l_Lean_Expr_updateMDataS_x21___redArg___closed__1;
    v___x_3263_ = lean_unsigned_to_nat(24);
    v___x_3264_ = lean_unsigned_to_nat(152);
    v___x_3265_ = l_Lean_Expr_updateMDataS_x21___redArg___closed__0;
    v___x_3266_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0;
    v___x_3267_ = l_mkPanicMessageWithDecl(
        v___x_3266_,
        v___x_3265_,
        v___x_3264_,
        v___x_3263_,
        v___x_3262_,
    );
    return v___x_3267_;
}
pub unsafe fn l_Lean_Expr_updateMDataS_x21___redArg(
    mut v_inst_3268_: *mut LeanObject,
    mut v_inst_3269_: *mut LeanObject,
    mut v_e_3270_: *mut LeanObject,
    mut v_newExpr_3271_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_3270_) == 10 {
        let mut v_data_3272_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expr_3273_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3274_: u8 = 0;
        v_data_3272_ = lean_ctor_get(v_e_3270_, 0);
        v_expr_3273_ = lean_ctor_get(v_e_3270_, 1);
        v___x_3274_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v_expr_3273_,
            v_newExpr_3271_,
        );
        if v___x_3274_ == 0 {
            let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_data_3272_);
            lean_dec_ref_known(v_e_3270_, 2);
            v___x_3275_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(
                v_inst_3268_,
                v_inst_3269_,
                v_data_3272_,
                v_newExpr_3271_,
            );
            return v___x_3275_;
        } else {
            let mut v_toApplicative_3276_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3277_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_newExpr_3271_);
            lean_dec_ref(v_inst_3268_);
            v_toApplicative_3276_ = lean_ctor_get(v_inst_3269_, 0);
            lean_inc_ref(v_toApplicative_3276_);
            lean_dec_ref(v_inst_3269_);
            v_toPure_3277_ = lean_ctor_get(v_toApplicative_3276_, 1);
            lean_inc(v_toPure_3277_);
            lean_dec_ref(v_toApplicative_3276_);
            v___x_3278_ = lean_apply_2(v_toPure_3277_, lean_box(0), v_e_3270_);
            return v___x_3278_;
        }
    } else {
        let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_newExpr_3271_);
        lean_dec_ref(v_e_3270_);
        lean_dec_ref(v_inst_3268_);
        v___x_3279_ = l_Lean_instInhabitedExpr;
        v___x_3280_ = l_instInhabitedOfMonad___redArg(v_inst_3269_, v___x_3279_);
        v___x_3281_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Expr_updateMDataS_x21___redArg___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once),
            _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2,
        );
        v___x_3282_ = l_panic___redArg(v___x_3280_, v___x_3281_);
        lean_dec(v___x_3280_);
        return v___x_3282_;
    }
}
pub unsafe fn l_Lean_Expr_updateMDataS_x21(
    mut v_m_3283_: *mut LeanObject,
    mut v_inst_3284_: *mut LeanObject,
    mut v_inst_3285_: *mut LeanObject,
    mut v_e_3286_: *mut LeanObject,
    mut v_newExpr_3287_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_3286_) == 10 {
        let mut v_data_3288_: *mut LeanObject = core::ptr::null_mut();
        let mut v_expr_3289_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3290_: u8 = 0;
        v_data_3288_ = lean_ctor_get(v_e_3286_, 0);
        v_expr_3289_ = lean_ctor_get(v_e_3286_, 1);
        v___x_3290_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v_expr_3289_,
            v_newExpr_3287_,
        );
        if v___x_3290_ == 0 {
            let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_data_3288_);
            lean_dec_ref_known(v_e_3286_, 2);
            v___x_3291_ = l_Lean_Meta_Sym_Internal_mkMDataS___redArg(
                v_inst_3284_,
                v_inst_3285_,
                v_data_3288_,
                v_newExpr_3287_,
            );
            return v___x_3291_;
        } else {
            let mut v_toApplicative_3292_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3293_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_newExpr_3287_);
            lean_dec_ref(v_inst_3284_);
            v_toApplicative_3292_ = lean_ctor_get(v_inst_3285_, 0);
            lean_inc_ref(v_toApplicative_3292_);
            lean_dec_ref(v_inst_3285_);
            v_toPure_3293_ = lean_ctor_get(v_toApplicative_3292_, 1);
            lean_inc(v_toPure_3293_);
            lean_dec_ref(v_toApplicative_3292_);
            v___x_3294_ = lean_apply_2(v_toPure_3293_, lean_box(0), v_e_3286_);
            return v___x_3294_;
        }
    } else {
        let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_newExpr_3287_);
        lean_dec_ref(v_e_3286_);
        lean_dec_ref(v_inst_3284_);
        v___x_3295_ = l_Lean_instInhabitedExpr;
        v___x_3296_ = l_instInhabitedOfMonad___redArg(v_inst_3285_, v___x_3295_);
        v___x_3297_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Expr_updateMDataS_x21___redArg___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Expr_updateMDataS_x21___redArg___closed__2_once),
            _init_l_Lean_Expr_updateMDataS_x21___redArg___closed__2,
        );
        v___x_3298_ = l_panic___redArg(v___x_3296_, v___x_3297_);
        lean_dec(v___x_3296_);
        return v___x_3298_;
    }
}
pub unsafe fn _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    v___x_3301_ = l_Lean_Expr_updateProjS_x21___redArg___closed__1;
    v___x_3302_ = lean_unsigned_to_nat(25);
    v___x_3303_ = lean_unsigned_to_nat(156);
    v___x_3304_ = l_Lean_Expr_updateProjS_x21___redArg___closed__0;
    v___x_3305_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0;
    v___x_3306_ = l_mkPanicMessageWithDecl(
        v___x_3305_,
        v___x_3304_,
        v___x_3303_,
        v___x_3302_,
        v___x_3301_,
    );
    return v___x_3306_;
}
pub unsafe fn l_Lean_Expr_updateProjS_x21___redArg(
    mut v_inst_3307_: *mut LeanObject,
    mut v_inst_3308_: *mut LeanObject,
    mut v_e_3309_: *mut LeanObject,
    mut v_newExpr_3310_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_3309_) == 11 {
        let mut v_typeName_3311_: *mut LeanObject = core::ptr::null_mut();
        let mut v_idx_3312_: *mut LeanObject = core::ptr::null_mut();
        let mut v_struct_3313_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3314_: u8 = 0;
        v_typeName_3311_ = lean_ctor_get(v_e_3309_, 0);
        v_idx_3312_ = lean_ctor_get(v_e_3309_, 1);
        v_struct_3313_ = lean_ctor_get(v_e_3309_, 2);
        v___x_3314_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v_struct_3313_,
            v_newExpr_3310_,
        );
        if v___x_3314_ == 0 {
            let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_idx_3312_);
            lean_inc(v_typeName_3311_);
            lean_dec_ref_known(v_e_3309_, 3);
            v___x_3315_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(
                v_inst_3307_,
                v_inst_3308_,
                v_typeName_3311_,
                v_idx_3312_,
                v_newExpr_3310_,
            );
            return v___x_3315_;
        } else {
            let mut v_toApplicative_3316_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_newExpr_3310_);
            lean_dec_ref(v_inst_3307_);
            v_toApplicative_3316_ = lean_ctor_get(v_inst_3308_, 0);
            lean_inc_ref(v_toApplicative_3316_);
            lean_dec_ref(v_inst_3308_);
            v_toPure_3317_ = lean_ctor_get(v_toApplicative_3316_, 1);
            lean_inc(v_toPure_3317_);
            lean_dec_ref(v_toApplicative_3316_);
            v___x_3318_ = lean_apply_2(v_toPure_3317_, lean_box(0), v_e_3309_);
            return v___x_3318_;
        }
    } else {
        let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3320_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3322_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_newExpr_3310_);
        lean_dec_ref(v_e_3309_);
        lean_dec_ref(v_inst_3307_);
        v___x_3319_ = l_Lean_instInhabitedExpr;
        v___x_3320_ = l_instInhabitedOfMonad___redArg(v_inst_3308_, v___x_3319_);
        v___x_3321_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Expr_updateProjS_x21___redArg___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Expr_updateProjS_x21___redArg___closed__2_once),
            _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2,
        );
        v___x_3322_ = l_panic___redArg(v___x_3320_, v___x_3321_);
        lean_dec(v___x_3320_);
        return v___x_3322_;
    }
}
pub unsafe fn l_Lean_Expr_updateProjS_x21(
    mut v_m_3323_: *mut LeanObject,
    mut v_inst_3324_: *mut LeanObject,
    mut v_inst_3325_: *mut LeanObject,
    mut v_e_3326_: *mut LeanObject,
    mut v_newExpr_3327_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_3326_) == 11 {
        let mut v_typeName_3328_: *mut LeanObject = core::ptr::null_mut();
        let mut v_idx_3329_: *mut LeanObject = core::ptr::null_mut();
        let mut v_struct_3330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3331_: u8 = 0;
        v_typeName_3328_ = lean_ctor_get(v_e_3326_, 0);
        v_idx_3329_ = lean_ctor_get(v_e_3326_, 1);
        v_struct_3330_ = lean_ctor_get(v_e_3326_, 2);
        v___x_3331_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
            v_struct_3330_,
            v_newExpr_3327_,
        );
        if v___x_3331_ == 0 {
            let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_idx_3329_);
            lean_inc(v_typeName_3328_);
            lean_dec_ref_known(v_e_3326_, 3);
            v___x_3332_ = l_Lean_Meta_Sym_Internal_mkProjS___redArg(
                v_inst_3324_,
                v_inst_3325_,
                v_typeName_3328_,
                v_idx_3329_,
                v_newExpr_3327_,
            );
            return v___x_3332_;
        } else {
            let mut v_toApplicative_3333_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toPure_3334_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_newExpr_3327_);
            lean_dec_ref(v_inst_3324_);
            v_toApplicative_3333_ = lean_ctor_get(v_inst_3325_, 0);
            lean_inc_ref(v_toApplicative_3333_);
            lean_dec_ref(v_inst_3325_);
            v_toPure_3334_ = lean_ctor_get(v_toApplicative_3333_, 1);
            lean_inc(v_toPure_3334_);
            lean_dec_ref(v_toApplicative_3333_);
            v___x_3335_ = lean_apply_2(v_toPure_3334_, lean_box(0), v_e_3326_);
            return v___x_3335_;
        }
    } else {
        let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_newExpr_3327_);
        lean_dec_ref(v_e_3326_);
        lean_dec_ref(v_inst_3324_);
        v___x_3336_ = l_Lean_instInhabitedExpr;
        v___x_3337_ = l_instInhabitedOfMonad___redArg(v_inst_3325_, v___x_3336_);
        v___x_3338_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Expr_updateProjS_x21___redArg___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Expr_updateProjS_x21___redArg___closed__2_once),
            _init_l_Lean_Expr_updateProjS_x21___redArg___closed__2,
        );
        v___x_3339_ = l_panic___redArg(v___x_3337_, v___x_3338_);
        lean_dec(v___x_3337_);
        return v___x_3339_;
    }
}
pub unsafe fn _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    v___x_3342_ = l_Lean_Expr_updateForallS_x21___redArg___closed__1;
    v___x_3343_ = lean_unsigned_to_nat(31);
    v___x_3344_ = lean_unsigned_to_nat(160);
    v___x_3345_ = l_Lean_Expr_updateForallS_x21___redArg___closed__0;
    v___x_3346_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0;
    v___x_3347_ = l_mkPanicMessageWithDecl(
        v___x_3346_,
        v___x_3345_,
        v___x_3344_,
        v___x_3343_,
        v___x_3342_,
    );
    return v___x_3347_;
}
pub unsafe fn l_Lean_Expr_updateForallS_x21___redArg(
    mut v_inst_3348_: *mut LeanObject,
    mut v_inst_3349_: *mut LeanObject,
    mut v_e_3350_: *mut LeanObject,
    mut v_newDomain_3351_: *mut LeanObject,
    mut v_newBody_3352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderName_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3356_: u8 = 0;
    let mut v___y_3358_: u8 = 0;
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: u8 = 0;
    let mut v___x_3364_: u8 = 0;
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3350_) == 7 {
                    v_binderName_3353_ = lean_ctor_get(v_e_3350_, 0);
                    v_binderType_3354_ = lean_ctor_get(v_e_3350_, 1);
                    v_body_3355_ = lean_ctor_get(v_e_3350_, 2);
                    v_binderInfo_3356_ = lean_ctor_get_uint8(
                        v_e_3350_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_3363_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_binderType_3354_,
                            v_newDomain_3351_,
                        );
                    if v___x_3363_ == 0 {
                        v___y_3358_ = v___x_3363_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3364_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_body_3355_,
                                v_newBody_3352_,
                            );
                        v___y_3358_ = v___x_3364_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newBody_3352_);
                    lean_dec_ref(v_newDomain_3351_);
                    lean_dec_ref(v_e_3350_);
                    lean_dec_ref(v_inst_3348_);
                    v___x_3365_ = l_Lean_instInhabitedExpr;
                    v___x_3366_ = l_instInhabitedOfMonad___redArg(v_inst_3349_, v___x_3365_);
                    v___x_3367_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Expr_updateForallS_x21___redArg___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Expr_updateForallS_x21___redArg___closed__2_once
                        ),
                        _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2,
                    );
                    v___x_3368_ = l_panic___redArg(v___x_3366_, v___x_3367_);
                    lean_dec(v___x_3366_);
                    return v___x_3368_;
                }
            }
            1 => {
                if v___y_3358_ == 0 {
                    lean_inc(v_binderName_3353_);
                    lean_dec_ref_known(v_e_3350_, 3);
                    v___x_3359_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(
                        v_inst_3348_,
                        v_inst_3349_,
                        v_binderName_3353_,
                        v_binderInfo_3356_,
                        v_newDomain_3351_,
                        v_newBody_3352_,
                    );
                    return v___x_3359_;
                } else {
                    lean_dec_ref(v_newBody_3352_);
                    lean_dec_ref(v_newDomain_3351_);
                    lean_dec_ref(v_inst_3348_);
                    v_toApplicative_3360_ = lean_ctor_get(v_inst_3349_, 0);
                    lean_inc_ref(v_toApplicative_3360_);
                    lean_dec_ref(v_inst_3349_);
                    v_toPure_3361_ = lean_ctor_get(v_toApplicative_3360_, 1);
                    lean_inc(v_toPure_3361_);
                    lean_dec_ref(v_toApplicative_3360_);
                    v___x_3362_ = lean_apply_2(v_toPure_3361_, lean_box(0), v_e_3350_);
                    return v___x_3362_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_updateForallS_x21(
    mut v_m_3369_: *mut LeanObject,
    mut v_inst_3370_: *mut LeanObject,
    mut v_inst_3371_: *mut LeanObject,
    mut v_e_3372_: *mut LeanObject,
    mut v_newDomain_3373_: *mut LeanObject,
    mut v_newBody_3374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderName_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3378_: u8 = 0;
    let mut v___y_3380_: u8 = 0;
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: u8 = 0;
    let mut v___x_3386_: u8 = 0;
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3372_) == 7 {
                    v_binderName_3375_ = lean_ctor_get(v_e_3372_, 0);
                    v_binderType_3376_ = lean_ctor_get(v_e_3372_, 1);
                    v_body_3377_ = lean_ctor_get(v_e_3372_, 2);
                    v_binderInfo_3378_ = lean_ctor_get_uint8(
                        v_e_3372_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_3385_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_binderType_3376_,
                            v_newDomain_3373_,
                        );
                    if v___x_3385_ == 0 {
                        v___y_3380_ = v___x_3385_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3386_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_body_3377_,
                                v_newBody_3374_,
                            );
                        v___y_3380_ = v___x_3386_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newBody_3374_);
                    lean_dec_ref(v_newDomain_3373_);
                    lean_dec_ref(v_e_3372_);
                    lean_dec_ref(v_inst_3370_);
                    v___x_3387_ = l_Lean_instInhabitedExpr;
                    v___x_3388_ = l_instInhabitedOfMonad___redArg(v_inst_3371_, v___x_3387_);
                    v___x_3389_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Expr_updateForallS_x21___redArg___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Expr_updateForallS_x21___redArg___closed__2_once
                        ),
                        _init_l_Lean_Expr_updateForallS_x21___redArg___closed__2,
                    );
                    v___x_3390_ = l_panic___redArg(v___x_3388_, v___x_3389_);
                    lean_dec(v___x_3388_);
                    return v___x_3390_;
                }
            }
            1 => {
                if v___y_3380_ == 0 {
                    lean_inc(v_binderName_3375_);
                    lean_dec_ref_known(v_e_3372_, 3);
                    v___x_3381_ = l_Lean_Meta_Sym_Internal_mkForallS___redArg(
                        v_inst_3370_,
                        v_inst_3371_,
                        v_binderName_3375_,
                        v_binderInfo_3378_,
                        v_newDomain_3373_,
                        v_newBody_3374_,
                    );
                    return v___x_3381_;
                } else {
                    lean_dec_ref(v_newBody_3374_);
                    lean_dec_ref(v_newDomain_3373_);
                    lean_dec_ref(v_inst_3370_);
                    v_toApplicative_3382_ = lean_ctor_get(v_inst_3371_, 0);
                    lean_inc_ref(v_toApplicative_3382_);
                    lean_dec_ref(v_inst_3371_);
                    v_toPure_3383_ = lean_ctor_get(v_toApplicative_3382_, 1);
                    lean_inc(v_toPure_3383_);
                    lean_dec_ref(v_toApplicative_3382_);
                    v___x_3384_ = lean_apply_2(v_toPure_3383_, lean_box(0), v_e_3372_);
                    return v___x_3384_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    v___x_3393_ = l_Lean_Expr_updateLambdaS_x21___redArg___closed__1;
    v___x_3394_ = lean_unsigned_to_nat(27);
    v___x_3395_ = lean_unsigned_to_nat(167);
    v___x_3396_ = l_Lean_Expr_updateLambdaS_x21___redArg___closed__0;
    v___x_3397_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0;
    v___x_3398_ = l_mkPanicMessageWithDecl(
        v___x_3397_,
        v___x_3396_,
        v___x_3395_,
        v___x_3394_,
        v___x_3393_,
    );
    return v___x_3398_;
}
pub unsafe fn l_Lean_Expr_updateLambdaS_x21___redArg(
    mut v_inst_3399_: *mut LeanObject,
    mut v_inst_3400_: *mut LeanObject,
    mut v_e_3401_: *mut LeanObject,
    mut v_newDomain_3402_: *mut LeanObject,
    mut v_newBody_3403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderName_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3407_: u8 = 0;
    let mut v___y_3409_: u8 = 0;
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: u8 = 0;
    let mut v___x_3415_: u8 = 0;
    let mut v___x_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3401_) == 6 {
                    v_binderName_3404_ = lean_ctor_get(v_e_3401_, 0);
                    v_binderType_3405_ = lean_ctor_get(v_e_3401_, 1);
                    v_body_3406_ = lean_ctor_get(v_e_3401_, 2);
                    v_binderInfo_3407_ = lean_ctor_get_uint8(
                        v_e_3401_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_3414_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_binderType_3405_,
                            v_newDomain_3402_,
                        );
                    if v___x_3414_ == 0 {
                        v___y_3409_ = v___x_3414_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3415_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_body_3406_,
                                v_newBody_3403_,
                            );
                        v___y_3409_ = v___x_3415_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newBody_3403_);
                    lean_dec_ref(v_newDomain_3402_);
                    lean_dec_ref(v_e_3401_);
                    lean_dec_ref(v_inst_3399_);
                    v___x_3416_ = l_Lean_instInhabitedExpr;
                    v___x_3417_ = l_instInhabitedOfMonad___redArg(v_inst_3400_, v___x_3416_);
                    v___x_3418_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Expr_updateLambdaS_x21___redArg___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once
                        ),
                        _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2,
                    );
                    v___x_3419_ = l_panic___redArg(v___x_3417_, v___x_3418_);
                    lean_dec(v___x_3417_);
                    return v___x_3419_;
                }
            }
            1 => {
                if v___y_3409_ == 0 {
                    lean_inc(v_binderName_3404_);
                    lean_dec_ref_known(v_e_3401_, 3);
                    v___x_3410_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(
                        v_inst_3399_,
                        v_inst_3400_,
                        v_binderName_3404_,
                        v_binderInfo_3407_,
                        v_newDomain_3402_,
                        v_newBody_3403_,
                    );
                    return v___x_3410_;
                } else {
                    lean_dec_ref(v_newBody_3403_);
                    lean_dec_ref(v_newDomain_3402_);
                    lean_dec_ref(v_inst_3399_);
                    v_toApplicative_3411_ = lean_ctor_get(v_inst_3400_, 0);
                    lean_inc_ref(v_toApplicative_3411_);
                    lean_dec_ref(v_inst_3400_);
                    v_toPure_3412_ = lean_ctor_get(v_toApplicative_3411_, 1);
                    lean_inc(v_toPure_3412_);
                    lean_dec_ref(v_toApplicative_3411_);
                    v___x_3413_ = lean_apply_2(v_toPure_3412_, lean_box(0), v_e_3401_);
                    return v___x_3413_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_updateLambdaS_x21(
    mut v_m_3420_: *mut LeanObject,
    mut v_inst_3421_: *mut LeanObject,
    mut v_inst_3422_: *mut LeanObject,
    mut v_e_3423_: *mut LeanObject,
    mut v_newDomain_3424_: *mut LeanObject,
    mut v_newBody_3425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderName_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3429_: u8 = 0;
    let mut v___y_3431_: u8 = 0;
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3423_) == 6 {
                    v_binderName_3426_ = lean_ctor_get(v_e_3423_, 0);
                    v_binderType_3427_ = lean_ctor_get(v_e_3423_, 1);
                    v_body_3428_ = lean_ctor_get(v_e_3423_, 2);
                    v_binderInfo_3429_ = lean_ctor_get_uint8(
                        v_e_3423_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    v___x_3436_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_binderType_3427_,
                            v_newDomain_3424_,
                        );
                    if v___x_3436_ == 0 {
                        v___y_3431_ = v___x_3436_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3437_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_body_3428_,
                                v_newBody_3425_,
                            );
                        v___y_3431_ = v___x_3437_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newBody_3425_);
                    lean_dec_ref(v_newDomain_3424_);
                    lean_dec_ref(v_e_3423_);
                    lean_dec_ref(v_inst_3421_);
                    v___x_3438_ = l_Lean_instInhabitedExpr;
                    v___x_3439_ = l_instInhabitedOfMonad___redArg(v_inst_3422_, v___x_3438_);
                    v___x_3440_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Expr_updateLambdaS_x21___redArg___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Expr_updateLambdaS_x21___redArg___closed__2_once
                        ),
                        _init_l_Lean_Expr_updateLambdaS_x21___redArg___closed__2,
                    );
                    v___x_3441_ = l_panic___redArg(v___x_3439_, v___x_3440_);
                    lean_dec(v___x_3439_);
                    return v___x_3441_;
                }
            }
            1 => {
                if v___y_3431_ == 0 {
                    lean_inc(v_binderName_3426_);
                    lean_dec_ref_known(v_e_3423_, 3);
                    v___x_3432_ = l_Lean_Meta_Sym_Internal_mkLambdaS___redArg(
                        v_inst_3421_,
                        v_inst_3422_,
                        v_binderName_3426_,
                        v_binderInfo_3429_,
                        v_newDomain_3424_,
                        v_newBody_3425_,
                    );
                    return v___x_3432_;
                } else {
                    lean_dec_ref(v_newBody_3425_);
                    lean_dec_ref(v_newDomain_3424_);
                    lean_dec_ref(v_inst_3421_);
                    v_toApplicative_3433_ = lean_ctor_get(v_inst_3422_, 0);
                    lean_inc_ref(v_toApplicative_3433_);
                    lean_dec_ref(v_inst_3422_);
                    v_toPure_3434_ = lean_ctor_get(v_toApplicative_3433_, 1);
                    lean_inc(v_toPure_3434_);
                    lean_dec_ref(v_toApplicative_3433_);
                    v___x_3435_ = lean_apply_2(v_toPure_3434_, lean_box(0), v_e_3423_);
                    return v___x_3435_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    v___x_3444_ = l_Lean_Expr_updateLetS_x21___redArg___closed__1;
    v___x_3445_ = lean_unsigned_to_nat(34);
    v___x_3446_ = lean_unsigned_to_nat(174);
    v___x_3447_ = l_Lean_Expr_updateLetS_x21___redArg___closed__0;
    v___x_3448_ = l_Lean_Meta_Sym_Internal_Sym_assertShared___closed__0;
    v___x_3449_ = l_mkPanicMessageWithDecl(
        v___x_3448_,
        v___x_3447_,
        v___x_3446_,
        v___x_3445_,
        v___x_3444_,
    );
    return v___x_3449_;
}
pub unsafe fn l_Lean_Expr_updateLetS_x21___redArg(
    mut v_inst_3450_: *mut LeanObject,
    mut v_inst_3451_: *mut LeanObject,
    mut v_e_3452_: *mut LeanObject,
    mut v_newType_3453_: *mut LeanObject,
    mut v_newVal_3454_: *mut LeanObject,
    mut v_newBody_3455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_3460_: u8 = 0;
    let mut v___y_3462_: u8 = 0;
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: u8 = 0;
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3452_) == 8 {
                    v_declName_3456_ = lean_ctor_get(v_e_3452_, 0);
                    v_type_3457_ = lean_ctor_get(v_e_3452_, 1);
                    v_value_3458_ = lean_ctor_get(v_e_3452_, 2);
                    v_body_3459_ = lean_ctor_get(v_e_3452_, 3);
                    v_nondep_3460_ = lean_ctor_get_uint8(
                        v_e_3452_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    v___x_3469_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_type_3457_,
                            v_newType_3453_,
                        );
                    if v___x_3469_ == 0 {
                        v___y_3462_ = v___x_3469_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3470_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_value_3458_,
                                v_newVal_3454_,
                            );
                        v___y_3462_ = v___x_3470_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newBody_3455_);
                    lean_dec_ref(v_newVal_3454_);
                    lean_dec_ref(v_newType_3453_);
                    lean_dec_ref(v_e_3452_);
                    lean_dec_ref(v_inst_3450_);
                    v___x_3471_ = l_Lean_instInhabitedExpr;
                    v___x_3472_ = l_instInhabitedOfMonad___redArg(v_inst_3451_, v___x_3471_);
                    v___x_3473_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Expr_updateLetS_x21___redArg___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Expr_updateLetS_x21___redArg___closed__2_once
                        ),
                        _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2,
                    );
                    v___x_3474_ = l_panic___redArg(v___x_3472_, v___x_3473_);
                    lean_dec(v___x_3472_);
                    return v___x_3474_;
                }
            }
            1 => {
                if v___y_3462_ == 0 {
                    lean_inc(v_declName_3456_);
                    lean_dec_ref_known(v_e_3452_, 4);
                    v___x_3463_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
                        v_inst_3450_,
                        v_inst_3451_,
                        v_declName_3456_,
                        v_newType_3453_,
                        v_newVal_3454_,
                        v_newBody_3455_,
                        v_nondep_3460_,
                    );
                    return v___x_3463_;
                } else {
                    v___x_3464_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_3459_,
                            v_newBody_3455_,
                        );
                    if v___x_3464_ == 0 {
                        lean_inc(v_declName_3456_);
                        lean_dec_ref_known(v_e_3452_, 4);
                        v___x_3465_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
                            v_inst_3450_,
                            v_inst_3451_,
                            v_declName_3456_,
                            v_newType_3453_,
                            v_newVal_3454_,
                            v_newBody_3455_,
                            v_nondep_3460_,
                        );
                        return v___x_3465_;
                    } else {
                        lean_dec_ref(v_newBody_3455_);
                        lean_dec_ref(v_newVal_3454_);
                        lean_dec_ref(v_newType_3453_);
                        lean_dec_ref(v_inst_3450_);
                        v_toApplicative_3466_ = lean_ctor_get(v_inst_3451_, 0);
                        lean_inc_ref(v_toApplicative_3466_);
                        lean_dec_ref(v_inst_3451_);
                        v_toPure_3467_ = lean_ctor_get(v_toApplicative_3466_, 1);
                        lean_inc(v_toPure_3467_);
                        lean_dec_ref(v_toApplicative_3466_);
                        v___x_3468_ = lean_apply_2(v_toPure_3467_, lean_box(0), v_e_3452_);
                        return v___x_3468_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_updateLetS_x21(
    mut v_m_3475_: *mut LeanObject,
    mut v_inst_3476_: *mut LeanObject,
    mut v_inst_3477_: *mut LeanObject,
    mut v_e_3478_: *mut LeanObject,
    mut v_newType_3479_: *mut LeanObject,
    mut v_newVal_3480_: *mut LeanObject,
    mut v_newBody_3481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_3486_: u8 = 0;
    let mut v___y_3488_: u8 = 0;
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: u8 = 0;
    let mut v___x_3496_: u8 = 0;
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_3478_) == 8 {
                    v_declName_3482_ = lean_ctor_get(v_e_3478_, 0);
                    v_type_3483_ = lean_ctor_get(v_e_3478_, 1);
                    v_value_3484_ = lean_ctor_get(v_e_3478_, 2);
                    v_body_3485_ = lean_ctor_get(v_e_3478_, 3);
                    v_nondep_3486_ = lean_ctor_get_uint8(
                        v_e_3478_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    v___x_3495_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_type_3483_,
                            v_newType_3479_,
                        );
                    if v___x_3495_ == 0 {
                        v___y_3488_ = v___x_3495_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3496_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_value_3484_,
                                v_newVal_3480_,
                            );
                        v___y_3488_ = v___x_3496_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_newBody_3481_);
                    lean_dec_ref(v_newVal_3480_);
                    lean_dec_ref(v_newType_3479_);
                    lean_dec_ref(v_e_3478_);
                    lean_dec_ref(v_inst_3476_);
                    v___x_3497_ = l_Lean_instInhabitedExpr;
                    v___x_3498_ = l_instInhabitedOfMonad___redArg(v_inst_3477_, v___x_3497_);
                    v___x_3499_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Expr_updateLetS_x21___redArg___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Expr_updateLetS_x21___redArg___closed__2_once
                        ),
                        _init_l_Lean_Expr_updateLetS_x21___redArg___closed__2,
                    );
                    v___x_3500_ = l_panic___redArg(v___x_3498_, v___x_3499_);
                    lean_dec(v___x_3498_);
                    return v___x_3500_;
                }
            }
            1 => {
                if v___y_3488_ == 0 {
                    lean_inc(v_declName_3482_);
                    lean_dec_ref_known(v_e_3478_, 4);
                    v___x_3489_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
                        v_inst_3476_,
                        v_inst_3477_,
                        v_declName_3482_,
                        v_newType_3479_,
                        v_newVal_3480_,
                        v_newBody_3481_,
                        v_nondep_3486_,
                    );
                    return v___x_3489_;
                } else {
                    v___x_3490_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_body_3485_,
                            v_newBody_3481_,
                        );
                    if v___x_3490_ == 0 {
                        lean_inc(v_declName_3482_);
                        lean_dec_ref_known(v_e_3478_, 4);
                        v___x_3491_ = l_Lean_Meta_Sym_Internal_mkLetS___redArg(
                            v_inst_3476_,
                            v_inst_3477_,
                            v_declName_3482_,
                            v_newType_3479_,
                            v_newVal_3480_,
                            v_newBody_3481_,
                            v_nondep_3486_,
                        );
                        return v___x_3491_;
                    } else {
                        lean_dec_ref(v_newBody_3481_);
                        lean_dec_ref(v_newVal_3480_);
                        lean_dec_ref(v_newType_3479_);
                        lean_dec_ref(v_inst_3476_);
                        v_toApplicative_3492_ = lean_ctor_get(v_inst_3477_, 0);
                        lean_inc_ref(v_toApplicative_3492_);
                        lean_dec_ref(v_inst_3477_);
                        v_toPure_3493_ = lean_ctor_get(v_toApplicative_3492_, 1);
                        lean_inc(v_toPure_3493_);
                        lean_dec_ref(v_toApplicative_3492_);
                        v___x_3494_ = lean_apply_2(v_toPure_3493_, lean_box(0), v_e_3478_);
                        return v___x_3494_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0(
    mut v_inst_3501_: *mut LeanObject,
    mut v_inst_3502_: *mut LeanObject,
    mut v_a_u2082_3503_: *mut LeanObject,
    mut v_____do__lift_3504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    v___x_3505_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3501_,
        v_inst_3502_,
        v_____do__lift_3504_,
        v_a_u2082_3503_,
    );
    return v___x_3505_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(
    mut v_inst_3506_: *mut LeanObject,
    mut v_inst_3507_: *mut LeanObject,
    mut v_f_3508_: *mut LeanObject,
    mut v_a_u2081_3509_: *mut LeanObject,
    mut v_a_u2082_3510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3511_ = lean_ctor_get(v_inst_3507_, 1);
    lean_inc(v_toBind_3511_);
    lean_inc_ref(v_inst_3507_);
    lean_inc_ref(v_inst_3506_);
    v___f_3512_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3512_, 0, v_inst_3506_);
    lean_closure_set(v___f_3512_, 1, v_inst_3507_);
    lean_closure_set(v___f_3512_, 2, v_a_u2082_3510_);
    v___x_3513_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3506_,
        v_inst_3507_,
        v_f_3508_,
        v_a_u2081_3509_,
    );
    v___x_3514_ = lean_apply_4(
        v_toBind_3511_,
        lean_box(0),
        lean_box(0),
        v___x_3513_,
        v___f_3512_,
    );
    return v___x_3514_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2082(
    mut v_m_3515_: *mut LeanObject,
    mut v_inst_3516_: *mut LeanObject,
    mut v_inst_3517_: *mut LeanObject,
    mut v_f_3518_: *mut LeanObject,
    mut v_a_u2081_3519_: *mut LeanObject,
    mut v_a_u2082_3520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    v___x_3521_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(
        v_inst_3516_,
        v_inst_3517_,
        v_f_3518_,
        v_a_u2081_3519_,
        v_a_u2082_3520_,
    );
    return v___x_3521_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0(
    mut v_inst_3522_: *mut LeanObject,
    mut v_inst_3523_: *mut LeanObject,
    mut v_a_u2083_3524_: *mut LeanObject,
    mut v_____do__lift_3525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    v___x_3526_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3522_,
        v_inst_3523_,
        v_____do__lift_3525_,
        v_a_u2083_3524_,
    );
    return v___x_3526_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(
    mut v_inst_3527_: *mut LeanObject,
    mut v_inst_3528_: *mut LeanObject,
    mut v_f_3529_: *mut LeanObject,
    mut v_a_u2081_3530_: *mut LeanObject,
    mut v_a_u2082_3531_: *mut LeanObject,
    mut v_a_u2083_3532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3533_ = lean_ctor_get(v_inst_3528_, 1);
    lean_inc(v_toBind_3533_);
    lean_inc_ref(v_inst_3528_);
    lean_inc_ref(v_inst_3527_);
    v___f_3534_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3534_, 0, v_inst_3527_);
    lean_closure_set(v___f_3534_, 1, v_inst_3528_);
    lean_closure_set(v___f_3534_, 2, v_a_u2083_3532_);
    v___x_3535_ = l_Lean_Meta_Sym_Internal_mkAppS_u2082___redArg(
        v_inst_3527_,
        v_inst_3528_,
        v_f_3529_,
        v_a_u2081_3530_,
        v_a_u2082_3531_,
    );
    v___x_3536_ = lean_apply_4(
        v_toBind_3533_,
        lean_box(0),
        lean_box(0),
        v___x_3535_,
        v___f_3534_,
    );
    return v___x_3536_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2083(
    mut v_m_3537_: *mut LeanObject,
    mut v_inst_3538_: *mut LeanObject,
    mut v_inst_3539_: *mut LeanObject,
    mut v_f_3540_: *mut LeanObject,
    mut v_a_u2081_3541_: *mut LeanObject,
    mut v_a_u2082_3542_: *mut LeanObject,
    mut v_a_u2083_3543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    v___x_3544_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(
        v_inst_3538_,
        v_inst_3539_,
        v_f_3540_,
        v_a_u2081_3541_,
        v_a_u2082_3542_,
        v_a_u2083_3543_,
    );
    return v___x_3544_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0(
    mut v_inst_3545_: *mut LeanObject,
    mut v_inst_3546_: *mut LeanObject,
    mut v_a_u2084_3547_: *mut LeanObject,
    mut v_____do__lift_3548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    v___x_3549_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3545_,
        v_inst_3546_,
        v_____do__lift_3548_,
        v_a_u2084_3547_,
    );
    return v___x_3549_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(
    mut v_inst_3550_: *mut LeanObject,
    mut v_inst_3551_: *mut LeanObject,
    mut v_f_3552_: *mut LeanObject,
    mut v_a_u2081_3553_: *mut LeanObject,
    mut v_a_u2082_3554_: *mut LeanObject,
    mut v_a_u2083_3555_: *mut LeanObject,
    mut v_a_u2084_3556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3557_ = lean_ctor_get(v_inst_3551_, 1);
    lean_inc(v_toBind_3557_);
    lean_inc_ref(v_inst_3551_);
    lean_inc_ref(v_inst_3550_);
    v___f_3558_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3558_, 0, v_inst_3550_);
    lean_closure_set(v___f_3558_, 1, v_inst_3551_);
    lean_closure_set(v___f_3558_, 2, v_a_u2084_3556_);
    v___x_3559_ = l_Lean_Meta_Sym_Internal_mkAppS_u2083___redArg(
        v_inst_3550_,
        v_inst_3551_,
        v_f_3552_,
        v_a_u2081_3553_,
        v_a_u2082_3554_,
        v_a_u2083_3555_,
    );
    v___x_3560_ = lean_apply_4(
        v_toBind_3557_,
        lean_box(0),
        lean_box(0),
        v___x_3559_,
        v___f_3558_,
    );
    return v___x_3560_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2084(
    mut v_m_3561_: *mut LeanObject,
    mut v_inst_3562_: *mut LeanObject,
    mut v_inst_3563_: *mut LeanObject,
    mut v_f_3564_: *mut LeanObject,
    mut v_a_u2081_3565_: *mut LeanObject,
    mut v_a_u2082_3566_: *mut LeanObject,
    mut v_a_u2083_3567_: *mut LeanObject,
    mut v_a_u2084_3568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    v___x_3569_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(
        v_inst_3562_,
        v_inst_3563_,
        v_f_3564_,
        v_a_u2081_3565_,
        v_a_u2082_3566_,
        v_a_u2083_3567_,
        v_a_u2084_3568_,
    );
    return v___x_3569_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0(
    mut v_inst_3570_: *mut LeanObject,
    mut v_inst_3571_: *mut LeanObject,
    mut v_a_u2085_3572_: *mut LeanObject,
    mut v_____do__lift_3573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    v___x_3574_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3570_,
        v_inst_3571_,
        v_____do__lift_3573_,
        v_a_u2085_3572_,
    );
    return v___x_3574_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(
    mut v_inst_3575_: *mut LeanObject,
    mut v_inst_3576_: *mut LeanObject,
    mut v_f_3577_: *mut LeanObject,
    mut v_a_u2081_3578_: *mut LeanObject,
    mut v_a_u2082_3579_: *mut LeanObject,
    mut v_a_u2083_3580_: *mut LeanObject,
    mut v_a_u2084_3581_: *mut LeanObject,
    mut v_a_u2085_3582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3583_ = lean_ctor_get(v_inst_3576_, 1);
    lean_inc(v_toBind_3583_);
    lean_inc_ref(v_inst_3576_);
    lean_inc_ref(v_inst_3575_);
    v___f_3584_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3584_, 0, v_inst_3575_);
    lean_closure_set(v___f_3584_, 1, v_inst_3576_);
    lean_closure_set(v___f_3584_, 2, v_a_u2085_3582_);
    v___x_3585_ = l_Lean_Meta_Sym_Internal_mkAppS_u2084___redArg(
        v_inst_3575_,
        v_inst_3576_,
        v_f_3577_,
        v_a_u2081_3578_,
        v_a_u2082_3579_,
        v_a_u2083_3580_,
        v_a_u2084_3581_,
    );
    v___x_3586_ = lean_apply_4(
        v_toBind_3583_,
        lean_box(0),
        lean_box(0),
        v___x_3585_,
        v___f_3584_,
    );
    return v___x_3586_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2085(
    mut v_m_3587_: *mut LeanObject,
    mut v_inst_3588_: *mut LeanObject,
    mut v_inst_3589_: *mut LeanObject,
    mut v_f_3590_: *mut LeanObject,
    mut v_a_u2081_3591_: *mut LeanObject,
    mut v_a_u2082_3592_: *mut LeanObject,
    mut v_a_u2083_3593_: *mut LeanObject,
    mut v_a_u2084_3594_: *mut LeanObject,
    mut v_a_u2085_3595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    v___x_3596_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(
        v_inst_3588_,
        v_inst_3589_,
        v_f_3590_,
        v_a_u2081_3591_,
        v_a_u2082_3592_,
        v_a_u2083_3593_,
        v_a_u2084_3594_,
        v_a_u2085_3595_,
    );
    return v___x_3596_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0(
    mut v_inst_3597_: *mut LeanObject,
    mut v_inst_3598_: *mut LeanObject,
    mut v_a_u2086_3599_: *mut LeanObject,
    mut v_____do__lift_3600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3601_: *mut LeanObject = core::ptr::null_mut();
    v___x_3601_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3597_,
        v_inst_3598_,
        v_____do__lift_3600_,
        v_a_u2086_3599_,
    );
    return v___x_3601_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(
    mut v_inst_3602_: *mut LeanObject,
    mut v_inst_3603_: *mut LeanObject,
    mut v_f_3604_: *mut LeanObject,
    mut v_a_u2081_3605_: *mut LeanObject,
    mut v_a_u2082_3606_: *mut LeanObject,
    mut v_a_u2083_3607_: *mut LeanObject,
    mut v_a_u2084_3608_: *mut LeanObject,
    mut v_a_u2085_3609_: *mut LeanObject,
    mut v_a_u2086_3610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3611_ = lean_ctor_get(v_inst_3603_, 1);
    lean_inc(v_toBind_3611_);
    lean_inc_ref(v_inst_3603_);
    lean_inc_ref(v_inst_3602_);
    v___f_3612_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3612_, 0, v_inst_3602_);
    lean_closure_set(v___f_3612_, 1, v_inst_3603_);
    lean_closure_set(v___f_3612_, 2, v_a_u2086_3610_);
    v___x_3613_ = l_Lean_Meta_Sym_Internal_mkAppS_u2085___redArg(
        v_inst_3602_,
        v_inst_3603_,
        v_f_3604_,
        v_a_u2081_3605_,
        v_a_u2082_3606_,
        v_a_u2083_3607_,
        v_a_u2084_3608_,
        v_a_u2085_3609_,
    );
    v___x_3614_ = lean_apply_4(
        v_toBind_3611_,
        lean_box(0),
        lean_box(0),
        v___x_3613_,
        v___f_3612_,
    );
    return v___x_3614_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2086(
    mut v_m_3615_: *mut LeanObject,
    mut v_inst_3616_: *mut LeanObject,
    mut v_inst_3617_: *mut LeanObject,
    mut v_f_3618_: *mut LeanObject,
    mut v_a_u2081_3619_: *mut LeanObject,
    mut v_a_u2082_3620_: *mut LeanObject,
    mut v_a_u2083_3621_: *mut LeanObject,
    mut v_a_u2084_3622_: *mut LeanObject,
    mut v_a_u2085_3623_: *mut LeanObject,
    mut v_a_u2086_3624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    v___x_3625_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(
        v_inst_3616_,
        v_inst_3617_,
        v_f_3618_,
        v_a_u2081_3619_,
        v_a_u2082_3620_,
        v_a_u2083_3621_,
        v_a_u2084_3622_,
        v_a_u2085_3623_,
        v_a_u2086_3624_,
    );
    return v___x_3625_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0(
    mut v_inst_3626_: *mut LeanObject,
    mut v_inst_3627_: *mut LeanObject,
    mut v_a_u2087_3628_: *mut LeanObject,
    mut v_____do__lift_3629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    v___x_3630_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3626_,
        v_inst_3627_,
        v_____do__lift_3629_,
        v_a_u2087_3628_,
    );
    return v___x_3630_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(
    mut v_inst_3631_: *mut LeanObject,
    mut v_inst_3632_: *mut LeanObject,
    mut v_f_3633_: *mut LeanObject,
    mut v_a_u2081_3634_: *mut LeanObject,
    mut v_a_u2082_3635_: *mut LeanObject,
    mut v_a_u2083_3636_: *mut LeanObject,
    mut v_a_u2084_3637_: *mut LeanObject,
    mut v_a_u2085_3638_: *mut LeanObject,
    mut v_a_u2086_3639_: *mut LeanObject,
    mut v_a_u2087_3640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3641_ = lean_ctor_get(v_inst_3632_, 1);
    lean_inc(v_toBind_3641_);
    lean_inc_ref(v_inst_3632_);
    lean_inc_ref(v_inst_3631_);
    v___f_3642_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3642_, 0, v_inst_3631_);
    lean_closure_set(v___f_3642_, 1, v_inst_3632_);
    lean_closure_set(v___f_3642_, 2, v_a_u2087_3640_);
    v___x_3643_ = l_Lean_Meta_Sym_Internal_mkAppS_u2086___redArg(
        v_inst_3631_,
        v_inst_3632_,
        v_f_3633_,
        v_a_u2081_3634_,
        v_a_u2082_3635_,
        v_a_u2083_3636_,
        v_a_u2084_3637_,
        v_a_u2085_3638_,
        v_a_u2086_3639_,
    );
    v___x_3644_ = lean_apply_4(
        v_toBind_3641_,
        lean_box(0),
        lean_box(0),
        v___x_3643_,
        v___f_3642_,
    );
    return v___x_3644_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2087(
    mut v_m_3645_: *mut LeanObject,
    mut v_inst_3646_: *mut LeanObject,
    mut v_inst_3647_: *mut LeanObject,
    mut v_f_3648_: *mut LeanObject,
    mut v_a_u2081_3649_: *mut LeanObject,
    mut v_a_u2082_3650_: *mut LeanObject,
    mut v_a_u2083_3651_: *mut LeanObject,
    mut v_a_u2084_3652_: *mut LeanObject,
    mut v_a_u2085_3653_: *mut LeanObject,
    mut v_a_u2086_3654_: *mut LeanObject,
    mut v_a_u2087_3655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    v___x_3656_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(
        v_inst_3646_,
        v_inst_3647_,
        v_f_3648_,
        v_a_u2081_3649_,
        v_a_u2082_3650_,
        v_a_u2083_3651_,
        v_a_u2084_3652_,
        v_a_u2085_3653_,
        v_a_u2086_3654_,
        v_a_u2087_3655_,
    );
    return v___x_3656_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0(
    mut v_inst_3657_: *mut LeanObject,
    mut v_inst_3658_: *mut LeanObject,
    mut v_a_u2088_3659_: *mut LeanObject,
    mut v_____do__lift_3660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    v___x_3661_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3657_,
        v_inst_3658_,
        v_____do__lift_3660_,
        v_a_u2088_3659_,
    );
    return v___x_3661_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(
    mut v_inst_3662_: *mut LeanObject,
    mut v_inst_3663_: *mut LeanObject,
    mut v_f_3664_: *mut LeanObject,
    mut v_a_u2081_3665_: *mut LeanObject,
    mut v_a_u2082_3666_: *mut LeanObject,
    mut v_a_u2083_3667_: *mut LeanObject,
    mut v_a_u2084_3668_: *mut LeanObject,
    mut v_a_u2085_3669_: *mut LeanObject,
    mut v_a_u2086_3670_: *mut LeanObject,
    mut v_a_u2087_3671_: *mut LeanObject,
    mut v_a_u2088_3672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3673_ = lean_ctor_get(v_inst_3663_, 1);
    lean_inc(v_toBind_3673_);
    lean_inc_ref(v_inst_3663_);
    lean_inc_ref(v_inst_3662_);
    v___f_3674_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3674_, 0, v_inst_3662_);
    lean_closure_set(v___f_3674_, 1, v_inst_3663_);
    lean_closure_set(v___f_3674_, 2, v_a_u2088_3672_);
    v___x_3675_ = l_Lean_Meta_Sym_Internal_mkAppS_u2087___redArg(
        v_inst_3662_,
        v_inst_3663_,
        v_f_3664_,
        v_a_u2081_3665_,
        v_a_u2082_3666_,
        v_a_u2083_3667_,
        v_a_u2084_3668_,
        v_a_u2085_3669_,
        v_a_u2086_3670_,
        v_a_u2087_3671_,
    );
    v___x_3676_ = lean_apply_4(
        v_toBind_3673_,
        lean_box(0),
        lean_box(0),
        v___x_3675_,
        v___f_3674_,
    );
    return v___x_3676_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2088(
    mut v_m_3677_: *mut LeanObject,
    mut v_inst_3678_: *mut LeanObject,
    mut v_inst_3679_: *mut LeanObject,
    mut v_f_3680_: *mut LeanObject,
    mut v_a_u2081_3681_: *mut LeanObject,
    mut v_a_u2082_3682_: *mut LeanObject,
    mut v_a_u2083_3683_: *mut LeanObject,
    mut v_a_u2084_3684_: *mut LeanObject,
    mut v_a_u2085_3685_: *mut LeanObject,
    mut v_a_u2086_3686_: *mut LeanObject,
    mut v_a_u2087_3687_: *mut LeanObject,
    mut v_a_u2088_3688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3689_: *mut LeanObject = core::ptr::null_mut();
    v___x_3689_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(
        v_inst_3678_,
        v_inst_3679_,
        v_f_3680_,
        v_a_u2081_3681_,
        v_a_u2082_3682_,
        v_a_u2083_3683_,
        v_a_u2084_3684_,
        v_a_u2085_3685_,
        v_a_u2086_3686_,
        v_a_u2087_3687_,
        v_a_u2088_3688_,
    );
    return v___x_3689_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0(
    mut v_inst_3690_: *mut LeanObject,
    mut v_inst_3691_: *mut LeanObject,
    mut v_a_u2089_3692_: *mut LeanObject,
    mut v_____do__lift_3693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3694_: *mut LeanObject = core::ptr::null_mut();
    v___x_3694_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3690_,
        v_inst_3691_,
        v_____do__lift_3693_,
        v_a_u2089_3692_,
    );
    return v___x_3694_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(
    mut v_inst_3695_: *mut LeanObject,
    mut v_inst_3696_: *mut LeanObject,
    mut v_f_3697_: *mut LeanObject,
    mut v_a_u2081_3698_: *mut LeanObject,
    mut v_a_u2082_3699_: *mut LeanObject,
    mut v_a_u2083_3700_: *mut LeanObject,
    mut v_a_u2084_3701_: *mut LeanObject,
    mut v_a_u2085_3702_: *mut LeanObject,
    mut v_a_u2086_3703_: *mut LeanObject,
    mut v_a_u2087_3704_: *mut LeanObject,
    mut v_a_u2088_3705_: *mut LeanObject,
    mut v_a_u2089_3706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3707_ = lean_ctor_get(v_inst_3696_, 1);
    lean_inc(v_toBind_3707_);
    lean_inc_ref(v_inst_3696_);
    lean_inc_ref(v_inst_3695_);
    v___f_3708_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3708_, 0, v_inst_3695_);
    lean_closure_set(v___f_3708_, 1, v_inst_3696_);
    lean_closure_set(v___f_3708_, 2, v_a_u2089_3706_);
    v___x_3709_ = l_Lean_Meta_Sym_Internal_mkAppS_u2088___redArg(
        v_inst_3695_,
        v_inst_3696_,
        v_f_3697_,
        v_a_u2081_3698_,
        v_a_u2082_3699_,
        v_a_u2083_3700_,
        v_a_u2084_3701_,
        v_a_u2085_3702_,
        v_a_u2086_3703_,
        v_a_u2087_3704_,
        v_a_u2088_3705_,
    );
    v___x_3710_ = lean_apply_4(
        v_toBind_3707_,
        lean_box(0),
        lean_box(0),
        v___x_3709_,
        v___f_3708_,
    );
    return v___x_3710_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2089(
    mut v_m_3711_: *mut LeanObject,
    mut v_inst_3712_: *mut LeanObject,
    mut v_inst_3713_: *mut LeanObject,
    mut v_f_3714_: *mut LeanObject,
    mut v_a_u2081_3715_: *mut LeanObject,
    mut v_a_u2082_3716_: *mut LeanObject,
    mut v_a_u2083_3717_: *mut LeanObject,
    mut v_a_u2084_3718_: *mut LeanObject,
    mut v_a_u2085_3719_: *mut LeanObject,
    mut v_a_u2086_3720_: *mut LeanObject,
    mut v_a_u2087_3721_: *mut LeanObject,
    mut v_a_u2088_3722_: *mut LeanObject,
    mut v_a_u2089_3723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    v___x_3724_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(
        v_inst_3712_,
        v_inst_3713_,
        v_f_3714_,
        v_a_u2081_3715_,
        v_a_u2082_3716_,
        v_a_u2083_3717_,
        v_a_u2084_3718_,
        v_a_u2085_3719_,
        v_a_u2086_3720_,
        v_a_u2087_3721_,
        v_a_u2088_3722_,
        v_a_u2089_3723_,
    );
    return v___x_3724_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0(
    mut v_inst_3725_: *mut LeanObject,
    mut v_inst_3726_: *mut LeanObject,
    mut v_a_u2081_u2080_3727_: *mut LeanObject,
    mut v_____do__lift_3728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3725_,
        v_inst_3726_,
        v_____do__lift_3728_,
        v_a_u2081_u2080_3727_,
    );
    return v___x_3729_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(
    mut v_inst_3730_: *mut LeanObject,
    mut v_inst_3731_: *mut LeanObject,
    mut v_f_3732_: *mut LeanObject,
    mut v_a_u2081_3733_: *mut LeanObject,
    mut v_a_u2082_3734_: *mut LeanObject,
    mut v_a_u2083_3735_: *mut LeanObject,
    mut v_a_u2084_3736_: *mut LeanObject,
    mut v_a_u2085_3737_: *mut LeanObject,
    mut v_a_u2086_3738_: *mut LeanObject,
    mut v_a_u2087_3739_: *mut LeanObject,
    mut v_a_u2088_3740_: *mut LeanObject,
    mut v_a_u2089_3741_: *mut LeanObject,
    mut v_a_u2081_u2080_3742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3743_ = lean_ctor_get(v_inst_3731_, 1);
    lean_inc(v_toBind_3743_);
    lean_inc_ref(v_inst_3731_);
    lean_inc_ref(v_inst_3730_);
    v___f_3744_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3744_, 0, v_inst_3730_);
    lean_closure_set(v___f_3744_, 1, v_inst_3731_);
    lean_closure_set(v___f_3744_, 2, v_a_u2081_u2080_3742_);
    v___x_3745_ = l_Lean_Meta_Sym_Internal_mkAppS_u2089___redArg(
        v_inst_3730_,
        v_inst_3731_,
        v_f_3732_,
        v_a_u2081_3733_,
        v_a_u2082_3734_,
        v_a_u2083_3735_,
        v_a_u2084_3736_,
        v_a_u2085_3737_,
        v_a_u2086_3738_,
        v_a_u2087_3739_,
        v_a_u2088_3740_,
        v_a_u2089_3741_,
    );
    v___x_3746_ = lean_apply_4(
        v_toBind_3743_,
        lean_box(0),
        lean_box(0),
        v___x_3745_,
        v___f_3744_,
    );
    return v___x_3746_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080(
    mut v_m_3747_: *mut LeanObject,
    mut v_inst_3748_: *mut LeanObject,
    mut v_inst_3749_: *mut LeanObject,
    mut v_f_3750_: *mut LeanObject,
    mut v_a_u2081_3751_: *mut LeanObject,
    mut v_a_u2082_3752_: *mut LeanObject,
    mut v_a_u2083_3753_: *mut LeanObject,
    mut v_a_u2084_3754_: *mut LeanObject,
    mut v_a_u2085_3755_: *mut LeanObject,
    mut v_a_u2086_3756_: *mut LeanObject,
    mut v_a_u2087_3757_: *mut LeanObject,
    mut v_a_u2088_3758_: *mut LeanObject,
    mut v_a_u2089_3759_: *mut LeanObject,
    mut v_a_u2081_u2080_3760_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    v___x_3761_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(
        v_inst_3748_,
        v_inst_3749_,
        v_f_3750_,
        v_a_u2081_3751_,
        v_a_u2082_3752_,
        v_a_u2083_3753_,
        v_a_u2084_3754_,
        v_a_u2085_3755_,
        v_a_u2086_3756_,
        v_a_u2087_3757_,
        v_a_u2088_3758_,
        v_a_u2089_3759_,
        v_a_u2081_u2080_3760_,
    );
    return v___x_3761_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0(
    mut v_inst_3762_: *mut LeanObject,
    mut v_inst_3763_: *mut LeanObject,
    mut v_a_u2081_u2081_3764_: *mut LeanObject,
    mut v_____do__lift_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    v___x_3766_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
        v_inst_3762_,
        v_inst_3763_,
        v_____do__lift_3765_,
        v_a_u2081_u2081_3764_,
    );
    return v___x_3766_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(
    mut v_inst_3767_: *mut LeanObject,
    mut v_inst_3768_: *mut LeanObject,
    mut v_f_3769_: *mut LeanObject,
    mut v_a_u2081_3770_: *mut LeanObject,
    mut v_a_u2082_3771_: *mut LeanObject,
    mut v_a_u2083_3772_: *mut LeanObject,
    mut v_a_u2084_3773_: *mut LeanObject,
    mut v_a_u2085_3774_: *mut LeanObject,
    mut v_a_u2086_3775_: *mut LeanObject,
    mut v_a_u2087_3776_: *mut LeanObject,
    mut v_a_u2088_3777_: *mut LeanObject,
    mut v_a_u2089_3778_: *mut LeanObject,
    mut v_a_u2081_u2080_3779_: *mut LeanObject,
    mut v_a_u2081_u2081_3780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_3781_ = lean_ctor_get(v_inst_3768_, 1);
    lean_inc(v_toBind_3781_);
    lean_inc_ref(v_inst_3768_);
    lean_inc_ref(v_inst_3767_);
    v___f_3782_ = lean_alloc_closure(
        l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3782_, 0, v_inst_3767_);
    lean_closure_set(v___f_3782_, 1, v_inst_3768_);
    lean_closure_set(v___f_3782_, 2, v_a_u2081_u2081_3780_);
    v___x_3783_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2080___redArg(
        v_inst_3767_,
        v_inst_3768_,
        v_f_3769_,
        v_a_u2081_3770_,
        v_a_u2082_3771_,
        v_a_u2083_3772_,
        v_a_u2084_3773_,
        v_a_u2085_3774_,
        v_a_u2086_3775_,
        v_a_u2087_3776_,
        v_a_u2088_3777_,
        v_a_u2089_3778_,
        v_a_u2081_u2080_3779_,
    );
    v___x_3784_ = lean_apply_4(
        v_toBind_3781_,
        lean_box(0),
        lean_box(0),
        v___x_3783_,
        v___f_3782_,
    );
    return v___x_3784_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081(
    mut v_m_3785_: *mut LeanObject,
    mut v_inst_3786_: *mut LeanObject,
    mut v_inst_3787_: *mut LeanObject,
    mut v_f_3788_: *mut LeanObject,
    mut v_a_u2081_3789_: *mut LeanObject,
    mut v_a_u2082_3790_: *mut LeanObject,
    mut v_a_u2083_3791_: *mut LeanObject,
    mut v_a_u2084_3792_: *mut LeanObject,
    mut v_a_u2085_3793_: *mut LeanObject,
    mut v_a_u2086_3794_: *mut LeanObject,
    mut v_a_u2087_3795_: *mut LeanObject,
    mut v_a_u2088_3796_: *mut LeanObject,
    mut v_a_u2089_3797_: *mut LeanObject,
    mut v_a_u2081_u2080_3798_: *mut LeanObject,
    mut v_a_u2081_u2081_3799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    v___x_3800_ = l_Lean_Meta_Sym_Internal_mkAppS_u2081_u2081___redArg(
        v_inst_3786_,
        v_inst_3787_,
        v_f_3788_,
        v_a_u2081_3789_,
        v_a_u2082_3790_,
        v_a_u2083_3791_,
        v_a_u2084_3792_,
        v_a_u2085_3793_,
        v_a_u2086_3794_,
        v_a_u2087_3795_,
        v_a_u2088_3796_,
        v_a_u2089_3797_,
        v_a_u2081_u2080_3798_,
        v_a_u2081_u2081_3799_,
    );
    return v___x_3800_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed(
    mut v_i_3801_: *mut LeanObject,
    mut v_inst_3802_: *mut LeanObject,
    mut v_inst_3803_: *mut LeanObject,
    mut v_args_3804_: *mut LeanObject,
    mut v_endIdx_3805_: *mut LeanObject,
    mut v_____do__lift_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3807_: *mut LeanObject = core::ptr::null_mut();
    v_res_3807_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(v_i_3801_, v_inst_3802_, v_inst_3803_, v_args_3804_, v_endIdx_3805_, v_____do__lift_3806_);
    lean_dec(v_i_3801_);
    return v_res_3807_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(
    mut v_inst_3808_: *mut LeanObject,
    mut v_inst_3809_: *mut LeanObject,
    mut v_args_3810_: *mut LeanObject,
    mut v_endIdx_3811_: *mut LeanObject,
    mut v_b_3812_: *mut LeanObject,
    mut v_i_3813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3814_: u8 = 0;
    v___x_3814_ = lean_nat_dec_le(v_endIdx_3811_, v_i_3813_);
    if v___x_3814_ == 0 {
        let mut v_toBind_3815_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3816_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_3815_ = lean_ctor_get(v_inst_3809_, 1);
        lean_inc(v_toBind_3815_);
        lean_inc_ref(v_args_3810_);
        lean_inc_ref(v_inst_3809_);
        lean_inc_ref(v_inst_3808_);
        lean_inc(v_i_3813_);
        v___f_3816_ = lean_alloc_closure(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
        lean_closure_set(v___f_3816_, 0, v_i_3813_);
        lean_closure_set(v___f_3816_, 1, v_inst_3808_);
        lean_closure_set(v___f_3816_, 2, v_inst_3809_);
        lean_closure_set(v___f_3816_, 3, v_args_3810_);
        lean_closure_set(v___f_3816_, 4, v_endIdx_3811_);
        v___x_3817_ = l_Lean_instInhabitedExpr;
        v___x_3818_ = lean_array_get(v___x_3817_, v_args_3810_, v_i_3813_);
        lean_dec(v_i_3813_);
        lean_dec_ref(v_args_3810_);
        v___x_3819_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
            v_inst_3808_,
            v_inst_3809_,
            v_b_3812_,
            v___x_3818_,
        );
        v___x_3820_ = lean_apply_4(
            v_toBind_3815_,
            lean_box(0),
            lean_box(0),
            v___x_3819_,
            v___f_3816_,
        );
        return v___x_3820_;
    } else {
        let mut v_toApplicative_3821_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_3822_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_3813_);
        lean_dec(v_endIdx_3811_);
        lean_dec_ref(v_args_3810_);
        lean_dec_ref(v_inst_3808_);
        v_toApplicative_3821_ = lean_ctor_get(v_inst_3809_, 0);
        lean_inc_ref(v_toApplicative_3821_);
        lean_dec_ref(v_inst_3809_);
        v_toPure_3822_ = lean_ctor_get(v_toApplicative_3821_, 1);
        lean_inc(v_toPure_3822_);
        lean_dec_ref(v_toApplicative_3821_);
        v___x_3823_ = lean_apply_2(v_toPure_3822_, lean_box(0), v_b_3812_);
        return v___x_3823_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg___lam__0(
    mut v_i_3824_: *mut LeanObject,
    mut v_inst_3825_: *mut LeanObject,
    mut v_inst_3826_: *mut LeanObject,
    mut v_args_3827_: *mut LeanObject,
    mut v_endIdx_3828_: *mut LeanObject,
    mut v_____do__lift_3829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    v___x_3830_ = lean_unsigned_to_nat(1);
    v___x_3831_ = lean_nat_add(v_i_3824_, v___x_3830_);
    v___x_3832_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_3825_, v_inst_3826_, v_args_3827_, v_endIdx_3828_, v_____do__lift_3829_, v___x_3831_);
    return v___x_3832_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go(
    mut v_m_3833_: *mut LeanObject,
    mut v_inst_3834_: *mut LeanObject,
    mut v_inst_3835_: *mut LeanObject,
    mut v_args_3836_: *mut LeanObject,
    mut v_endIdx_3837_: *mut LeanObject,
    mut v_b_3838_: *mut LeanObject,
    mut v_i_3839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    v___x_3840_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_3834_, v_inst_3835_, v_args_3836_, v_endIdx_3837_, v_b_3838_, v_i_3839_);
    return v___x_3840_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRangeS___redArg(
    mut v_inst_3841_: *mut LeanObject,
    mut v_inst_3842_: *mut LeanObject,
    mut v_f_3843_: *mut LeanObject,
    mut v_beginIdx_3844_: *mut LeanObject,
    mut v_endIdx_3845_: *mut LeanObject,
    mut v_args_3846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    v___x_3847_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_3841_, v_inst_3842_, v_args_3846_, v_endIdx_3845_, v_f_3843_, v_beginIdx_3844_);
    return v___x_3847_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRangeS(
    mut v_m_3848_: *mut LeanObject,
    mut v_inst_3849_: *mut LeanObject,
    mut v_inst_3850_: *mut LeanObject,
    mut v_f_3851_: *mut LeanObject,
    mut v_beginIdx_3852_: *mut LeanObject,
    mut v_endIdx_3853_: *mut LeanObject,
    mut v_args_3854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    v___x_3855_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_3849_, v_inst_3850_, v_args_3854_, v_endIdx_3853_, v_f_3851_, v_beginIdx_3852_);
    return v___x_3855_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppNS___redArg(
    mut v_inst_3856_: *mut LeanObject,
    mut v_inst_3857_: *mut LeanObject,
    mut v_f_3858_: *mut LeanObject,
    mut v_args_3859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    v___x_3860_ = lean_unsigned_to_nat(0);
    v___x_3861_ = lean_array_get_size(v_args_3859_);
    v___x_3862_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRangeS_go___redArg(v_inst_3856_, v_inst_3857_, v_args_3859_, v___x_3861_, v_f_3858_, v___x_3860_);
    return v___x_3862_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppNS(
    mut v_m_3863_: *mut LeanObject,
    mut v_inst_3864_: *mut LeanObject,
    mut v_inst_3865_: *mut LeanObject,
    mut v_f_3866_: *mut LeanObject,
    mut v_args_3867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    v___x_3868_ = l_Lean_Meta_Sym_Internal_mkAppNS___redArg(
        v_inst_3864_,
        v_inst_3865_,
        v_f_3866_,
        v_args_3867_,
    );
    return v___x_3868_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed(
    mut v_inst_3869_: *mut LeanObject,
    mut v_inst_3870_: *mut LeanObject,
    mut v_revArgs_3871_: *mut LeanObject,
    mut v_start_3872_: *mut LeanObject,
    mut v_i_3873_: *mut LeanObject,
    mut v_____do__lift_3874_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3875_: *mut LeanObject = core::ptr::null_mut();
    v_res_3875_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(v_inst_3869_, v_inst_3870_, v_revArgs_3871_, v_start_3872_, v_i_3873_, v_____do__lift_3874_);
    lean_dec(v_i_3873_);
    return v_res_3875_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(
    mut v_inst_3876_: *mut LeanObject,
    mut v_inst_3877_: *mut LeanObject,
    mut v_revArgs_3878_: *mut LeanObject,
    mut v_start_3879_: *mut LeanObject,
    mut v_b_3880_: *mut LeanObject,
    mut v_i_3881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3882_: u8 = 0;
    v___x_3882_ = lean_nat_dec_le(v_i_3881_, v_start_3879_);
    if v___x_3882_ == 0 {
        let mut v_toBind_3883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
        let mut v_i_3885_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3886_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_3883_ = lean_ctor_get(v_inst_3877_, 1);
        lean_inc(v_toBind_3883_);
        v___x_3884_ = lean_unsigned_to_nat(1);
        v_i_3885_ = lean_nat_sub(v_i_3881_, v___x_3884_);
        lean_inc(v_i_3885_);
        lean_inc_ref(v_revArgs_3878_);
        lean_inc_ref(v_inst_3877_);
        lean_inc_ref(v_inst_3876_);
        v___f_3886_ = lean_alloc_closure(l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0___boxed as *mut core::ffi::c_void, 6, 5);
        lean_closure_set(v___f_3886_, 0, v_inst_3876_);
        lean_closure_set(v___f_3886_, 1, v_inst_3877_);
        lean_closure_set(v___f_3886_, 2, v_revArgs_3878_);
        lean_closure_set(v___f_3886_, 3, v_start_3879_);
        lean_closure_set(v___f_3886_, 4, v_i_3885_);
        v___x_3887_ = l_Lean_instInhabitedExpr;
        v___x_3888_ = lean_array_get(v___x_3887_, v_revArgs_3878_, v_i_3885_);
        lean_dec(v_i_3885_);
        lean_dec_ref(v_revArgs_3878_);
        v___x_3889_ = l_Lean_Meta_Sym_Internal_mkAppS___redArg(
            v_inst_3876_,
            v_inst_3877_,
            v_b_3880_,
            v___x_3888_,
        );
        v___x_3890_ = lean_apply_4(
            v_toBind_3883_,
            lean_box(0),
            lean_box(0),
            v___x_3889_,
            v___f_3886_,
        );
        return v___x_3890_;
    } else {
        let mut v_toApplicative_3891_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_3892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_start_3879_);
        lean_dec_ref(v_revArgs_3878_);
        lean_dec_ref(v_inst_3876_);
        v_toApplicative_3891_ = lean_ctor_get(v_inst_3877_, 0);
        lean_inc_ref(v_toApplicative_3891_);
        lean_dec_ref(v_inst_3877_);
        v_toPure_3892_ = lean_ctor_get(v_toApplicative_3891_, 1);
        lean_inc(v_toPure_3892_);
        lean_dec_ref(v_toApplicative_3891_);
        v___x_3893_ = lean_apply_2(v_toPure_3892_, lean_box(0), v_b_3880_);
        return v___x_3893_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___lam__0(
    mut v_inst_3894_: *mut LeanObject,
    mut v_inst_3895_: *mut LeanObject,
    mut v_revArgs_3896_: *mut LeanObject,
    mut v_start_3897_: *mut LeanObject,
    mut v_i_3898_: *mut LeanObject,
    mut v_____do__lift_3899_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    v___x_3900_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_3894_, v_inst_3895_, v_revArgs_3896_, v_start_3897_, v_____do__lift_3899_, v_i_3898_);
    return v___x_3900_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg___boxed(
    mut v_inst_3901_: *mut LeanObject,
    mut v_inst_3902_: *mut LeanObject,
    mut v_revArgs_3903_: *mut LeanObject,
    mut v_start_3904_: *mut LeanObject,
    mut v_b_3905_: *mut LeanObject,
    mut v_i_3906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3907_: *mut LeanObject = core::ptr::null_mut();
    v_res_3907_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_3901_, v_inst_3902_, v_revArgs_3903_, v_start_3904_, v_b_3905_, v_i_3906_);
    lean_dec(v_i_3906_);
    return v_res_3907_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(
    mut v_m_3908_: *mut LeanObject,
    mut v_inst_3909_: *mut LeanObject,
    mut v_inst_3910_: *mut LeanObject,
    mut v_revArgs_3911_: *mut LeanObject,
    mut v_start_3912_: *mut LeanObject,
    mut v_b_3913_: *mut LeanObject,
    mut v_i_3914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    v___x_3915_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_3909_, v_inst_3910_, v_revArgs_3911_, v_start_3912_, v_b_3913_, v_i_3914_);
    return v___x_3915_;
}
pub unsafe fn l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___boxed(
    mut v_m_3916_: *mut LeanObject,
    mut v_inst_3917_: *mut LeanObject,
    mut v_inst_3918_: *mut LeanObject,
    mut v_revArgs_3919_: *mut LeanObject,
    mut v_start_3920_: *mut LeanObject,
    mut v_b_3921_: *mut LeanObject,
    mut v_i_3922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3923_: *mut LeanObject = core::ptr::null_mut();
    v_res_3923_ =
        l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go(
            v_m_3916_,
            v_inst_3917_,
            v_inst_3918_,
            v_revArgs_3919_,
            v_start_3920_,
            v_b_3921_,
            v_i_3922_,
        );
    lean_dec(v_i_3922_);
    return v_res_3923_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(
    mut v_inst_3924_: *mut LeanObject,
    mut v_inst_3925_: *mut LeanObject,
    mut v_f_3926_: *mut LeanObject,
    mut v_beginIdx_3927_: *mut LeanObject,
    mut v_endIdx_3928_: *mut LeanObject,
    mut v_revArgs_3929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    v___x_3930_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_3924_, v_inst_3925_, v_revArgs_3929_, v_beginIdx_3927_, v_f_3926_, v_endIdx_3928_);
    return v___x_3930_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg___boxed(
    mut v_inst_3931_: *mut LeanObject,
    mut v_inst_3932_: *mut LeanObject,
    mut v_f_3933_: *mut LeanObject,
    mut v_beginIdx_3934_: *mut LeanObject,
    mut v_endIdx_3935_: *mut LeanObject,
    mut v_revArgs_3936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3937_: *mut LeanObject = core::ptr::null_mut();
    v_res_3937_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS___redArg(
        v_inst_3931_,
        v_inst_3932_,
        v_f_3933_,
        v_beginIdx_3934_,
        v_endIdx_3935_,
        v_revArgs_3936_,
    );
    lean_dec(v_endIdx_3935_);
    return v_res_3937_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevRangeS(
    mut v_m_3938_: *mut LeanObject,
    mut v_inst_3939_: *mut LeanObject,
    mut v_inst_3940_: *mut LeanObject,
    mut v_f_3941_: *mut LeanObject,
    mut v_beginIdx_3942_: *mut LeanObject,
    mut v_endIdx_3943_: *mut LeanObject,
    mut v_revArgs_3944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    v___x_3945_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_3939_, v_inst_3940_, v_revArgs_3944_, v_beginIdx_3942_, v_f_3941_, v_endIdx_3943_);
    return v___x_3945_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevRangeS___boxed(
    mut v_m_3946_: *mut LeanObject,
    mut v_inst_3947_: *mut LeanObject,
    mut v_inst_3948_: *mut LeanObject,
    mut v_f_3949_: *mut LeanObject,
    mut v_beginIdx_3950_: *mut LeanObject,
    mut v_endIdx_3951_: *mut LeanObject,
    mut v_revArgs_3952_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3953_: *mut LeanObject = core::ptr::null_mut();
    v_res_3953_ = l_Lean_Meta_Sym_Internal_mkAppRevRangeS(
        v_m_3946_,
        v_inst_3947_,
        v_inst_3948_,
        v_f_3949_,
        v_beginIdx_3950_,
        v_endIdx_3951_,
        v_revArgs_3952_,
    );
    lean_dec(v_endIdx_3951_);
    return v_res_3953_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(
    mut v_inst_3954_: *mut LeanObject,
    mut v_inst_3955_: *mut LeanObject,
    mut v_f_3956_: *mut LeanObject,
    mut v_revArgs_3957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    v___x_3958_ = lean_unsigned_to_nat(0);
    v___x_3959_ = lean_array_get_size(v_revArgs_3957_);
    v___x_3960_ = l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_mkAppRevRangeS_go___redArg(v_inst_3954_, v_inst_3955_, v_revArgs_3957_, v___x_3958_, v_f_3956_, v___x_3959_);
    return v___x_3960_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppRevS(
    mut v_m_3961_: *mut LeanObject,
    mut v_inst_3962_: *mut LeanObject,
    mut v_inst_3963_: *mut LeanObject,
    mut v_f_3964_: *mut LeanObject,
    mut v_revArgs_3965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    v___x_3966_ = l_Lean_Meta_Sym_Internal_mkAppRevS___redArg(
        v_inst_3962_,
        v_inst_3963_,
        v_f_3964_,
        v_revArgs_3965_,
    );
    return v___x_3966_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy =
        _init_l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy();
    lean_mark_persistent(
        l___private_Lean_Meta_Sym_AlphaShareBuilder_0__Lean_Meta_Sym_Internal_dummy,
    );
    l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM =
        _init_l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM();
    lean_mark_persistent(l_Lean_Meta_Sym_Internal_instMonadShareCommonAlphaShareBuilderM);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
}
