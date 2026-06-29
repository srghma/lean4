// Lean compiler output
// Module: Lean.Elab.DeclUtil
// Imports: Lean.Meta.Check Lean.Parser.Command
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fswap, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_array_uget_borrowed, lean_expr_instantiate1,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_shiftr,
    lean_nat_sub, lean_st_ref_get, lean_string_append, lean_usize_add, lean_usize_dec_eq,
    lean_usize_of_nat, lean_whnf,
};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::{l_Lean_Syntax_isNone, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{l_Lean_Name_hasMacroScopes, l_Lean_Syntax_getArg};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_lt;
use crate::r#gen::Lean::Expr::{l_Lean_BinderInfo_isInstImplicit, l_Lean_instBEqBinderInfo_beq};
use crate::r#gen::Lean::Message::{l_Lean_MessageData_ofSyntax, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::Check::{
    initialize_Lean_Meta_Check, l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg,
    runtime_initialize_Lean_Meta_Check,
};
use crate::r#gen::Lean::Parser::Command::{
    initialize_Lean_Parser_Command, runtime_initialize_Lean_Parser_Command,
};
pub static l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0_value:
    crate::leanh::LeanStringObject<81> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 81,
    m_capacity: 81,
    m_length: 80,
    m_data: [
        73, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114, 114, 111, 114, 58, 32, 77, 105, 115,
        109, 97, 116, 99, 104, 101, 100, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112,
        97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 119, 104, 101, 110, 32, 99, 104, 101, 99,
        107, 105, 110, 103, 32, 116, 121, 112, 101, 32, 99, 111, 109, 112, 97, 116, 105, 98, 105,
        108, 105, 116, 121, 0,
    ],
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [80, 97, 114, 97, 109, 101, 116, 101, 114, 32, 96, 0],
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [96, 32, 0],
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        80, 97, 114, 97, 109, 101, 116, 101, 114, 32, 110, 97, 109, 101, 115, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [96, 32, 97, 110, 100, 32, 96, 0],
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11_value:
    crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        96, 32, 100, 105, 102, 102, 101, 114, 32, 98, 117, 116, 32, 119, 101, 114, 101, 32, 101,
        120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 32, 109, 97, 116, 99, 104, 0,
    ],
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        66, 105, 110, 100, 101, 114, 32, 97, 110, 110, 111, 116, 97, 116, 105, 111, 110, 115, 32,
        102, 111, 114, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [96, 32, 109, 117, 115, 116, 32, 109, 97, 116, 99, 104, 0],
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_sortDeclLevelParams___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_sortDeclLevelParams___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_sortDeclLevelParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_sortDeclLevelParams___closed__1_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            117, 110, 117, 115, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115, 101, 32, 112, 97,
            114, 97, 109, 101, 116, 101, 114, 32, 39, 0,
        ],
    };
static mut l_Lean_Elab_sortDeclLevelParams___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_sortDeclLevelParams___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_sortDeclLevelParams___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [39, 0],
    };
static mut l_Lean_Elab_sortDeclLevelParams___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_sortDeclLevelParams___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0(
    mut v_k_756_: *mut crate::leanh::LeanObject,
    mut v_b_757_: *mut crate::leanh::LeanObject,
    mut v___y_758_: *mut crate::leanh::LeanObject,
    mut v___y_759_: *mut crate::leanh::LeanObject,
    mut v___y_760_: *mut crate::leanh::LeanObject,
    mut v___y_761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_761_);
    crate::leanh::lean_inc_ref(v___y_760_);
    crate::leanh::lean_inc(v___y_759_);
    crate::leanh::lean_inc_ref(v___y_758_);
    v___x_763_ = crate::leanh::lean_apply_6(
        v_k_756_,
        v_b_757_,
        v___y_758_,
        v___y_759_,
        v___y_760_,
        v___y_761_,
        crate::leanh::lean_box(0),
    );
    return v___x_763_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0___boxed(
    mut v_k_764_: *mut crate::leanh::LeanObject,
    mut v_b_765_: *mut crate::leanh::LeanObject,
    mut v___y_766_: *mut crate::leanh::LeanObject,
    mut v___y_767_: *mut crate::leanh::LeanObject,
    mut v___y_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
    mut v___y_770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_771_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0(v_k_764_, v_b_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
    crate::leanh::lean_dec(v___y_769_);
    crate::leanh::lean_dec_ref(v___y_768_);
    crate::leanh::lean_dec(v___y_767_);
    crate::leanh::lean_dec_ref(v___y_766_);
    return v_res_771_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(
    mut v_name_772_: *mut crate::leanh::LeanObject,
    mut v_bi_773_: u8,
    mut v_type_774_: *mut crate::leanh::LeanObject,
    mut v_k_775_: *mut crate::leanh::LeanObject,
    mut v_kind_776_: u8,
    mut v___y_777_: *mut crate::leanh::LeanObject,
    mut v___y_778_: *mut crate::leanh::LeanObject,
    mut v___y_779_: *mut crate::leanh::LeanObject,
    mut v___y_780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_791_: u8 = 0;
    let mut v_a_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_795_: u8 = 0;
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_782_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_782_, 0, v_k_775_);
                v___x_783_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_772_,
                    v_bi_773_,
                    v_type_774_,
                    v___f_782_,
                    v_kind_776_,
                    v___y_777_,
                    v___y_778_,
                    v___y_779_,
                    v___y_780_,
                );
                if crate::leanh::lean_obj_tag(v___x_783_) == 0 {
                    v_a_784_ = crate::leanh::lean_ctor_get(v___x_783_, 0);
                    v_isSharedCheck_791_ = (!crate::leanh::lean_is_exclusive(v___x_783_)) as u8;
                    if v_isSharedCheck_791_ == 0 {
                        v___x_786_ = v___x_783_;
                        v_isShared_787_ = v_isSharedCheck_791_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_784_);
                        crate::leanh::lean_dec(v___x_783_);
                        v___x_786_ = crate::leanh::lean_box(0);
                        v_isShared_787_ = v_isSharedCheck_791_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_792_ = crate::leanh::lean_ctor_get(v___x_783_, 0);
                    v_isSharedCheck_799_ = (!crate::leanh::lean_is_exclusive(v___x_783_)) as u8;
                    if v_isSharedCheck_799_ == 0 {
                        v___x_794_ = v___x_783_;
                        v_isShared_795_ = v_isSharedCheck_799_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_792_);
                        crate::leanh::lean_dec(v___x_783_);
                        v___x_794_ = crate::leanh::lean_box(0);
                        v_isShared_795_ = v_isSharedCheck_799_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_787_ == 0 {
                    v___x_789_ = v___x_786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_790_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
                    v___x_789_ = v_reuseFailAlloc_790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_789_;
            }
            3 => {
                if v_isShared_795_ == 0 {
                    v___x_797_ = v___x_794_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
                    v___x_797_ = v_reuseFailAlloc_798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg___boxed(
    mut v_name_800_: *mut crate::leanh::LeanObject,
    mut v_bi_801_: *mut crate::leanh::LeanObject,
    mut v_type_802_: *mut crate::leanh::LeanObject,
    mut v_k_803_: *mut crate::leanh::LeanObject,
    mut v_kind_804_: *mut crate::leanh::LeanObject,
    mut v___y_805_: *mut crate::leanh::LeanObject,
    mut v___y_806_: *mut crate::leanh::LeanObject,
    mut v___y_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_810_: u8 = 0;
    let mut v_kind_boxed_811_: u8 = 0;
    let mut v_res_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_810_ = (crate::leanh::lean_unbox(v_bi_801_) as u8);
    v_kind_boxed_811_ = (crate::leanh::lean_unbox(v_kind_804_) as u8);
    v_res_812_ =
        l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(
            v_name_800_,
            v_bi_boxed_810_,
            v_type_802_,
            v_k_803_,
            v_kind_boxed_811_,
            v___y_805_,
            v___y_806_,
            v___y_807_,
            v___y_808_,
        );
    crate::leanh::lean_dec(v___y_808_);
    crate::leanh::lean_dec_ref(v___y_807_);
    crate::leanh::lean_dec(v___y_806_);
    crate::leanh::lean_dec_ref(v___y_805_);
    return v_res_812_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1(
    mut v_00_u03b1_813_: *mut crate::leanh::LeanObject,
    mut v_name_814_: *mut crate::leanh::LeanObject,
    mut v_bi_815_: u8,
    mut v_type_816_: *mut crate::leanh::LeanObject,
    mut v_k_817_: *mut crate::leanh::LeanObject,
    mut v_kind_818_: u8,
    mut v___y_819_: *mut crate::leanh::LeanObject,
    mut v___y_820_: *mut crate::leanh::LeanObject,
    mut v___y_821_: *mut crate::leanh::LeanObject,
    mut v___y_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_824_ =
        l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(
            v_name_814_,
            v_bi_815_,
            v_type_816_,
            v_k_817_,
            v_kind_818_,
            v___y_819_,
            v___y_820_,
            v___y_821_,
            v___y_822_,
        );
    return v___x_824_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___boxed(
    mut v_00_u03b1_825_: *mut crate::leanh::LeanObject,
    mut v_name_826_: *mut crate::leanh::LeanObject,
    mut v_bi_827_: *mut crate::leanh::LeanObject,
    mut v_type_828_: *mut crate::leanh::LeanObject,
    mut v_k_829_: *mut crate::leanh::LeanObject,
    mut v_kind_830_: *mut crate::leanh::LeanObject,
    mut v___y_831_: *mut crate::leanh::LeanObject,
    mut v___y_832_: *mut crate::leanh::LeanObject,
    mut v___y_833_: *mut crate::leanh::LeanObject,
    mut v___y_834_: *mut crate::leanh::LeanObject,
    mut v___y_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_836_: u8 = 0;
    let mut v_kind_boxed_837_: u8 = 0;
    let mut v_res_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_836_ = (crate::leanh::lean_unbox(v_bi_827_) as u8);
    v_kind_boxed_837_ = (crate::leanh::lean_unbox(v_kind_830_) as u8);
    v_res_838_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1(
        v_00_u03b1_825_,
        v_name_826_,
        v_bi_boxed_836_,
        v_type_828_,
        v_k_829_,
        v_kind_boxed_837_,
        v___y_831_,
        v___y_832_,
        v___y_833_,
        v___y_834_,
    );
    crate::leanh::lean_dec(v___y_834_);
    crate::leanh::lean_dec_ref(v___y_833_);
    crate::leanh::lean_dec(v___y_832_);
    crate::leanh::lean_dec_ref(v___y_831_);
    return v_res_838_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(
    mut v_msgData_839_: *mut crate::leanh::LeanObject,
    mut v___y_840_: *mut crate::leanh::LeanObject,
    mut v___y_841_: *mut crate::leanh::LeanObject,
    mut v___y_842_: *mut crate::leanh::LeanObject,
    mut v___y_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_845_ = lean_st_ref_get(v___y_843_);
    v_env_846_ = crate::leanh::lean_ctor_get(v___x_845_, 0);
    crate::leanh::lean_inc_ref(v_env_846_);
    crate::leanh::lean_dec(v___x_845_);
    v___x_847_ = lean_st_ref_get(v___y_841_);
    v_mctx_848_ = crate::leanh::lean_ctor_get(v___x_847_, 0);
    crate::leanh::lean_inc_ref(v_mctx_848_);
    crate::leanh::lean_dec(v___x_847_);
    v_lctx_849_ = crate::leanh::lean_ctor_get(v___y_840_, 2);
    v_options_850_ = crate::leanh::lean_ctor_get(v___y_842_, 2);
    crate::leanh::lean_inc_ref(v_options_850_);
    crate::leanh::lean_inc_ref(v_lctx_849_);
    v___x_851_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_851_, 0, v_env_846_);
    crate::leanh::lean_ctor_set(v___x_851_, 1, v_mctx_848_);
    crate::leanh::lean_ctor_set(v___x_851_, 2, v_lctx_849_);
    crate::leanh::lean_ctor_set(v___x_851_, 3, v_options_850_);
    v___x_852_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_852_, 0, v___x_851_);
    crate::leanh::lean_ctor_set(v___x_852_, 1, v_msgData_839_);
    v___x_853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_853_, 0, v___x_852_);
    return v___x_853_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0___boxed(
    mut v_msgData_854_: *mut crate::leanh::LeanObject,
    mut v___y_855_: *mut crate::leanh::LeanObject,
    mut v___y_856_: *mut crate::leanh::LeanObject,
    mut v___y_857_: *mut crate::leanh::LeanObject,
    mut v___y_858_: *mut crate::leanh::LeanObject,
    mut v___y_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_860_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msgData_854_, v___y_855_, v___y_856_, v___y_857_, v___y_858_);
    crate::leanh::lean_dec(v___y_858_);
    crate::leanh::lean_dec_ref(v___y_857_);
    crate::leanh::lean_dec(v___y_856_);
    crate::leanh::lean_dec_ref(v___y_855_);
    return v_res_860_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(
    mut v_msg_861_: *mut crate::leanh::LeanObject,
    mut v___y_862_: *mut crate::leanh::LeanObject,
    mut v___y_863_: *mut crate::leanh::LeanObject,
    mut v___y_864_: *mut crate::leanh::LeanObject,
    mut v___y_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_872_: u8 = 0;
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_867_ = crate::leanh::lean_ctor_get(v___y_864_, 5);
                v___x_868_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0_spec__0(v_msg_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_);
                v_a_869_ = crate::leanh::lean_ctor_get(v___x_868_, 0);
                v_isSharedCheck_877_ = (!crate::leanh::lean_is_exclusive(v___x_868_)) as u8;
                if v_isSharedCheck_877_ == 0 {
                    v___x_871_ = v___x_868_;
                    v_isShared_872_ = v_isSharedCheck_877_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_869_);
                    crate::leanh::lean_dec(v___x_868_);
                    v___x_871_ = crate::leanh::lean_box(0);
                    v_isShared_872_ = v_isSharedCheck_877_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_867_);
                v___x_873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_873_, 0, v_ref_867_);
                crate::leanh::lean_ctor_set(v___x_873_, 1, v_a_869_);
                if v_isShared_872_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_871_, 1);
                    crate::leanh::lean_ctor_set(v___x_871_, 0, v___x_873_);
                    v___x_875_ = v___x_871_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_876_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_873_);
                    v___x_875_ = v_reuseFailAlloc_876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_875_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg___boxed(
    mut v_msg_878_: *mut crate::leanh::LeanObject,
    mut v___y_879_: *mut crate::leanh::LeanObject,
    mut v___y_880_: *mut crate::leanh::LeanObject,
    mut v___y_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: *mut crate::leanh::LeanObject,
    mut v___y_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_884_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(
        v_msg_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_,
    );
    crate::leanh::lean_dec(v___y_882_);
    crate::leanh::lean_dec_ref(v___y_881_);
    crate::leanh::lean_dec(v___y_880_);
    crate::leanh::lean_dec_ref(v___y_879_);
    return v_res_884_;
}
pub unsafe fn _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__0;
    v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
    return v___x_887_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed(
    mut v_body_888_: *mut crate::leanh::LeanObject,
    mut v_body_889_: *mut crate::leanh::LeanObject,
    mut v_x_890_: *mut crate::leanh::LeanObject,
    mut v_k_891_: *mut crate::leanh::LeanObject,
    mut v_n_892_: *mut crate::leanh::LeanObject,
    mut v_x_893_: *mut crate::leanh::LeanObject,
    mut v___y_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
    mut v___y_896_: *mut crate::leanh::LeanObject,
    mut v___y_897_: *mut crate::leanh::LeanObject,
    mut v___y_898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_899_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(
        v_body_888_,
        v_body_889_,
        v_x_890_,
        v_k_891_,
        v_n_892_,
        v_x_893_,
        v___y_894_,
        v___y_895_,
        v___y_896_,
        v___y_897_,
    );
    crate::leanh::lean_dec(v___y_897_);
    crate::leanh::lean_dec_ref(v___y_896_);
    crate::leanh::lean_dec(v___y_895_);
    crate::leanh::lean_dec_ref(v___y_894_);
    crate::leanh::lean_dec(v_n_892_);
    crate::leanh::lean_dec_ref(v_body_889_);
    crate::leanh::lean_dec_ref(v_body_888_);
    return v_res_899_;
}
pub unsafe fn _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_903_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__3;
    v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
    return v___x_904_;
}
pub unsafe fn _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__5;
    v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
    return v___x_907_;
}
pub unsafe fn _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_909_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__7;
    v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
    return v___x_910_;
}
pub unsafe fn _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__9;
    v___x_913_ = l_Lean_stringToMessageData(v___x_912_);
    return v___x_913_;
}
pub unsafe fn _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_915_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__11;
    v___x_916_ = l_Lean_stringToMessageData(v___x_915_);
    return v___x_916_;
}
pub unsafe fn _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__13;
    v___x_919_ = l_Lean_stringToMessageData(v___x_918_);
    return v___x_919_;
}
pub unsafe fn _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__15;
    v___x_922_ = l_Lean_stringToMessageData(v___x_921_);
    return v___x_922_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatibleAux___redArg(
    mut v_k_923_: *mut crate::leanh::LeanObject,
    mut v_x_924_: *mut crate::leanh::LeanObject,
    mut v_x_925_: *mut crate::leanh::LeanObject,
    mut v_x_926_: *mut crate::leanh::LeanObject,
    mut v_x_927_: *mut crate::leanh::LeanObject,
    mut v_a_928_: *mut crate::leanh::LeanObject,
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_934_: u8 = 0;
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_950_: u8 = 0;
    let mut v_binderName_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_954_: u8 = 0;
    let mut v_one_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: u8 = 0;
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: u8 = 0;
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_988_: u8 = 0;
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_992_: u8 = 0;
    let mut v_a_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_996_: u8 = 0;
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1000_: u8 = 0;
    let mut v_a_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1004_: u8 = 0;
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut v___y_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1033_: u8 = 0;
    let mut v___y_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1039_: u8 = 0;
    let mut v___y_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1045_: u8 = 0;
    let mut v___x_1046_: u8 = 0;
    let mut v___y_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: u8 = 0;
    let mut v___x_1053_: u8 = 0;
    let mut v___x_1054_: u8 = 0;
    let mut v___x_1055_: u8 = 0;
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1066_: u8 = 0;
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1070_: u8 = 0;
    let mut v_a_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1078_: u8 = 0;
    let mut v_a_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1082_: u8 = 0;
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1086_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_933_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_934_ = lean_nat_dec_eq(v_x_924_, v_zero_933_);
                if v_isZero_934_ == 1 {
                    crate::leanh::lean_inc(v_a_931_);
                    crate::leanh::lean_inc_ref(v_a_930_);
                    crate::leanh::lean_inc(v_a_929_);
                    crate::leanh::lean_inc_ref(v_a_928_);
                    v___x_935_ = crate::leanh::lean_apply_8(
                        v_k_923_,
                        v_x_927_,
                        v_x_925_,
                        v_x_926_,
                        v_a_928_,
                        v_a_929_,
                        v_a_930_,
                        v_a_931_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_935_;
                } else {
                    crate::leanh::lean_inc(v_a_931_);
                    crate::leanh::lean_inc_ref(v_a_930_);
                    crate::leanh::lean_inc(v_a_929_);
                    crate::leanh::lean_inc_ref(v_a_928_);
                    v___x_936_ = lean_whnf(v_x_925_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
                    if crate::leanh::lean_obj_tag(v___x_936_) == 0 {
                        v_a_937_ = crate::leanh::lean_ctor_get(v___x_936_, 0);
                        crate::leanh::lean_inc(v_a_937_);
                        crate::leanh::lean_dec_ref_known(v___x_936_, 1);
                        crate::leanh::lean_inc(v_a_931_);
                        crate::leanh::lean_inc_ref(v_a_930_);
                        crate::leanh::lean_inc(v_a_929_);
                        crate::leanh::lean_inc_ref(v_a_928_);
                        v___x_938_ = lean_whnf(v_x_926_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
                        if crate::leanh::lean_obj_tag(v___x_938_) == 0 {
                            v_a_939_ = crate::leanh::lean_ctor_get(v___x_938_, 0);
                            crate::leanh::lean_inc(v_a_939_);
                            crate::leanh::lean_dec_ref_known(v___x_938_, 1);
                            if crate::leanh::lean_obj_tag(v_a_937_) == 7 {
                                if crate::leanh::lean_obj_tag(v_a_939_) == 7 {
                                    v_binderName_947_ = crate::leanh::lean_ctor_get(v_a_937_, 0);
                                    crate::leanh::lean_inc(v_binderName_947_);
                                    v_binderType_948_ = crate::leanh::lean_ctor_get(v_a_937_, 1);
                                    crate::leanh::lean_inc_ref(v_binderType_948_);
                                    v_body_949_ = crate::leanh::lean_ctor_get(v_a_937_, 2);
                                    crate::leanh::lean_inc_ref(v_body_949_);
                                    v_binderInfo_950_ = crate::leanh::lean_ctor_get_uint8(
                                        v_a_937_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    crate::leanh::lean_dec_ref_known(v_a_937_, 3);
                                    v_binderName_951_ = crate::leanh::lean_ctor_get(v_a_939_, 0);
                                    crate::leanh::lean_inc(v_binderName_951_);
                                    v_binderType_952_ = crate::leanh::lean_ctor_get(v_a_939_, 1);
                                    crate::leanh::lean_inc_ref(v_binderType_952_);
                                    v_body_953_ = crate::leanh::lean_ctor_get(v_a_939_, 2);
                                    crate::leanh::lean_inc_ref(v_body_953_);
                                    v_binderInfo_954_ = crate::leanh::lean_ctor_get_uint8(
                                        v_a_939_,
                                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                                            + 8) as u32,
                                    );
                                    crate::leanh::lean_dec_ref_known(v_a_939_, 3);
                                    v_one_955_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v_n_956_ = lean_nat_sub(v_x_924_, v_one_955_);
                                    v___f_957_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                                    crate::leanh::lean_closure_set(v___f_957_, 0, v_body_949_);
                                    crate::leanh::lean_closure_set(v___f_957_, 1, v_body_953_);
                                    crate::leanh::lean_closure_set(v___f_957_, 2, v_x_927_);
                                    crate::leanh::lean_closure_set(v___f_957_, 3, v_k_923_);
                                    crate::leanh::lean_closure_set(v___f_957_, 4, v_n_956_);
                                    v___x_1055_ = l_Lean_instBEqBinderInfo_beq(
                                        v_binderInfo_950_,
                                        v_binderInfo_954_,
                                    );
                                    if v___x_1055_ == 0 {
                                        crate::leanh::lean_dec_ref(v___f_957_);
                                        crate::leanh::lean_dec_ref(v_binderType_952_);
                                        crate::leanh::lean_dec(v_binderName_951_);
                                        crate::leanh::lean_dec_ref(v_binderType_948_);
                                        v___x_1056_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14), core::ptr::addr_of_mut!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14_once), _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__14);
                                        v___x_1057_ = lean_mk_syntax_ident(v_binderName_947_);
                                        v___x_1058_ = l_Lean_MessageData_ofSyntax(v___x_1057_);
                                        v___x_1059_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1059_, 0, v___x_1056_);
                                        crate::leanh::lean_ctor_set(v___x_1059_, 1, v___x_1058_);
                                        v___x_1060_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16), core::ptr::addr_of_mut!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16_once), _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__16);
                                        v___x_1061_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_1061_, 0, v___x_1059_);
                                        crate::leanh::lean_ctor_set(v___x_1061_, 1, v___x_1060_);
                                        v___x_1062_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_1061_, v_a_928_, v_a_929_, v_a_930_, v_a_931_);
                                        v_a_1063_ = crate::leanh::lean_ctor_get(v___x_1062_, 0);
                                        v_isSharedCheck_1070_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1062_)) as u8;
                                        if v_isSharedCheck_1070_ == 0 {
                                            v___x_1065_ = v___x_1062_;
                                            v_isShared_1066_ = v_isSharedCheck_1070_;
                                            state = 16;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1063_);
                                            crate::leanh::lean_dec(v___x_1062_);
                                            v___x_1065_ = crate::leanh::lean_box(0);
                                            v_isShared_1066_ = v_isSharedCheck_1070_;
                                            state = 16;
                                            continue;
                                        }
                                    } else {
                                        v___y_1048_ = v_a_928_;
                                        v___y_1049_ = v_a_929_;
                                        v___y_1050_ = v_a_930_;
                                        v___y_1051_ = v_a_931_;
                                        state = 15;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_a_937_, 3);
                                    crate::leanh::lean_dec(v_a_939_);
                                    crate::leanh::lean_dec_ref(v_x_927_);
                                    crate::leanh::lean_dec_ref(v_k_923_);
                                    v___y_941_ = v_a_928_;
                                    v___y_942_ = v_a_929_;
                                    v___y_943_ = v_a_930_;
                                    v___y_944_ = v_a_931_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_939_);
                                crate::leanh::lean_dec(v_a_937_);
                                crate::leanh::lean_dec_ref(v_x_927_);
                                crate::leanh::lean_dec_ref(v_k_923_);
                                v___y_941_ = v_a_928_;
                                v___y_942_ = v_a_929_;
                                v___y_943_ = v_a_930_;
                                v___y_944_ = v_a_931_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_937_);
                            crate::leanh::lean_dec_ref(v_x_927_);
                            crate::leanh::lean_dec_ref(v_k_923_);
                            v_a_1071_ = crate::leanh::lean_ctor_get(v___x_938_, 0);
                            v_isSharedCheck_1078_ =
                                (!crate::leanh::lean_is_exclusive(v___x_938_)) as u8;
                            if v_isSharedCheck_1078_ == 0 {
                                v___x_1073_ = v___x_938_;
                                v_isShared_1074_ = v_isSharedCheck_1078_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1071_);
                                crate::leanh::lean_dec(v___x_938_);
                                v___x_1073_ = crate::leanh::lean_box(0);
                                v_isShared_1074_ = v_isSharedCheck_1078_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_x_927_);
                        crate::leanh::lean_dec_ref(v_x_926_);
                        crate::leanh::lean_dec_ref(v_k_923_);
                        v_a_1079_ = crate::leanh::lean_ctor_get(v___x_936_, 0);
                        v_isSharedCheck_1086_ =
                            (!crate::leanh::lean_is_exclusive(v___x_936_)) as u8;
                        if v_isSharedCheck_1086_ == 0 {
                            v___x_1081_ = v___x_936_;
                            v_isShared_1082_ = v_isSharedCheck_1086_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1079_);
                            crate::leanh::lean_dec(v___x_936_);
                            v___x_1081_ = crate::leanh::lean_box(0);
                            v_isShared_1082_ = v_isSharedCheck_1086_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_945_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1_once
                    ),
                    _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__1,
                );
                v___x_946_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_945_, v___y_941_, v___y_942_, v___y_943_, v___y_944_);
                return v___x_946_;
            }
            2 => {
                v___x_963_ = 0;
                v___x_964_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__1___redArg(v_binderName_947_, v_binderInfo_950_, v_binderType_948_, v___f_957_, v___x_963_, v___y_959_, v___y_960_, v___y_961_, v___y_962_);
                return v___x_964_;
            }
            3 => {
                crate::leanh::lean_inc_ref(v_binderType_952_);
                crate::leanh::lean_inc_ref(v_binderType_948_);
                v___x_970_ = l_Lean_Meta_isExprDefEq(
                    v_binderType_948_,
                    v_binderType_952_,
                    v___y_966_,
                    v___y_967_,
                    v___y_968_,
                    v___y_969_,
                );
                if crate::leanh::lean_obj_tag(v___x_970_) == 0 {
                    v_a_971_ = crate::leanh::lean_ctor_get(v___x_970_, 0);
                    crate::leanh::lean_inc(v_a_971_);
                    crate::leanh::lean_dec_ref_known(v___x_970_, 1);
                    v___x_972_ = (crate::leanh::lean_unbox(v_a_971_) as u8);
                    crate::leanh::lean_dec(v_a_971_);
                    if v___x_972_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_957_);
                        v___x_973_ = crate::leanh::lean_box(0);
                        v___x_974_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2;
                        v___x_975_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(
                            v_binderType_948_,
                            v_binderType_952_,
                            v___x_973_,
                            v___x_974_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_975_) == 0 {
                            v_a_976_ = crate::leanh::lean_ctor_get(v___x_975_, 0);
                            crate::leanh::lean_inc(v_a_976_);
                            crate::leanh::lean_dec_ref_known(v___x_975_, 1);
                            v___x_977_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4_once), _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__4);
                            v___x_978_ = lean_mk_syntax_ident(v_binderName_947_);
                            v___x_979_ = l_Lean_MessageData_ofSyntax(v___x_978_);
                            v___x_980_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_980_, 0, v___x_977_);
                            crate::leanh::lean_ctor_set(v___x_980_, 1, v___x_979_);
                            v___x_981_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6_once), _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__6);
                            v___x_982_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_982_, 0, v___x_980_);
                            crate::leanh::lean_ctor_set(v___x_982_, 1, v___x_981_);
                            v___x_983_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_983_, 0, v___x_982_);
                            crate::leanh::lean_ctor_set(v___x_983_, 1, v_a_976_);
                            v___x_984_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_983_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
                            v_a_985_ = crate::leanh::lean_ctor_get(v___x_984_, 0);
                            v_isSharedCheck_992_ =
                                (!crate::leanh::lean_is_exclusive(v___x_984_)) as u8;
                            if v_isSharedCheck_992_ == 0 {
                                v___x_987_ = v___x_984_;
                                v_isShared_988_ = v_isSharedCheck_992_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_985_);
                                crate::leanh::lean_dec(v___x_984_);
                                v___x_987_ = crate::leanh::lean_box(0);
                                v_isShared_988_ = v_isSharedCheck_992_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_binderName_947_);
                            v_a_993_ = crate::leanh::lean_ctor_get(v___x_975_, 0);
                            v_isSharedCheck_1000_ =
                                (!crate::leanh::lean_is_exclusive(v___x_975_)) as u8;
                            if v_isSharedCheck_1000_ == 0 {
                                v___x_995_ = v___x_975_;
                                v_isShared_996_ = v_isSharedCheck_1000_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_993_);
                                crate::leanh::lean_dec(v___x_975_);
                                v___x_995_ = crate::leanh::lean_box(0);
                                v_isShared_996_ = v_isSharedCheck_1000_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_binderType_952_);
                        v___y_959_ = v___y_966_;
                        v___y_960_ = v___y_967_;
                        v___y_961_ = v___y_968_;
                        v___y_962_ = v___y_969_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_957_);
                    crate::leanh::lean_dec_ref(v_binderType_952_);
                    crate::leanh::lean_dec_ref(v_binderType_948_);
                    crate::leanh::lean_dec(v_binderName_947_);
                    v_a_1001_ = crate::leanh::lean_ctor_get(v___x_970_, 0);
                    v_isSharedCheck_1008_ = (!crate::leanh::lean_is_exclusive(v___x_970_)) as u8;
                    if v_isSharedCheck_1008_ == 0 {
                        v___x_1003_ = v___x_970_;
                        v_isShared_1004_ = v_isSharedCheck_1008_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1001_);
                        crate::leanh::lean_dec(v___x_970_);
                        v___x_1003_ = crate::leanh::lean_box(0);
                        v_isShared_1004_ = v_isSharedCheck_1008_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_988_ == 0 {
                    v___x_990_ = v___x_987_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_991_, 0, v_a_985_);
                    v___x_990_ = v_reuseFailAlloc_991_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_990_;
            }
            6 => {
                if v_isShared_996_ == 0 {
                    v___x_998_ = v___x_995_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
                    v___x_998_ = v_reuseFailAlloc_999_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_998_;
            }
            8 => {
                if v_isShared_1004_ == 0 {
                    v___x_1006_ = v___x_1003_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
                    v___x_1006_ = v_reuseFailAlloc_1007_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1006_;
            }
            10 => {
                v___x_1014_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8_once
                    ),
                    _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__8,
                );
                v___x_1015_ = lean_mk_syntax_ident(v_binderName_947_);
                v___x_1016_ = l_Lean_MessageData_ofSyntax(v___x_1015_);
                v___x_1017_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1017_, 0, v___x_1014_);
                crate::leanh::lean_ctor_set(v___x_1017_, 1, v___x_1016_);
                v___x_1018_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10_once
                    ),
                    _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__10,
                );
                v___x_1019_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1019_, 0, v___x_1017_);
                crate::leanh::lean_ctor_set(v___x_1019_, 1, v___x_1018_);
                v___x_1020_ = lean_mk_syntax_ident(v_binderName_951_);
                v___x_1021_ = l_Lean_MessageData_ofSyntax(v___x_1020_);
                v___x_1022_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1022_, 0, v___x_1019_);
                crate::leanh::lean_ctor_set(v___x_1022_, 1, v___x_1021_);
                v___x_1023_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12_once
                    ),
                    _init_l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__12,
                );
                v___x_1024_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1024_, 0, v___x_1022_);
                crate::leanh::lean_ctor_set(v___x_1024_, 1, v___x_1023_);
                v___x_1025_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(v___x_1024_, v___y_1012_, v___y_1013_, v___y_1010_, v___y_1011_);
                v_a_1026_ = crate::leanh::lean_ctor_get(v___x_1025_, 0);
                v_isSharedCheck_1033_ = (!crate::leanh::lean_is_exclusive(v___x_1025_)) as u8;
                if v_isSharedCheck_1033_ == 0 {
                    v___x_1028_ = v___x_1025_;
                    v_isShared_1029_ = v_isSharedCheck_1033_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1026_);
                    crate::leanh::lean_dec(v___x_1025_);
                    v___x_1028_ = crate::leanh::lean_box(0);
                    v_isShared_1029_ = v_isSharedCheck_1033_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1029_ == 0 {
                    v___x_1031_ = v___x_1028_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1032_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
                    v___x_1031_ = v_reuseFailAlloc_1032_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1031_;
            }
            13 => {
                if v___y_1039_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_957_);
                    crate::leanh::lean_dec_ref(v_binderType_952_);
                    crate::leanh::lean_dec_ref(v_binderType_948_);
                    v___y_1010_ = v___y_1035_;
                    v___y_1011_ = v___y_1036_;
                    v___y_1012_ = v___y_1037_;
                    v___y_1013_ = v___y_1038_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_binderName_951_);
                    v___y_966_ = v___y_1037_;
                    v___y_967_ = v___y_1038_;
                    v___y_968_ = v___y_1035_;
                    v___y_969_ = v___y_1036_;
                    state = 3;
                    continue;
                }
            }
            14 => {
                if v___y_1045_ == 0 {
                    crate::leanh::lean_dec_ref(v___f_957_);
                    crate::leanh::lean_dec_ref(v_binderType_952_);
                    crate::leanh::lean_dec_ref(v_binderType_948_);
                    v___y_1010_ = v___y_1041_;
                    v___y_1011_ = v___y_1042_;
                    v___y_1012_ = v___y_1043_;
                    v___y_1013_ = v___y_1044_;
                    state = 10;
                    continue;
                } else {
                    v___x_1046_ = l_Lean_Name_hasMacroScopes(v_binderName_951_);
                    v___y_1035_ = v___y_1041_;
                    v___y_1036_ = v___y_1042_;
                    v___y_1037_ = v___y_1043_;
                    v___y_1038_ = v___y_1044_;
                    v___y_1039_ = v___x_1046_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_1052_ = lean_name_eq(v_binderName_947_, v_binderName_951_);
                if v___x_1052_ == 0 {
                    v___x_1053_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_950_);
                    if v___x_1053_ == 0 {
                        v___y_1041_ = v___y_1050_;
                        v___y_1042_ = v___y_1051_;
                        v___y_1043_ = v___y_1048_;
                        v___y_1044_ = v___y_1049_;
                        v___y_1045_ = v___x_1053_;
                        state = 14;
                        continue;
                    } else {
                        v___x_1054_ = l_Lean_Name_hasMacroScopes(v_binderName_947_);
                        v___y_1041_ = v___y_1050_;
                        v___y_1042_ = v___y_1051_;
                        v___y_1043_ = v___y_1048_;
                        v___y_1044_ = v___y_1049_;
                        v___y_1045_ = v___x_1054_;
                        state = 14;
                        continue;
                    }
                } else {
                    v___y_1035_ = v___y_1050_;
                    v___y_1036_ = v___y_1051_;
                    v___y_1037_ = v___y_1048_;
                    v___y_1038_ = v___y_1049_;
                    v___y_1039_ = v___x_1052_;
                    state = 13;
                    continue;
                }
            }
            16 => {
                if v_isShared_1066_ == 0 {
                    v___x_1068_ = v___x_1065_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
                    v___x_1068_ = v_reuseFailAlloc_1069_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1068_;
            }
            18 => {
                if v_isShared_1074_ == 0 {
                    v___x_1076_ = v___x_1073_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_a_1071_);
                    v___x_1076_ = v_reuseFailAlloc_1077_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1076_;
            }
            20 => {
                if v_isShared_1082_ == 0 {
                    v___x_1084_ = v___x_1081_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1085_, 0, v_a_1079_);
                    v___x_1084_ = v_reuseFailAlloc_1085_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1084_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatibleAux___redArg___lam__0(
    mut v_body_1087_: *mut crate::leanh::LeanObject,
    mut v_body_1088_: *mut crate::leanh::LeanObject,
    mut v_x_1089_: *mut crate::leanh::LeanObject,
    mut v_k_1090_: *mut crate::leanh::LeanObject,
    mut v_n_1091_: *mut crate::leanh::LeanObject,
    mut v_x_1092_: *mut crate::leanh::LeanObject,
    mut v___y_1093_: *mut crate::leanh::LeanObject,
    mut v___y_1094_: *mut crate::leanh::LeanObject,
    mut v___y_1095_: *mut crate::leanh::LeanObject,
    mut v___y_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1098_ = lean_expr_instantiate1(v_body_1087_, v_x_1092_);
    v___x_1099_ = lean_expr_instantiate1(v_body_1088_, v_x_1092_);
    v___x_1100_ = lean_array_push(v_x_1089_, v_x_1092_);
    v___x_1101_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(
        v_k_1090_,
        v_n_1091_,
        v___x_1098_,
        v___x_1099_,
        v___x_1100_,
        v___y_1093_,
        v___y_1094_,
        v___y_1095_,
        v___y_1096_,
    );
    return v___x_1101_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatibleAux___redArg___boxed(
    mut v_k_1102_: *mut crate::leanh::LeanObject,
    mut v_x_1103_: *mut crate::leanh::LeanObject,
    mut v_x_1104_: *mut crate::leanh::LeanObject,
    mut v_x_1105_: *mut crate::leanh::LeanObject,
    mut v_x_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1112_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(
        v_k_1102_, v_x_1103_, v_x_1104_, v_x_1105_, v_x_1106_, v_a_1107_, v_a_1108_, v_a_1109_,
        v_a_1110_,
    );
    crate::leanh::lean_dec(v_a_1110_);
    crate::leanh::lean_dec_ref(v_a_1109_);
    crate::leanh::lean_dec(v_a_1108_);
    crate::leanh::lean_dec_ref(v_a_1107_);
    crate::leanh::lean_dec(v_x_1103_);
    return v_res_1112_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatibleAux(
    mut v_00_u03b1_1113_: *mut crate::leanh::LeanObject,
    mut v_k_1114_: *mut crate::leanh::LeanObject,
    mut v_x_1115_: *mut crate::leanh::LeanObject,
    mut v_x_1116_: *mut crate::leanh::LeanObject,
    mut v_x_1117_: *mut crate::leanh::LeanObject,
    mut v_x_1118_: *mut crate::leanh::LeanObject,
    mut v_a_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
    mut v_a_1122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1124_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(
        v_k_1114_, v_x_1115_, v_x_1116_, v_x_1117_, v_x_1118_, v_a_1119_, v_a_1120_, v_a_1121_,
        v_a_1122_,
    );
    return v___x_1124_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatibleAux___boxed(
    mut v_00_u03b1_1125_: *mut crate::leanh::LeanObject,
    mut v_k_1126_: *mut crate::leanh::LeanObject,
    mut v_x_1127_: *mut crate::leanh::LeanObject,
    mut v_x_1128_: *mut crate::leanh::LeanObject,
    mut v_x_1129_: *mut crate::leanh::LeanObject,
    mut v_x_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
    mut v_a_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
    mut v_a_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1136_ = l_Lean_Meta_forallTelescopeCompatibleAux(
        v_00_u03b1_1125_,
        v_k_1126_,
        v_x_1127_,
        v_x_1128_,
        v_x_1129_,
        v_x_1130_,
        v_a_1131_,
        v_a_1132_,
        v_a_1133_,
        v_a_1134_,
    );
    crate::leanh::lean_dec(v_a_1134_);
    crate::leanh::lean_dec_ref(v_a_1133_);
    crate::leanh::lean_dec(v_a_1132_);
    crate::leanh::lean_dec_ref(v_a_1131_);
    crate::leanh::lean_dec(v_x_1127_);
    return v_res_1136_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(
    mut v_00_u03b1_1137_: *mut crate::leanh::LeanObject,
    mut v_msg_1138_: *mut crate::leanh::LeanObject,
    mut v___y_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1144_ =
        l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___redArg(
            v_msg_1138_,
            v___y_1139_,
            v___y_1140_,
            v___y_1141_,
            v___y_1142_,
        );
    return v___x_1144_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0___boxed(
    mut v_00_u03b1_1145_: *mut crate::leanh::LeanObject,
    mut v_msg_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
    mut v___y_1148_: *mut crate::leanh::LeanObject,
    mut v___y_1149_: *mut crate::leanh::LeanObject,
    mut v___y_1150_: *mut crate::leanh::LeanObject,
    mut v___y_1151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1152_ = l_Lean_throwError___at___00Lean_Meta_forallTelescopeCompatibleAux_spec__0(
        v_00_u03b1_1145_,
        v_msg_1146_,
        v___y_1147_,
        v___y_1148_,
        v___y_1149_,
        v___y_1150_,
    );
    crate::leanh::lean_dec(v___y_1150_);
    crate::leanh::lean_dec_ref(v___y_1149_);
    crate::leanh::lean_dec(v___y_1148_);
    crate::leanh::lean_dec_ref(v___y_1147_);
    return v_res_1152_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(
    mut v_k_1153_: *mut crate::leanh::LeanObject,
    mut v_runInBase_1154_: *mut crate::leanh::LeanObject,
    mut v_xs_1155_: *mut crate::leanh::LeanObject,
    mut v_type_u2081_1156_: *mut crate::leanh::LeanObject,
    mut v_type_u2082_1157_: *mut crate::leanh::LeanObject,
    mut v___y_1158_: *mut crate::leanh::LeanObject,
    mut v___y_1159_: *mut crate::leanh::LeanObject,
    mut v___y_1160_: *mut crate::leanh::LeanObject,
    mut v___y_1161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1163_ = crate::leanh::lean_apply_3(
        v_k_1153_,
        v_xs_1155_,
        v_type_u2081_1156_,
        v_type_u2082_1157_,
    );
    crate::leanh::lean_inc(v___y_1161_);
    crate::leanh::lean_inc_ref(v___y_1160_);
    crate::leanh::lean_inc(v___y_1159_);
    crate::leanh::lean_inc_ref(v___y_1158_);
    v___x_1164_ = crate::leanh::lean_apply_7(
        v_runInBase_1154_,
        crate::leanh::lean_box(0),
        v___x_1163_,
        v___y_1158_,
        v___y_1159_,
        v___y_1160_,
        v___y_1161_,
        crate::leanh::lean_box(0),
    );
    return v___x_1164_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed(
    mut v_k_1165_: *mut crate::leanh::LeanObject,
    mut v_runInBase_1166_: *mut crate::leanh::LeanObject,
    mut v_xs_1167_: *mut crate::leanh::LeanObject,
    mut v_type_u2081_1168_: *mut crate::leanh::LeanObject,
    mut v_type_u2082_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
    mut v___y_1171_: *mut crate::leanh::LeanObject,
    mut v___y_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1175_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0(
        v_k_1165_,
        v_runInBase_1166_,
        v_xs_1167_,
        v_type_u2081_1168_,
        v_type_u2082_1169_,
        v___y_1170_,
        v___y_1171_,
        v___y_1172_,
        v___y_1173_,
    );
    crate::leanh::lean_dec(v___y_1173_);
    crate::leanh::lean_dec_ref(v___y_1172_);
    crate::leanh::lean_dec(v___y_1171_);
    crate::leanh::lean_dec_ref(v___y_1170_);
    return v_res_1175_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(
    mut v_k_1176_: *mut crate::leanh::LeanObject,
    mut v_numParams_1177_: *mut crate::leanh::LeanObject,
    mut v_type_u2081_1178_: *mut crate::leanh::LeanObject,
    mut v_type_u2082_1179_: *mut crate::leanh::LeanObject,
    mut v_runInBase_1180_: *mut crate::leanh::LeanObject,
    mut v___y_1181_: *mut crate::leanh::LeanObject,
    mut v___y_1182_: *mut crate::leanh::LeanObject,
    mut v___y_1183_: *mut crate::leanh::LeanObject,
    mut v___y_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1186_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_forallTelescopeCompatible___redArg___lam__0___boxed as *mut core::ffi::c_void,
        10,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1186_, 0, v_k_1176_);
    crate::leanh::lean_closure_set(v___f_1186_, 1, v_runInBase_1180_);
    v___x_1187_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg___closed__2;
    v___x_1188_ = l_Lean_Meta_forallTelescopeCompatibleAux___redArg(
        v___f_1186_,
        v_numParams_1177_,
        v_type_u2081_1178_,
        v_type_u2082_1179_,
        v___x_1187_,
        v___y_1181_,
        v___y_1182_,
        v___y_1183_,
        v___y_1184_,
    );
    return v___x_1188_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed(
    mut v_k_1189_: *mut crate::leanh::LeanObject,
    mut v_numParams_1190_: *mut crate::leanh::LeanObject,
    mut v_type_u2081_1191_: *mut crate::leanh::LeanObject,
    mut v_type_u2082_1192_: *mut crate::leanh::LeanObject,
    mut v_runInBase_1193_: *mut crate::leanh::LeanObject,
    mut v___y_1194_: *mut crate::leanh::LeanObject,
    mut v___y_1195_: *mut crate::leanh::LeanObject,
    mut v___y_1196_: *mut crate::leanh::LeanObject,
    mut v___y_1197_: *mut crate::leanh::LeanObject,
    mut v___y_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1199_ = l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1(
        v_k_1189_,
        v_numParams_1190_,
        v_type_u2081_1191_,
        v_type_u2082_1192_,
        v_runInBase_1193_,
        v___y_1194_,
        v___y_1195_,
        v___y_1196_,
        v___y_1197_,
    );
    crate::leanh::lean_dec(v___y_1197_);
    crate::leanh::lean_dec_ref(v___y_1196_);
    crate::leanh::lean_dec(v___y_1195_);
    crate::leanh::lean_dec_ref(v___y_1194_);
    crate::leanh::lean_dec(v_numParams_1190_);
    return v_res_1199_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatible___redArg(
    mut v_inst_1200_: *mut crate::leanh::LeanObject,
    mut v_inst_1201_: *mut crate::leanh::LeanObject,
    mut v_type_u2081_1202_: *mut crate::leanh::LeanObject,
    mut v_type_u2082_1203_: *mut crate::leanh::LeanObject,
    mut v_numParams_1204_: *mut crate::leanh::LeanObject,
    mut v_k_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_liftWith_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_restoreM_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1206_ = crate::leanh::lean_ctor_get(v_inst_1200_, 1);
    crate::leanh::lean_inc(v_toBind_1206_);
    crate::leanh::lean_dec_ref(v_inst_1200_);
    v_liftWith_1207_ = crate::leanh::lean_ctor_get(v_inst_1201_, 0);
    crate::leanh::lean_inc(v_liftWith_1207_);
    v_restoreM_1208_ = crate::leanh::lean_ctor_get(v_inst_1201_, 1);
    crate::leanh::lean_inc(v_restoreM_1208_);
    crate::leanh::lean_dec_ref(v_inst_1201_);
    v___f_1209_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_forallTelescopeCompatible___redArg___lam__1___boxed as *mut core::ffi::c_void,
        10,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1209_, 0, v_k_1205_);
    crate::leanh::lean_closure_set(v___f_1209_, 1, v_numParams_1204_);
    crate::leanh::lean_closure_set(v___f_1209_, 2, v_type_u2081_1202_);
    crate::leanh::lean_closure_set(v___f_1209_, 3, v_type_u2082_1203_);
    v___x_1210_ =
        crate::leanh::lean_apply_2(v_liftWith_1207_, crate::leanh::lean_box(0), v___f_1209_);
    v___x_1211_ = crate::leanh::lean_apply_1(v_restoreM_1208_, crate::leanh::lean_box(0));
    v___x_1212_ = crate::leanh::lean_apply_4(
        v_toBind_1206_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1210_,
        v___x_1211_,
    );
    return v___x_1212_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeCompatible(
    mut v_m_1213_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1214_: *mut crate::leanh::LeanObject,
    mut v_inst_1215_: *mut crate::leanh::LeanObject,
    mut v_inst_1216_: *mut crate::leanh::LeanObject,
    mut v_type_u2081_1217_: *mut crate::leanh::LeanObject,
    mut v_type_u2082_1218_: *mut crate::leanh::LeanObject,
    mut v_numParams_1219_: *mut crate::leanh::LeanObject,
    mut v_k_1220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1221_ = l_Lean_Meta_forallTelescopeCompatible___redArg(
        v_inst_1215_,
        v_inst_1216_,
        v_type_u2081_1217_,
        v_type_u2082_1218_,
        v_numParams_1219_,
        v_k_1220_,
    );
    return v___x_1221_;
}
pub unsafe fn l_Lean_Elab_expandOptDeclSig(
    mut v_stx_1222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_optType_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    v___x_1223_ = crate::leanh::lean_unsigned_to_nat(0);
    v_binders_1224_ = l_Lean_Syntax_getArg(v_stx_1222_, v___x_1223_);
    v___x_1225_ = crate::leanh::lean_unsigned_to_nat(1);
    v_optType_1226_ = l_Lean_Syntax_getArg(v_stx_1222_, v___x_1225_);
    v___x_1227_ = l_Lean_Syntax_isNone(v_optType_1226_);
    if v___x_1227_ == 0 {
        let mut v_typeSpec_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_typeSpec_1228_ = l_Lean_Syntax_getArg(v_optType_1226_, v___x_1223_);
        crate::leanh::lean_dec(v_optType_1226_);
        v___x_1229_ = l_Lean_Syntax_getArg(v_typeSpec_1228_, v___x_1225_);
        crate::leanh::lean_dec(v_typeSpec_1228_);
        v___x_1230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1230_, 0, v___x_1229_);
        v___x_1231_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1231_, 0, v_binders_1224_);
        crate::leanh::lean_ctor_set(v___x_1231_, 1, v___x_1230_);
        return v___x_1231_;
    } else {
        let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_optType_1226_);
        v___x_1232_ = crate::leanh::lean_box(0);
        v___x_1233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1233_, 0, v_binders_1224_);
        crate::leanh::lean_ctor_set(v___x_1233_, 1, v___x_1232_);
        return v___x_1233_;
    }
}
pub unsafe fn l_Lean_Elab_expandOptDeclSig___boxed(
    mut v_stx_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1235_ = l_Lean_Elab_expandOptDeclSig(v_stx_1234_);
    crate::leanh::lean_dec(v_stx_1234_);
    return v_res_1235_;
}
pub unsafe fn l_Lean_Elab_expandDeclSig(
    mut v_stx_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeSpec_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = crate::leanh::lean_unsigned_to_nat(0);
    v_binders_1238_ = l_Lean_Syntax_getArg(v_stx_1236_, v___x_1237_);
    v___x_1239_ = crate::leanh::lean_unsigned_to_nat(1);
    v_typeSpec_1240_ = l_Lean_Syntax_getArg(v_stx_1236_, v___x_1239_);
    v___x_1241_ = l_Lean_Syntax_getArg(v_typeSpec_1240_, v___x_1239_);
    crate::leanh::lean_dec(v_typeSpec_1240_);
    v___x_1242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1242_, 0, v_binders_1238_);
    crate::leanh::lean_ctor_set(v___x_1242_, 1, v___x_1241_);
    return v___x_1242_;
}
pub unsafe fn l_Lean_Elab_expandDeclSig___boxed(
    mut v_stx_1243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1244_ = l_Lean_Elab_expandDeclSig(v_stx_1243_);
    crate::leanh::lean_dec(v_stx_1243_);
    return v_res_1244_;
}
pub unsafe fn l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(
    mut v_a_1245_: *mut crate::leanh::LeanObject,
    mut v_x_1246_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1247_: u8 = 0;
    let mut v_head_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1246_) == 0 {
                    v___x_1247_ = 0;
                    return v___x_1247_;
                } else {
                    v_head_1248_ = crate::leanh::lean_ctor_get(v_x_1246_, 0);
                    v_tail_1249_ = crate::leanh::lean_ctor_get(v_x_1246_, 1);
                    v___x_1250_ = lean_name_eq(v_a_1245_, v_head_1248_);
                    if v___x_1250_ == 0 {
                        v_x_1246_ = v_tail_1249_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1250_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0___boxed(
    mut v_a_1252_: *mut crate::leanh::LeanObject,
    mut v_x_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1254_: u8 = 0;
    let mut v_r_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1254_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(v_a_1252_, v_x_1253_);
    crate::leanh::lean_dec(v_x_1253_);
    crate::leanh::lean_dec(v_a_1252_);
    v_r_1255_ = crate::leanh::lean_box((v_res_1254_) as usize);
    return v_r_1255_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(
    mut v_allUserParams_1256_: *mut crate::leanh::LeanObject,
    mut v_as_1257_: *mut crate::leanh::LeanObject,
    mut v_i_1258_: usize,
    mut v_stop_1259_: usize,
    mut v_b_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: usize = 0;
    let mut v___x_1264_: usize = 0;
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1266_ = lean_usize_dec_eq(v_i_1258_, v_stop_1259_);
                if v___x_1266_ == 0 {
                    v___x_1267_ = lean_array_uget_borrowed(v_as_1257_, v_i_1258_);
                    v___x_1268_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(
                        v___x_1267_,
                        v_allUserParams_1256_,
                    );
                    if v___x_1268_ == 0 {
                        crate::leanh::lean_inc(v___x_1267_);
                        v___x_1269_ = lean_array_push(v_b_1260_, v___x_1267_);
                        v___y_1262_ = v___x_1269_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1262_ = v_b_1260_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1260_;
                }
            }
            1 => {
                v___x_1263_ = 1usize;
                v___x_1264_ = lean_usize_add(v_i_1258_, v___x_1263_);
                v_i_1258_ = v___x_1264_;
                v_b_1260_ = v___y_1262_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5___boxed(
    mut v_allUserParams_1270_: *mut crate::leanh::LeanObject,
    mut v_as_1271_: *mut crate::leanh::LeanObject,
    mut v_i_1272_: *mut crate::leanh::LeanObject,
    mut v_stop_1273_: *mut crate::leanh::LeanObject,
    mut v_b_1274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1275_: usize = 0;
    let mut v_stop_boxed_1276_: usize = 0;
    let mut v_res_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1275_ = crate::leanh::lean_unbox_usize(v_i_1272_);
    crate::leanh::lean_dec(v_i_1272_);
    v_stop_boxed_1276_ = crate::leanh::lean_unbox_usize(v_stop_1273_);
    crate::leanh::lean_dec(v_stop_1273_);
    v_res_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_1270_, v_as_1271_, v_i_boxed_1275_, v_stop_boxed_1276_, v_b_1274_);
    crate::leanh::lean_dec_ref(v_as_1271_);
    crate::leanh::lean_dec(v_allUserParams_1270_);
    return v_res_1277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(
    mut v_a_1278_: *mut crate::leanh::LeanObject,
    mut v_as_1279_: *mut crate::leanh::LeanObject,
    mut v_i_1280_: usize,
    mut v_stop_1281_: usize,
) -> u8 {
    let mut v___x_1282_: u8 = 0;
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: u8 = 0;
    let mut v___x_1285_: usize = 0;
    let mut v___x_1286_: usize = 0;
    let mut v___x_1288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1282_ = lean_usize_dec_eq(v_i_1280_, v_stop_1281_);
                if v___x_1282_ == 0 {
                    v___x_1283_ = lean_array_uget_borrowed(v_as_1279_, v_i_1280_);
                    v___x_1284_ = lean_name_eq(v_a_1278_, v___x_1283_);
                    if v___x_1284_ == 0 {
                        v___x_1285_ = 1usize;
                        v___x_1286_ = lean_usize_add(v_i_1280_, v___x_1285_);
                        v_i_1280_ = v___x_1286_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1284_;
                    }
                } else {
                    v___x_1288_ = 0;
                    return v___x_1288_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1___boxed(
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_as_1290_: *mut crate::leanh::LeanObject,
    mut v_i_1291_: *mut crate::leanh::LeanObject,
    mut v_stop_1292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1293_: usize = 0;
    let mut v_stop_boxed_1294_: usize = 0;
    let mut v_res_1295_: u8 = 0;
    let mut v_r_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1293_ = crate::leanh::lean_unbox_usize(v_i_1291_);
    crate::leanh::lean_dec(v_i_1291_);
    v_stop_boxed_1294_ = crate::leanh::lean_unbox_usize(v_stop_1292_);
    crate::leanh::lean_dec(v_stop_1292_);
    v_res_1295_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_1289_, v_as_1290_, v_i_boxed_1293_, v_stop_boxed_1294_);
    crate::leanh::lean_dec_ref(v_as_1290_);
    crate::leanh::lean_dec(v_a_1289_);
    v_r_1296_ = crate::leanh::lean_box((v_res_1295_) as usize);
    return v_r_1296_;
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(
    mut v_as_1297_: *mut crate::leanh::LeanObject,
    mut v_a_1298_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: u8 = 0;
    v___x_1299_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1300_ = lean_array_get_size(v_as_1297_);
    v___x_1301_ = lean_nat_dec_lt(v___x_1299_, v___x_1300_);
    if v___x_1301_ == 0 {
        return v___x_1301_;
    } else {
        if v___x_1301_ == 0 {
            return v___x_1301_;
        } else {
            let mut v___x_1302_: usize = 0;
            let mut v___x_1303_: usize = 0;
            let mut v___x_1304_: u8 = 0;
            v___x_1302_ = 0usize;
            v___x_1303_ = lean_usize_of_nat(v___x_1300_);
            v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1_spec__1(v_a_1298_, v_as_1297_, v___x_1302_, v___x_1303_);
            return v___x_1304_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1___boxed(
    mut v_as_1305_: *mut crate::leanh::LeanObject,
    mut v_a_1306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1307_: u8 = 0;
    let mut v_r_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ =
        l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(v_as_1305_, v_a_1306_);
    crate::leanh::lean_dec(v_a_1306_);
    crate::leanh::lean_dec_ref(v_as_1305_);
    v_r_1308_ = crate::leanh::lean_box((v_res_1307_) as usize);
    return v_r_1308_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(
    mut v_usedParams_1309_: *mut crate::leanh::LeanObject,
    mut v_x_1310_: *mut crate::leanh::LeanObject,
    mut v_x_1311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1316_: u8 = 0;
    let mut v___x_1317_: u8 = 0;
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1311_) == 0 {
                    return v_x_1310_;
                } else {
                    v_head_1312_ = crate::leanh::lean_ctor_get(v_x_1311_, 0);
                    v_tail_1313_ = crate::leanh::lean_ctor_get(v_x_1311_, 1);
                    v_isSharedCheck_1323_ = (!crate::leanh::lean_is_exclusive(v_x_1311_)) as u8;
                    if v_isSharedCheck_1323_ == 0 {
                        v___x_1315_ = v_x_1311_;
                        v_isShared_1316_ = v_isSharedCheck_1323_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1313_);
                        crate::leanh::lean_inc(v_head_1312_);
                        crate::leanh::lean_dec(v_x_1311_);
                        v___x_1315_ = crate::leanh::lean_box(0);
                        v_isShared_1316_ = v_isSharedCheck_1323_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1317_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(
                    v_usedParams_1309_,
                    v_head_1312_,
                );
                if v___x_1317_ == 0 {
                    crate::leanh::lean_del_object(v___x_1315_);
                    crate::leanh::lean_dec(v_head_1312_);
                    v_x_1311_ = v_tail_1313_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_1316_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1315_, 1, v_x_1310_);
                        v___x_1320_ = v___x_1315_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1322_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_head_1312_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1322_, 1, v_x_1310_);
                        v___x_1320_ = v_reuseFailAlloc_1322_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_x_1310_ = v___x_1320_;
                v_x_1311_ = v_tail_1313_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3___boxed(
    mut v_usedParams_1324_: *mut crate::leanh::LeanObject,
    mut v_x_1325_: *mut crate::leanh::LeanObject,
    mut v_x_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1327_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(
        v_usedParams_1324_,
        v_x_1325_,
        v_x_1326_,
    );
    crate::leanh::lean_dec_ref(v_usedParams_1324_);
    return v_res_1327_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(
    mut v_usedParams_1328_: *mut crate::leanh::LeanObject,
    mut v_scopeParams_1329_: *mut crate::leanh::LeanObject,
    mut v_x_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: u8 = 0;
    let mut v___x_1335_: u8 = 0;
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1330_) == 0 {
                    v___x_1331_ = crate::leanh::lean_box(0);
                    return v___x_1331_;
                } else {
                    v_head_1332_ = crate::leanh::lean_ctor_get(v_x_1330_, 0);
                    v_tail_1333_ = crate::leanh::lean_ctor_get(v_x_1330_, 1);
                    v___x_1334_ = l_Array_contains___at___00Lean_Elab_sortDeclLevelParams_spec__1(
                        v_usedParams_1328_,
                        v_head_1332_,
                    );
                    if v___x_1334_ == 0 {
                        v___x_1335_ = l_List_elem___at___00Lean_Elab_sortDeclLevelParams_spec__0(
                            v_head_1332_,
                            v_scopeParams_1329_,
                        );
                        if v___x_1335_ == 0 {
                            crate::leanh::lean_inc(v_head_1332_);
                            v___x_1336_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1336_, 0, v_head_1332_);
                            return v___x_1336_;
                        } else {
                            if v___x_1334_ == 0 {
                                v_x_1330_ = v_tail_1333_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_head_1332_);
                                v___x_1338_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1338_, 0, v_head_1332_);
                                return v___x_1338_;
                            }
                        }
                    } else {
                        v_x_1330_ = v_tail_1333_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2___boxed(
    mut v_usedParams_1340_: *mut crate::leanh::LeanObject,
    mut v_scopeParams_1341_: *mut crate::leanh::LeanObject,
    mut v_x_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1343_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(
        v_usedParams_1340_,
        v_scopeParams_1341_,
        v_x_1342_,
    );
    crate::leanh::lean_dec(v_x_1342_);
    crate::leanh::lean_dec(v_scopeParams_1341_);
    crate::leanh::lean_dec_ref(v_usedParams_1340_);
    return v_res_1343_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(
    mut v_hi_1344_: *mut crate::leanh::LeanObject,
    mut v_pivot_1345_: *mut crate::leanh::LeanObject,
    mut v_as_1346_: *mut crate::leanh::LeanObject,
    mut v_i_1347_: *mut crate::leanh::LeanObject,
    mut v_k_1348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1349_: u8 = 0;
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: u8 = 0;
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1349_ = lean_nat_dec_lt(v_k_1348_, v_hi_1344_);
                if v___x_1349_ == 0 {
                    crate::leanh::lean_dec(v_k_1348_);
                    v___x_1350_ = lean_array_fswap(v_as_1346_, v_i_1347_, v_hi_1344_);
                    v___x_1351_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1351_, 0, v_i_1347_);
                    crate::leanh::lean_ctor_set(v___x_1351_, 1, v___x_1350_);
                    return v___x_1351_;
                } else {
                    v___x_1352_ = lean_array_fget_borrowed(v_as_1346_, v_k_1348_);
                    v___x_1353_ = l_Lean_Name_lt(v___x_1352_, v_pivot_1345_);
                    if v___x_1353_ == 0 {
                        v___x_1354_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1355_ = lean_nat_add(v_k_1348_, v___x_1354_);
                        crate::leanh::lean_dec(v_k_1348_);
                        v_k_1348_ = v___x_1355_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1357_ = lean_array_fswap(v_as_1346_, v_i_1347_, v_k_1348_);
                        v___x_1358_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1359_ = lean_nat_add(v_i_1347_, v___x_1358_);
                        crate::leanh::lean_dec(v_i_1347_);
                        v___x_1360_ = lean_nat_add(v_k_1348_, v___x_1358_);
                        crate::leanh::lean_dec(v_k_1348_);
                        v_as_1346_ = v___x_1357_;
                        v_i_1347_ = v___x_1359_;
                        v_k_1348_ = v___x_1360_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg___boxed(
    mut v_hi_1362_: *mut crate::leanh::LeanObject,
    mut v_pivot_1363_: *mut crate::leanh::LeanObject,
    mut v_as_1364_: *mut crate::leanh::LeanObject,
    mut v_i_1365_: *mut crate::leanh::LeanObject,
    mut v_k_1366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_1362_, v_pivot_1363_, v_as_1364_, v_i_1365_, v_k_1366_);
    crate::leanh::lean_dec(v_pivot_1363_);
    crate::leanh::lean_dec(v_hi_1362_);
    return v_res_1367_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(
    mut v_n_1368_: *mut crate::leanh::LeanObject,
    mut v_as_1369_: *mut crate::leanh::LeanObject,
    mut v_lo_1370_: *mut crate::leanh::LeanObject,
    mut v_hi_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: u8 = 0;
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: u8 = 0;
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1383_ = lean_nat_dec_lt(v_lo_1370_, v_hi_1371_);
                if v___x_1383_ == 0 {
                    crate::leanh::lean_dec(v_lo_1370_);
                    return v_as_1369_;
                } else {
                    v___x_1384_ = lean_nat_add(v_lo_1370_, v_hi_1371_);
                    v___x_1385_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_1386_ = lean_nat_shiftr(v___x_1384_, v___x_1385_);
                    crate::leanh::lean_dec(v___x_1384_);
                    v___x_1399_ = lean_array_fget_borrowed(v_as_1369_, v_mid_1386_);
                    v___x_1400_ = lean_array_fget_borrowed(v_as_1369_, v_lo_1370_);
                    v___x_1401_ = l_Lean_Name_lt(v___x_1399_, v___x_1400_);
                    if v___x_1401_ == 0 {
                        v___y_1394_ = v_as_1369_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1402_ = lean_array_fswap(v_as_1369_, v_lo_1370_, v_mid_1386_);
                        v___y_1394_ = v___x_1402_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_1374_ = lean_array_fget(v___y_1373_, v_hi_1371_);
                crate::leanh::lean_inc_n(v_lo_1370_, 2);
                v___x_1375_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_1371_, v_pivot_1374_, v___y_1373_, v_lo_1370_, v_lo_1370_);
                crate::leanh::lean_dec(v_pivot_1374_);
                v_fst_1376_ = crate::leanh::lean_ctor_get(v___x_1375_, 0);
                crate::leanh::lean_inc(v_fst_1376_);
                v_snd_1377_ = crate::leanh::lean_ctor_get(v___x_1375_, 1);
                crate::leanh::lean_inc(v_snd_1377_);
                crate::leanh::lean_dec_ref(v___x_1375_);
                v___x_1378_ = lean_nat_dec_le(v_hi_1371_, v_fst_1376_);
                if v___x_1378_ == 0 {
                    v___x_1379_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_1368_, v_snd_1377_, v_lo_1370_, v_fst_1376_);
                    v___x_1380_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1381_ = lean_nat_add(v_fst_1376_, v___x_1380_);
                    crate::leanh::lean_dec(v_fst_1376_);
                    v_as_1369_ = v___x_1379_;
                    v_lo_1370_ = v___x_1381_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_1376_);
                    crate::leanh::lean_dec(v_lo_1370_);
                    return v_snd_1377_;
                }
            }
            2 => {
                v___x_1389_ = lean_array_fget_borrowed(v___y_1388_, v_mid_1386_);
                v___x_1390_ = lean_array_fget_borrowed(v___y_1388_, v_hi_1371_);
                v___x_1391_ = l_Lean_Name_lt(v___x_1389_, v___x_1390_);
                if v___x_1391_ == 0 {
                    crate::leanh::lean_dec(v_mid_1386_);
                    v___y_1373_ = v___y_1388_;
                    state = 1;
                    continue;
                } else {
                    v___x_1392_ = lean_array_fswap(v___y_1388_, v_mid_1386_, v_hi_1371_);
                    crate::leanh::lean_dec(v_mid_1386_);
                    v___y_1373_ = v___x_1392_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1395_ = lean_array_fget_borrowed(v___y_1394_, v_hi_1371_);
                v___x_1396_ = lean_array_fget_borrowed(v___y_1394_, v_lo_1370_);
                v___x_1397_ = l_Lean_Name_lt(v___x_1395_, v___x_1396_);
                if v___x_1397_ == 0 {
                    v___y_1388_ = v___y_1394_;
                    state = 2;
                    continue;
                } else {
                    v___x_1398_ = lean_array_fswap(v___y_1394_, v_lo_1370_, v_hi_1371_);
                    v___y_1388_ = v___x_1398_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg___boxed(
    mut v_n_1403_: *mut crate::leanh::LeanObject,
    mut v_as_1404_: *mut crate::leanh::LeanObject,
    mut v_lo_1405_: *mut crate::leanh::LeanObject,
    mut v_hi_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1407_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_1403_, v_as_1404_, v_lo_1405_, v_hi_1406_);
    crate::leanh::lean_dec(v_hi_1406_);
    crate::leanh::lean_dec(v_n_1403_);
    return v_res_1407_;
}
pub unsafe fn l_Lean_Elab_sortDeclLevelParams(
    mut v_scopeParams_1412_: *mut crate::leanh::LeanObject,
    mut v_allUserParams_1413_: *mut crate::leanh::LeanObject,
    mut v_usedParams_1414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: u8 = 0;
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: u8 = 0;
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: u8 = 0;
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: usize = 0;
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: usize = 0;
    let mut v___x_1451_: usize = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1456_: u8 = 0;
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: u8 = 0;
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1466_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1415_ = l_List_find_x3f___at___00Lean_Elab_sortDeclLevelParams_spec__2(
                    v_usedParams_1414_,
                    v_scopeParams_1412_,
                    v_allUserParams_1413_,
                );
                if crate::leanh::lean_obj_tag(v___x_1415_) == 0 {
                    v___x_1416_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_allUserParams_1413_);
                    v_result_1417_ = l_List_foldl___at___00Lean_Elab_sortDeclLevelParams_spec__3(
                        v_usedParams_1414_,
                        v___x_1416_,
                        v_allUserParams_1413_,
                    );
                    v___x_1435_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1443_ = lean_array_get_size(v_usedParams_1414_);
                    v___x_1444_ = l_Lean_Elab_sortDeclLevelParams___closed__0;
                    v___x_1445_ = lean_nat_dec_lt(v___x_1435_, v___x_1443_);
                    if v___x_1445_ == 0 {
                        crate::leanh::lean_dec(v_allUserParams_1413_);
                        v___y_1437_ = v___x_1444_;
                        state = 4;
                        continue;
                    } else {
                        v___x_1446_ = lean_nat_dec_le(v___x_1443_, v___x_1443_);
                        if v___x_1446_ == 0 {
                            if v___x_1445_ == 0 {
                                crate::leanh::lean_dec(v_allUserParams_1413_);
                                v___y_1437_ = v___x_1444_;
                                state = 4;
                                continue;
                            } else {
                                v___x_1447_ = 0usize;
                                v___x_1448_ = lean_usize_of_nat(v___x_1443_);
                                v___x_1449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_1413_, v_usedParams_1414_, v___x_1447_, v___x_1448_, v___x_1444_);
                                crate::leanh::lean_dec(v_allUserParams_1413_);
                                v___y_1437_ = v___x_1449_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___x_1450_ = 0usize;
                            v___x_1451_ = lean_usize_of_nat(v___x_1443_);
                            v___x_1452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_sortDeclLevelParams_spec__5(v_allUserParams_1413_, v_usedParams_1414_, v___x_1450_, v___x_1451_, v___x_1444_);
                            crate::leanh::lean_dec(v_allUserParams_1413_);
                            v___y_1437_ = v___x_1452_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_allUserParams_1413_);
                    v_val_1453_ = crate::leanh::lean_ctor_get(v___x_1415_, 0);
                    v_isSharedCheck_1466_ = (!crate::leanh::lean_is_exclusive(v___x_1415_)) as u8;
                    if v_isSharedCheck_1466_ == 0 {
                        v___x_1455_ = v___x_1415_;
                        v_isShared_1456_ = v_isSharedCheck_1466_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1453_);
                        crate::leanh::lean_dec(v___x_1415_);
                        v___x_1455_ = crate::leanh::lean_box(0);
                        v_isShared_1456_ = v_isSharedCheck_1466_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1420_ = lean_array_to_list(v___y_1419_);
                v___x_1421_ = l_List_appendTR___redArg(v_result_1417_, v___x_1420_);
                v___x_1422_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1422_, 0, v___x_1421_);
                return v___x_1422_;
            }
            2 => {
                v___x_1428_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v___y_1425_, v___y_1426_, v___y_1424_, v___y_1427_);
                crate::leanh::lean_dec(v___y_1427_);
                crate::leanh::lean_dec(v___y_1425_);
                v___y_1419_ = v___x_1428_;
                state = 1;
                continue;
            }
            3 => {
                v___x_1434_ = lean_nat_dec_le(v___y_1433_, v___y_1430_);
                if v___x_1434_ == 0 {
                    crate::leanh::lean_dec(v___y_1430_);
                    crate::leanh::lean_inc(v___y_1433_);
                    v___y_1424_ = v___y_1433_;
                    v___y_1425_ = v___y_1431_;
                    v___y_1426_ = v___y_1432_;
                    v___y_1427_ = v___y_1433_;
                    state = 2;
                    continue;
                } else {
                    v___y_1424_ = v___y_1433_;
                    v___y_1425_ = v___y_1431_;
                    v___y_1426_ = v___y_1432_;
                    v___y_1427_ = v___y_1430_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_1438_ = lean_array_get_size(v___y_1437_);
                v___x_1439_ = lean_nat_dec_eq(v___x_1438_, v___x_1435_);
                if v___x_1439_ == 0 {
                    v___x_1440_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1441_ = lean_nat_sub(v___x_1438_, v___x_1440_);
                    v___x_1442_ = lean_nat_dec_le(v___x_1435_, v___x_1441_);
                    if v___x_1442_ == 0 {
                        crate::leanh::lean_inc(v___x_1441_);
                        v___y_1430_ = v___x_1441_;
                        v___y_1431_ = v___x_1438_;
                        v___y_1432_ = v___y_1437_;
                        v___y_1433_ = v___x_1441_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1430_ = v___x_1441_;
                        v___y_1431_ = v___x_1438_;
                        v___y_1432_ = v___y_1437_;
                        v___y_1433_ = v___x_1435_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___y_1419_ = v___y_1437_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_1457_ = l_Lean_Elab_sortDeclLevelParams___closed__1;
                v___x_1458_ = 1;
                v___x_1459_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_val_1453_,
                    v___x_1458_,
                );
                v___x_1460_ = lean_string_append(v___x_1457_, v___x_1459_);
                crate::leanh::lean_dec_ref(v___x_1459_);
                v___x_1461_ = l_Lean_Elab_sortDeclLevelParams___closed__2;
                v___x_1462_ = lean_string_append(v___x_1460_, v___x_1461_);
                if v_isShared_1456_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1455_, 0);
                    crate::leanh::lean_ctor_set(v___x_1455_, 0, v___x_1462_);
                    v___x_1464_ = v___x_1455_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1465_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1462_);
                    v___x_1464_ = v_reuseFailAlloc_1465_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1464_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_sortDeclLevelParams___boxed(
    mut v_scopeParams_1467_: *mut crate::leanh::LeanObject,
    mut v_allUserParams_1468_: *mut crate::leanh::LeanObject,
    mut v_usedParams_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l_Lean_Elab_sortDeclLevelParams(
        v_scopeParams_1467_,
        v_allUserParams_1468_,
        v_usedParams_1469_,
    );
    crate::leanh::lean_dec_ref(v_usedParams_1469_);
    crate::leanh::lean_dec(v_scopeParams_1467_);
    return v_res_1470_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(
    mut v_n_1471_: *mut crate::leanh::LeanObject,
    mut v_as_1472_: *mut crate::leanh::LeanObject,
    mut v_lo_1473_: *mut crate::leanh::LeanObject,
    mut v_hi_1474_: *mut crate::leanh::LeanObject,
    mut v_w_1475_: *mut crate::leanh::LeanObject,
    mut v_hlo_1476_: *mut crate::leanh::LeanObject,
    mut v_hhi_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___redArg(v_n_1471_, v_as_1472_, v_lo_1473_, v_hi_1474_);
    return v___x_1478_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4___boxed(
    mut v_n_1479_: *mut crate::leanh::LeanObject,
    mut v_as_1480_: *mut crate::leanh::LeanObject,
    mut v_lo_1481_: *mut crate::leanh::LeanObject,
    mut v_hi_1482_: *mut crate::leanh::LeanObject,
    mut v_w_1483_: *mut crate::leanh::LeanObject,
    mut v_hlo_1484_: *mut crate::leanh::LeanObject,
    mut v_hhi_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1486_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4(v_n_1479_, v_as_1480_, v_lo_1481_, v_hi_1482_, v_w_1483_, v_hlo_1484_, v_hhi_1485_);
    crate::leanh::lean_dec(v_hi_1482_);
    crate::leanh::lean_dec(v_n_1479_);
    return v_res_1486_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(
    mut v_n_1487_: *mut crate::leanh::LeanObject,
    mut v_lo_1488_: *mut crate::leanh::LeanObject,
    mut v_hi_1489_: *mut crate::leanh::LeanObject,
    mut v_hhi_1490_: *mut crate::leanh::LeanObject,
    mut v_pivot_1491_: *mut crate::leanh::LeanObject,
    mut v_as_1492_: *mut crate::leanh::LeanObject,
    mut v_i_1493_: *mut crate::leanh::LeanObject,
    mut v_k_1494_: *mut crate::leanh::LeanObject,
    mut v_ilo_1495_: *mut crate::leanh::LeanObject,
    mut v_ik_1496_: *mut crate::leanh::LeanObject,
    mut v_w_1497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1498_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___redArg(v_hi_1489_, v_pivot_1491_, v_as_1492_, v_i_1493_, v_k_1494_);
    return v___x_1498_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5___boxed(
    mut v_n_1499_: *mut crate::leanh::LeanObject,
    mut v_lo_1500_: *mut crate::leanh::LeanObject,
    mut v_hi_1501_: *mut crate::leanh::LeanObject,
    mut v_hhi_1502_: *mut crate::leanh::LeanObject,
    mut v_pivot_1503_: *mut crate::leanh::LeanObject,
    mut v_as_1504_: *mut crate::leanh::LeanObject,
    mut v_i_1505_: *mut crate::leanh::LeanObject,
    mut v_k_1506_: *mut crate::leanh::LeanObject,
    mut v_ilo_1507_: *mut crate::leanh::LeanObject,
    mut v_ik_1508_: *mut crate::leanh::LeanObject,
    mut v_w_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1510_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Elab_sortDeclLevelParams_spec__4_spec__5(v_n_1499_, v_lo_1500_, v_hi_1501_, v_hhi_1502_, v_pivot_1503_, v_as_1504_, v_i_1505_, v_k_1506_, v_ilo_1507_, v_ik_1508_, v_w_1509_);
    crate::leanh::lean_dec(v_pivot_1503_);
    crate::leanh::lean_dec(v_hi_1501_);
    crate::leanh::lean_dec(v_lo_1500_);
    crate::leanh::lean_dec(v_n_1499_);
    return v_res_1510_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_DeclUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Check(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_DeclUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_DeclUtil(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Check(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Parser_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeclUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_DeclUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_DeclUtil(builtin);
}
