// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.Internalize
// Imports: Lean.Meta.Tactic.Grind.AC.Util Lean.Meta.Tactic.Grind.AC.DenoteExpr
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_lt, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::GetElem::l_outOfBounds___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_get_x21___redArg, l_Lean_PersistentArray_push___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFn_x21, l_Lean_Expr_isApp, l_Lean_instInhabitedExpr, l_Lean_mkAppB,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::DenoteExpr::{
    initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Types::l_Lean_Meta_Grind_AC_acExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::AC::Util::{
    initialize_Lean_Meta_Tactic_Grind_AC_Util, l_Lean_Meta_Grind_AC_ACM_getStruct,
    l_Lean_Meta_Grind_AC_addTermOpId___redArg, l_Lean_Meta_Grind_AC_getOpId_x3f,
    l_Lean_Meta_Grind_AC_isOp_x3f, l_Lean_Meta_Grind_AC_mkVar,
    l_Lean_Meta_Grind_AC_modifyStruct___redArg, runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg, l_Lean_Meta_Grind_getConfig___redArg,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0:
    f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_internalize___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_internalize___closed__1_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [97, 99, 0],
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_internalize___closed__2_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 110, 116, 101, 114, 110, 97, 108, 105, 122, 101, 0],
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_AC_internalize___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__0_value)
                as *mut leanh::LeanObject,
            15947788021050471391 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_AC_internalize___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__1_value)
                as *mut leanh::LeanObject,
            879949681028799497 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_AC_internalize___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__2_value)
                as *mut leanh::LeanObject,
            4658627966637684372 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_internalize___closed__4_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_Grind_AC_internalize___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_AC_internalize___closed__5_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__4_value)
                as *mut leanh::LeanObject,
            14231257465488249300 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_internalize___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_internalize___closed__7_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [91, 0],
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_internalize___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_AC_internalize___closed__9_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [93, 32, 0],
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_AC_internalize___closed__9_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_AC_internalize___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_AC_internalize___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(
    mut v_parent_x3f_847_: *mut leanh::LeanObject,
    mut v_op_848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_853_: u8 = 0;
    let mut v___y_855_: u8 = 0;
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: u8 = 0;
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: u8 = 0;
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut v___x_871_: u8 = 0;
    let mut v___x_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_parent_x3f_847_) == 1 {
                    v_val_850_ = leanh::lean_ctor_get(v_parent_x3f_847_, 0);
                    v_isSharedCheck_870_ =
                        (!leanh::lean_is_exclusive(v_parent_x3f_847_)) as u8;
                    if v_isSharedCheck_870_ == 0 {
                        v___x_852_ = v_parent_x3f_847_;
                        v_isShared_853_ = v_isSharedCheck_870_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_850_);
                        leanh::lean_dec(v_parent_x3f_847_);
                        v___x_852_ = leanh::lean_box(0);
                        v_isShared_853_ = v_isSharedCheck_870_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_parent_x3f_847_);
                    v___x_871_ = 0;
                    v___x_872_ = leanh::lean_box((v___x_871_) as usize);
                    v___x_873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_873_, 0, v___x_872_);
                    return v___x_873_;
                }
            }
            1 => {
                v___x_867_ = l_Lean_Expr_isApp(v_val_850_);
                if v___x_867_ == 0 {
                    v___y_855_ = v___x_867_;
                    state = 2;
                    continue;
                } else {
                    v___x_868_ = l_Lean_Expr_appFn_x21(v_val_850_);
                    v___x_869_ = l_Lean_Expr_isApp(v___x_868_);
                    leanh::lean_dec_ref(v___x_868_);
                    v___y_855_ = v___x_869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_855_ == 0 {
                    leanh::lean_dec(v_val_850_);
                    v___x_856_ = leanh::lean_box((v___y_855_) as usize);
                    if v_isShared_853_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_852_, 0);
                        leanh::lean_ctor_set(v___x_852_, 0, v___x_856_);
                        v___x_858_ = v___x_852_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_859_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
                        v___x_858_ = v_reuseFailAlloc_859_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_860_ = l_Lean_Expr_appFn_x21(v_val_850_);
                    leanh::lean_dec(v_val_850_);
                    v___x_861_ = l_Lean_Expr_appFn_x21(v___x_860_);
                    leanh::lean_dec_ref(v___x_860_);
                    v___x_862_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v___x_861_, v_op_848_,
                        );
                    leanh::lean_dec_ref(v___x_861_);
                    v___x_863_ = leanh::lean_box((v___x_862_) as usize);
                    if v_isShared_853_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_852_, 0);
                        leanh::lean_ctor_set(v___x_852_, 0, v___x_863_);
                        v___x_865_ = v___x_852_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_866_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_863_);
                        v___x_865_ = v_reuseFailAlloc_866_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_858_;
            }
            4 => {
                return v___x_865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg___boxed(
    mut v_parent_x3f_874_: *mut leanh::LeanObject,
    mut v_op_875_: *mut leanh::LeanObject,
    mut v_a_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_877_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_874_, v_op_875_);
    leanh::lean_dec_ref(v_op_875_);
    return v_res_877_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(
    mut v_parent_x3f_878_: *mut leanh::LeanObject,
    mut v_op_879_: *mut leanh::LeanObject,
    mut v_a_880_: *mut leanh::LeanObject,
    mut v_a_881_: *mut leanh::LeanObject,
    mut v_a_882_: *mut leanh::LeanObject,
    mut v_a_883_: *mut leanh::LeanObject,
    mut v_a_884_: *mut leanh::LeanObject,
    mut v_a_885_: *mut leanh::LeanObject,
    mut v_a_886_: *mut leanh::LeanObject,
    mut v_a_887_: *mut leanh::LeanObject,
    mut v_a_888_: *mut leanh::LeanObject,
    mut v_a_889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_891_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_878_, v_op_879_);
    return v___x_891_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___boxed(
    mut v_parent_x3f_892_: *mut leanh::LeanObject,
    mut v_op_893_: *mut leanh::LeanObject,
    mut v_a_894_: *mut leanh::LeanObject,
    mut v_a_895_: *mut leanh::LeanObject,
    mut v_a_896_: *mut leanh::LeanObject,
    mut v_a_897_: *mut leanh::LeanObject,
    mut v_a_898_: *mut leanh::LeanObject,
    mut v_a_899_: *mut leanh::LeanObject,
    mut v_a_900_: *mut leanh::LeanObject,
    mut v_a_901_: *mut leanh::LeanObject,
    mut v_a_902_: *mut leanh::LeanObject,
    mut v_a_903_: *mut leanh::LeanObject,
    mut v_a_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_905_ =
        l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp(
            v_parent_x3f_892_,
            v_op_893_,
            v_a_894_,
            v_a_895_,
            v_a_896_,
            v_a_897_,
            v_a_898_,
            v_a_899_,
            v_a_900_,
            v_a_901_,
            v_a_902_,
            v_a_903_,
        );
    leanh::lean_dec(v_a_903_);
    leanh::lean_dec_ref(v_a_902_);
    leanh::lean_dec(v_a_901_);
    leanh::lean_dec_ref(v_a_900_);
    leanh::lean_dec(v_a_899_);
    leanh::lean_dec_ref(v_a_898_);
    leanh::lean_dec(v_a_897_);
    leanh::lean_dec_ref(v_a_896_);
    leanh::lean_dec(v_a_895_);
    leanh::lean_dec(v_a_894_);
    leanh::lean_dec_ref(v_op_893_);
    return v_res_905_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_reify(
    mut v_e_906_: *mut leanh::LeanObject,
    mut v_a_907_: *mut leanh::LeanObject,
    mut v_a_908_: *mut leanh::LeanObject,
    mut v_a_909_: *mut leanh::LeanObject,
    mut v_a_910_: *mut leanh::LeanObject,
    mut v_a_911_: *mut leanh::LeanObject,
    mut v_a_912_: *mut leanh::LeanObject,
    mut v_a_913_: *mut leanh::LeanObject,
    mut v_a_914_: *mut leanh::LeanObject,
    mut v_a_915_: *mut leanh::LeanObject,
    mut v_a_916_: *mut leanh::LeanObject,
    mut v_a_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_926_: u8 = 0;
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_933_: u8 = 0;
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_940_: u8 = 0;
    let mut v_isSharedCheck_941_: u8 = 0;
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut v_a_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_955_: u8 = 0;
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_959_: u8 = 0;
    let mut v_a_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_963_: u8 = 0;
    let mut v___x_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_919_ = l_Lean_Meta_Grind_AC_isOp_x3f(
                    v_e_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_,
                    v_a_914_, v_a_915_, v_a_916_, v_a_917_,
                );
                if leanh::lean_obj_tag(v___x_919_) == 0 {
                    v_a_920_ = leanh::lean_ctor_get(v___x_919_, 0);
                    leanh::lean_inc(v_a_920_);
                    leanh::lean_dec_ref_known(v___x_919_, 1);
                    if leanh::lean_obj_tag(v_a_920_) == 1 {
                        leanh::lean_dec_ref(v_e_906_);
                        v_val_921_ = leanh::lean_ctor_get(v_a_920_, 0);
                        leanh::lean_inc(v_val_921_);
                        leanh::lean_dec_ref_known(v_a_920_, 1);
                        v_fst_922_ = leanh::lean_ctor_get(v_val_921_, 0);
                        v_snd_923_ = leanh::lean_ctor_get(v_val_921_, 1);
                        v_isSharedCheck_941_ = (!leanh::lean_is_exclusive(v_val_921_)) as u8;
                        if v_isSharedCheck_941_ == 0 {
                            v___x_925_ = v_val_921_;
                            v_isShared_926_ = v_isSharedCheck_941_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_923_);
                            leanh::lean_inc(v_fst_922_);
                            leanh::lean_dec(v_val_921_);
                            v___x_925_ = leanh::lean_box(0);
                            v_isShared_926_ = v_isSharedCheck_941_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_920_);
                        v___x_942_ = l_Lean_Meta_Grind_AC_mkVar(
                            v_e_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_,
                            v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_,
                        );
                        if leanh::lean_obj_tag(v___x_942_) == 0 {
                            v_a_943_ = leanh::lean_ctor_get(v___x_942_, 0);
                            v_isSharedCheck_951_ =
                                (!leanh::lean_is_exclusive(v___x_942_)) as u8;
                            if v_isSharedCheck_951_ == 0 {
                                v___x_945_ = v___x_942_;
                                v_isShared_946_ = v_isSharedCheck_951_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_943_);
                                leanh::lean_dec(v___x_942_);
                                v___x_945_ = leanh::lean_box(0);
                                v_isShared_946_ = v_isSharedCheck_951_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_952_ = leanh::lean_ctor_get(v___x_942_, 0);
                            v_isSharedCheck_959_ =
                                (!leanh::lean_is_exclusive(v___x_942_)) as u8;
                            if v_isSharedCheck_959_ == 0 {
                                v___x_954_ = v___x_942_;
                                v_isShared_955_ = v_isSharedCheck_959_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_952_);
                                leanh::lean_dec(v___x_942_);
                                v___x_954_ = leanh::lean_box(0);
                                v_isShared_955_ = v_isSharedCheck_959_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_e_906_);
                    v_a_960_ = leanh::lean_ctor_get(v___x_919_, 0);
                    v_isSharedCheck_967_ = (!leanh::lean_is_exclusive(v___x_919_)) as u8;
                    if v_isSharedCheck_967_ == 0 {
                        v___x_962_ = v___x_919_;
                        v_isShared_963_ = v_isSharedCheck_967_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_960_);
                        leanh::lean_dec(v___x_919_);
                        v___x_962_ = leanh::lean_box(0);
                        v_isShared_963_ = v_isSharedCheck_967_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_927_ = l_Lean_Meta_Grind_AC_reify(
                    v_fst_922_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_,
                    v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_,
                );
                if leanh::lean_obj_tag(v___x_927_) == 0 {
                    v_a_928_ = leanh::lean_ctor_get(v___x_927_, 0);
                    leanh::lean_inc(v_a_928_);
                    leanh::lean_dec_ref_known(v___x_927_, 1);
                    v___x_929_ = l_Lean_Meta_Grind_AC_reify(
                        v_snd_923_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_,
                        v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_,
                    );
                    if leanh::lean_obj_tag(v___x_929_) == 0 {
                        v_a_930_ = leanh::lean_ctor_get(v___x_929_, 0);
                        v_isSharedCheck_940_ = (!leanh::lean_is_exclusive(v___x_929_)) as u8;
                        if v_isSharedCheck_940_ == 0 {
                            v___x_932_ = v___x_929_;
                            v_isShared_933_ = v_isSharedCheck_940_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_930_);
                            leanh::lean_dec(v___x_929_);
                            v___x_932_ = leanh::lean_box(0);
                            v_isShared_933_ = v_isSharedCheck_940_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_928_);
                        leanh::lean_del_object(v___x_925_);
                        return v___x_929_;
                    }
                } else {
                    leanh::lean_del_object(v___x_925_);
                    leanh::lean_dec(v_snd_923_);
                    return v___x_927_;
                }
            }
            2 => {
                if v_isShared_926_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_925_, 1);
                    leanh::lean_ctor_set(v___x_925_, 1, v_a_930_);
                    leanh::lean_ctor_set(v___x_925_, 0, v_a_928_);
                    v___x_935_ = v___x_925_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_939_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_928_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_939_, 1, v_a_930_);
                    v___x_935_ = v_reuseFailAlloc_939_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_933_ == 0 {
                    leanh::lean_ctor_set(v___x_932_, 0, v___x_935_);
                    v___x_937_ = v___x_932_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_938_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
                    v___x_937_ = v_reuseFailAlloc_938_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_937_;
            }
            5 => {
                v___x_947_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_947_, 0, v_a_943_);
                if v_isShared_946_ == 0 {
                    leanh::lean_ctor_set(v___x_945_, 0, v___x_947_);
                    v___x_949_ = v___x_945_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_950_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
                    v___x_949_ = v_reuseFailAlloc_950_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_949_;
            }
            7 => {
                if v_isShared_955_ == 0 {
                    v___x_957_ = v___x_954_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_958_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
                    v___x_957_ = v_reuseFailAlloc_958_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_957_;
            }
            9 => {
                if v_isShared_963_ == 0 {
                    v___x_965_ = v___x_962_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_966_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_966_, 0, v_a_960_);
                    v___x_965_ = v_reuseFailAlloc_966_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_reify___boxed(
    mut v_e_968_: *mut leanh::LeanObject,
    mut v_a_969_: *mut leanh::LeanObject,
    mut v_a_970_: *mut leanh::LeanObject,
    mut v_a_971_: *mut leanh::LeanObject,
    mut v_a_972_: *mut leanh::LeanObject,
    mut v_a_973_: *mut leanh::LeanObject,
    mut v_a_974_: *mut leanh::LeanObject,
    mut v_a_975_: *mut leanh::LeanObject,
    mut v_a_976_: *mut leanh::LeanObject,
    mut v_a_977_: *mut leanh::LeanObject,
    mut v_a_978_: *mut leanh::LeanObject,
    mut v_a_979_: *mut leanh::LeanObject,
    mut v_a_980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_981_ = l_Lean_Meta_Grind_AC_reify(
        v_e_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_, v_a_975_, v_a_976_,
        v_a_977_, v_a_978_, v_a_979_,
    );
    leanh::lean_dec(v_a_979_);
    leanh::lean_dec_ref(v_a_978_);
    leanh::lean_dec(v_a_977_);
    leanh::lean_dec_ref(v_a_976_);
    leanh::lean_dec(v_a_975_);
    leanh::lean_dec_ref(v_a_974_);
    leanh::lean_dec(v_a_973_);
    leanh::lean_dec_ref(v_a_972_);
    leanh::lean_dec(v_a_971_);
    leanh::lean_dec(v_a_970_);
    leanh::lean_dec(v_a_969_);
    return v_res_981_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(
    mut v_x_982_: *mut leanh::LeanObject,
    mut v_x_983_: *mut leanh::LeanObject,
    mut v_x_984_: *mut leanh::LeanObject,
    mut v_x_985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: u8 = 0;
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: u8 = 0;
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1011_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_986_ = leanh::lean_ctor_get(v_x_982_, 0);
                v_vs_987_ = leanh::lean_ctor_get(v_x_982_, 1);
                v_isSharedCheck_1011_ = (!leanh::lean_is_exclusive(v_x_982_)) as u8;
                if v_isSharedCheck_1011_ == 0 {
                    v___x_989_ = v_x_982_;
                    v_isShared_990_ = v_isSharedCheck_1011_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_987_);
                    leanh::lean_inc(v_ks_986_);
                    leanh::lean_dec(v_x_982_);
                    v___x_989_ = leanh::lean_box(0);
                    v_isShared_990_ = v_isSharedCheck_1011_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_991_ = lean_array_get_size(v_ks_986_);
                v___x_992_ = lean_nat_dec_lt(v_x_983_, v___x_991_);
                if v___x_992_ == 0 {
                    leanh::lean_dec(v_x_983_);
                    v___x_993_ = lean_array_push(v_ks_986_, v_x_984_);
                    v___x_994_ = lean_array_push(v_vs_987_, v_x_985_);
                    if v_isShared_990_ == 0 {
                        leanh::lean_ctor_set(v___x_989_, 1, v___x_994_);
                        leanh::lean_ctor_set(v___x_989_, 0, v___x_993_);
                        v___x_996_ = v___x_989_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_997_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_993_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_997_, 1, v___x_994_);
                        v___x_996_ = v_reuseFailAlloc_997_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_998_ = lean_array_fget_borrowed(v_ks_986_, v_x_983_);
                    v___x_999_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_984_,
                            v_k_x27_998_,
                        );
                    if v___x_999_ == 0 {
                        if v_isShared_990_ == 0 {
                            v___x_1001_ = v___x_989_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1005_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_ks_986_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_vs_987_);
                            v___x_1001_ = v_reuseFailAlloc_1005_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1006_ = lean_array_fset(v_ks_986_, v_x_983_, v_x_984_);
                        v___x_1007_ = lean_array_fset(v_vs_987_, v_x_983_, v_x_985_);
                        leanh::lean_dec(v_x_983_);
                        if v_isShared_990_ == 0 {
                            leanh::lean_ctor_set(v___x_989_, 1, v___x_1007_);
                            leanh::lean_ctor_set(v___x_989_, 0, v___x_1006_);
                            v___x_1009_ = v___x_989_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1010_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1006_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1010_, 1, v___x_1007_);
                            v___x_1009_ = v_reuseFailAlloc_1010_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_996_;
            }
            3 => {
                v___x_1002_ = leanh::lean_unsigned_to_nat(1);
                v___x_1003_ = lean_nat_add(v_x_983_, v___x_1002_);
                leanh::lean_dec(v_x_983_);
                v_x_982_ = v___x_1001_;
                v_x_983_ = v___x_1003_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(
    mut v_n_1012_: *mut leanh::LeanObject,
    mut v_k_1013_: *mut leanh::LeanObject,
    mut v_v_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1015_ = leanh::lean_unsigned_to_nat(0);
    v___x_1016_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_n_1012_, v___x_1015_, v_k_1013_, v_v_1014_);
    return v___x_1016_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_1017_: usize = 0;
    let mut v___x_1018_: usize = 0;
    let mut v___x_1019_: usize = 0;
    v___x_1017_ = 5usize;
    v___x_1018_ = 1usize;
    v___x_1019_ = lean_usize_shift_left(v___x_1018_, v___x_1017_);
    return v___x_1019_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_1020_: usize = 0;
    let mut v___x_1021_: usize = 0;
    let mut v___x_1022_: usize = 0;
    v___x_1020_ = 1usize;
    v___x_1021_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__0);
    v___x_1022_ = lean_usize_sub(v___x_1021_, v___x_1020_);
    return v___x_1022_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1023_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1023_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(
    mut v_x_1024_: *mut leanh::LeanObject,
    mut v_x_1025_: usize,
    mut v_x_1026_: usize,
    mut v_x_1027_: *mut leanh::LeanObject,
    mut v_x_1028_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: usize = 0;
    let mut v___x_1031_: usize = 0;
    let mut v___x_1032_: usize = 0;
    let mut v___x_1033_: usize = 0;
    let mut v_j_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: u8 = 0;
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v_v_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1053_: u8 = 0;
    let mut v___x_1054_: u8 = 0;
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_node_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v___x_1065_: usize = 0;
    let mut v___x_1066_: usize = 0;
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1071_: u8 = 0;
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut v_unused_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1079_: u8 = 0;
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1084_: u8 = 0;
    let mut v_ks_1085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: usize = 0;
    let mut v___x_1091_: u8 = 0;
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: u8 = 0;
    let mut v_reuseFailAlloc_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1096_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1024_) == 0 {
                    v_es_1029_ = leanh::lean_ctor_get(v_x_1024_, 0);
                    v___x_1030_ = 5usize;
                    v___x_1031_ = 1usize;
                    v___x_1032_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1);
                    v___x_1033_ = lean_usize_land(v_x_1025_, v___x_1032_);
                    v_j_1034_ = lean_usize_to_nat(v___x_1033_);
                    v___x_1035_ = lean_array_get_size(v_es_1029_);
                    v___x_1036_ = lean_nat_dec_lt(v_j_1034_, v___x_1035_);
                    if v___x_1036_ == 0 {
                        leanh::lean_dec(v_j_1034_);
                        leanh::lean_dec(v_x_1028_);
                        leanh::lean_dec_ref(v_x_1027_);
                        return v_x_1024_;
                    } else {
                        leanh::lean_inc_ref(v_es_1029_);
                        v_isSharedCheck_1073_ = (!leanh::lean_is_exclusive(v_x_1024_)) as u8;
                        if v_isSharedCheck_1073_ == 0 {
                            v_unused_1074_ = leanh::lean_ctor_get(v_x_1024_, 0);
                            leanh::lean_dec(v_unused_1074_);
                            v___x_1038_ = v_x_1024_;
                            v_isShared_1039_ = v_isSharedCheck_1073_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1024_);
                            v___x_1038_ = leanh::lean_box(0);
                            v_isShared_1039_ = v_isSharedCheck_1073_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1075_ = leanh::lean_ctor_get(v_x_1024_, 0);
                    v_vs_1076_ = leanh::lean_ctor_get(v_x_1024_, 1);
                    v_isSharedCheck_1096_ = (!leanh::lean_is_exclusive(v_x_1024_)) as u8;
                    if v_isSharedCheck_1096_ == 0 {
                        v___x_1078_ = v_x_1024_;
                        v_isShared_1079_ = v_isSharedCheck_1096_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1076_);
                        leanh::lean_inc(v_ks_1075_);
                        leanh::lean_dec(v_x_1024_);
                        v___x_1078_ = leanh::lean_box(0);
                        v_isShared_1079_ = v_isSharedCheck_1096_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1040_ = lean_array_fget(v_es_1029_, v_j_1034_);
                v___x_1041_ = leanh::lean_box(0);
                v_xs_x27_1042_ = lean_array_fset(v_es_1029_, v_j_1034_, v___x_1041_);
                match leanh::lean_obj_tag(v_v_1040_) {
                    0 => {
                        v_key_1049_ = leanh::lean_ctor_get(v_v_1040_, 0);
                        v_val_1050_ = leanh::lean_ctor_get(v_v_1040_, 1);
                        v_isSharedCheck_1060_ = (!leanh::lean_is_exclusive(v_v_1040_)) as u8;
                        if v_isSharedCheck_1060_ == 0 {
                            v___x_1052_ = v_v_1040_;
                            v_isShared_1053_ = v_isSharedCheck_1060_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1050_);
                            leanh::lean_inc(v_key_1049_);
                            leanh::lean_dec(v_v_1040_);
                            v___x_1052_ = leanh::lean_box(0);
                            v_isShared_1053_ = v_isSharedCheck_1060_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1061_ = leanh::lean_ctor_get(v_v_1040_, 0);
                        v_isSharedCheck_1071_ = (!leanh::lean_is_exclusive(v_v_1040_)) as u8;
                        if v_isSharedCheck_1071_ == 0 {
                            v___x_1063_ = v_v_1040_;
                            v_isShared_1064_ = v_isSharedCheck_1071_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1061_);
                            leanh::lean_dec(v_v_1040_);
                            v___x_1063_ = leanh::lean_box(0);
                            v_isShared_1064_ = v_isSharedCheck_1071_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1072_, 0, v_x_1027_);
                        leanh::lean_ctor_set(v___x_1072_, 1, v_x_1028_);
                        v___y_1044_ = v___x_1072_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1045_ = lean_array_fset(v_xs_x27_1042_, v_j_1034_, v___y_1044_);
                leanh::lean_dec(v_j_1034_);
                if v_isShared_1039_ == 0 {
                    leanh::lean_ctor_set(v___x_1038_, 0, v___x_1045_);
                    v___x_1047_ = v___x_1038_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1048_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
                    v___x_1047_ = v_reuseFailAlloc_1048_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1047_;
            }
            4 => {
                v___x_1054_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1027_,
                        v_key_1049_,
                    );
                if v___x_1054_ == 0 {
                    leanh::lean_del_object(v___x_1052_);
                    v___x_1055_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1049_,
                        v_val_1050_,
                        v_x_1027_,
                        v_x_1028_,
                    );
                    v___x_1056_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1056_, 0, v___x_1055_);
                    v___y_1044_ = v___x_1056_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1050_);
                    leanh::lean_dec(v_key_1049_);
                    if v_isShared_1053_ == 0 {
                        leanh::lean_ctor_set(v___x_1052_, 1, v_x_1028_);
                        leanh::lean_ctor_set(v___x_1052_, 0, v_x_1027_);
                        v___x_1058_ = v___x_1052_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1059_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_x_1027_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 1, v_x_1028_);
                        v___x_1058_ = v_reuseFailAlloc_1059_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1044_ = v___x_1058_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1065_ = lean_usize_shift_right(v_x_1025_, v___x_1030_);
                v___x_1066_ = lean_usize_add(v_x_1026_, v___x_1031_);
                v___x_1067_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_node_1061_, v___x_1065_, v___x_1066_, v_x_1027_, v_x_1028_);
                if v_isShared_1064_ == 0 {
                    leanh::lean_ctor_set(v___x_1063_, 0, v___x_1067_);
                    v___x_1069_ = v___x_1063_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1070_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1067_);
                    v___x_1069_ = v_reuseFailAlloc_1070_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1044_ = v___x_1069_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1079_ == 0 {
                    v___x_1081_ = v___x_1078_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1095_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_ks_1075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_vs_1076_);
                    v___x_1081_ = v_reuseFailAlloc_1095_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1082_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v___x_1081_, v_x_1027_, v_x_1028_);
                v___x_1090_ = 7usize;
                v___x_1091_ = lean_usize_dec_le(v___x_1090_, v_x_1026_);
                if v___x_1091_ == 0 {
                    v___x_1092_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1082_);
                    v___x_1093_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1094_ = lean_nat_dec_lt(v___x_1092_, v___x_1093_);
                    leanh::lean_dec(v___x_1092_);
                    v___y_1084_ = v___x_1094_;
                    state = 10;
                    continue;
                } else {
                    v___y_1084_ = v___x_1091_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1084_ == 0 {
                    v_ks_1085_ = leanh::lean_ctor_get(v_newNode_1082_, 0);
                    leanh::lean_inc_ref(v_ks_1085_);
                    v_vs_1086_ = leanh::lean_ctor_get(v_newNode_1082_, 1);
                    leanh::lean_inc_ref(v_vs_1086_);
                    leanh::lean_dec_ref(v_newNode_1082_);
                    v___x_1087_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1088_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__2);
                    v___x_1089_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_x_1026_, v_ks_1085_, v_vs_1086_, v___x_1087_, v___x_1088_);
                    leanh::lean_dec_ref(v_vs_1086_);
                    leanh::lean_dec_ref(v_ks_1085_);
                    return v___x_1089_;
                } else {
                    return v_newNode_1082_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(
    mut v_depth_1097_: usize,
    mut v_keys_1098_: *mut leanh::LeanObject,
    mut v_vals_1099_: *mut leanh::LeanObject,
    mut v_i_1100_: *mut leanh::LeanObject,
    mut v_entries_1101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: u8 = 0;
    let mut v_k_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: u64 = 0;
    let mut v_h_1107_: usize = 0;
    let mut v___x_1108_: usize = 0;
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: usize = 0;
    let mut v___x_1111_: usize = 0;
    let mut v___x_1112_: usize = 0;
    let mut v_h_1113_: usize = 0;
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1102_ = lean_array_get_size(v_keys_1098_);
                v___x_1103_ = lean_nat_dec_lt(v_i_1100_, v___x_1102_);
                if v___x_1103_ == 0 {
                    leanh::lean_dec(v_i_1100_);
                    return v_entries_1101_;
                } else {
                    v_k_1104_ = lean_array_fget_borrowed(v_keys_1098_, v_i_1100_);
                    v_v_1105_ = lean_array_fget_borrowed(v_vals_1099_, v_i_1100_);
                    v___x_1106_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1104_);
                    v_h_1107_ = lean_uint64_to_usize(v___x_1106_);
                    v___x_1108_ = 5usize;
                    v___x_1109_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1110_ = 1usize;
                    v___x_1111_ = lean_usize_sub(v_depth_1097_, v___x_1110_);
                    v___x_1112_ = lean_usize_mul(v___x_1108_, v___x_1111_);
                    v_h_1113_ = lean_usize_shift_right(v_h_1107_, v___x_1112_);
                    v___x_1114_ = lean_nat_add(v_i_1100_, v___x_1109_);
                    leanh::lean_dec(v_i_1100_);
                    leanh::lean_inc(v_v_1105_);
                    leanh::lean_inc(v_k_1104_);
                    v___x_1115_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_entries_1101_, v_h_1113_, v_depth_1097_, v_k_1104_, v_v_1105_);
                    v_i_1100_ = v___x_1114_;
                    v_entries_1101_ = v___x_1115_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_1117_: *mut leanh::LeanObject,
    mut v_keys_1118_: *mut leanh::LeanObject,
    mut v_vals_1119_: *mut leanh::LeanObject,
    mut v_i_1120_: *mut leanh::LeanObject,
    mut v_entries_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1122_: usize = 0;
    let mut v_res_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1122_ = leanh::lean_unbox_usize(v_depth_1117_);
    leanh::lean_dec(v_depth_1117_);
    v_res_1123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1122_, v_keys_1118_, v_vals_1119_, v_i_1120_, v_entries_1121_);
    leanh::lean_dec_ref(v_vals_1119_);
    leanh::lean_dec_ref(v_keys_1118_);
    return v_res_1123_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___boxed(
    mut v_x_1124_: *mut leanh::LeanObject,
    mut v_x_1125_: *mut leanh::LeanObject,
    mut v_x_1126_: *mut leanh::LeanObject,
    mut v_x_1127_: *mut leanh::LeanObject,
    mut v_x_1128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_55673__boxed_1129_: usize = 0;
    let mut v_x_55674__boxed_1130_: usize = 0;
    let mut v_res_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_55673__boxed_1129_ = leanh::lean_unbox_usize(v_x_1125_);
    leanh::lean_dec(v_x_1125_);
    v_x_55674__boxed_1130_ = leanh::lean_unbox_usize(v_x_1126_);
    leanh::lean_dec(v_x_1126_);
    v_res_1131_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_1124_, v_x_55673__boxed_1129_, v_x_55674__boxed_1130_, v_x_1127_, v_x_1128_);
    return v_res_1131_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(
    mut v_x_1132_: *mut leanh::LeanObject,
    mut v_x_1133_: *mut leanh::LeanObject,
    mut v_x_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1135_: u64 = 0;
    let mut v___x_1136_: usize = 0;
    let mut v___x_1137_: usize = 0;
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1135_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1133_);
    v___x_1136_ = lean_uint64_to_usize(v___x_1135_);
    v___x_1137_ = 1usize;
    v___x_1138_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_1132_, v___x_1136_, v___x_1137_, v_x_1133_, v_x_1134_);
    return v___x_1138_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_internalize___lam__0(
    mut v_e_1139_: *mut leanh::LeanObject,
    mut v_a_1140_: *mut leanh::LeanObject,
    mut v_ac_1141_: u8,
    mut v_s_1142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_op_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_x3f_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assocInst_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_idempotentInst_x3f_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_commInst_x3f_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutralInst_x3f_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextId_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denote_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_denoteEntries_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_queue_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basis_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1162_: u8 = 0;
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_1143_ = leanh::lean_ctor_get(v_s_1142_, 0);
                v_type_1144_ = leanh::lean_ctor_get(v_s_1142_, 1);
                v_u_1145_ = leanh::lean_ctor_get(v_s_1142_, 2);
                v_op_1146_ = leanh::lean_ctor_get(v_s_1142_, 3);
                v_neutral_x3f_1147_ = leanh::lean_ctor_get(v_s_1142_, 4);
                v_assocInst_1148_ = leanh::lean_ctor_get(v_s_1142_, 5);
                v_idempotentInst_x3f_1149_ = leanh::lean_ctor_get(v_s_1142_, 6);
                v_commInst_x3f_1150_ = leanh::lean_ctor_get(v_s_1142_, 7);
                v_neutralInst_x3f_1151_ = leanh::lean_ctor_get(v_s_1142_, 8);
                v_nextId_1152_ = leanh::lean_ctor_get(v_s_1142_, 9);
                v_vars_1153_ = leanh::lean_ctor_get(v_s_1142_, 10);
                v_varMap_1154_ = leanh::lean_ctor_get(v_s_1142_, 11);
                v_denote_1155_ = leanh::lean_ctor_get(v_s_1142_, 12);
                v_denoteEntries_1156_ = leanh::lean_ctor_get(v_s_1142_, 13);
                v_queue_1157_ = leanh::lean_ctor_get(v_s_1142_, 14);
                v_basis_1158_ = leanh::lean_ctor_get(v_s_1142_, 15);
                v_diseqs_1159_ = leanh::lean_ctor_get(v_s_1142_, 16);
                v_isSharedCheck_1169_ = (!leanh::lean_is_exclusive(v_s_1142_)) as u8;
                if v_isSharedCheck_1169_ == 0 {
                    v___x_1161_ = v_s_1142_;
                    v_isShared_1162_ = v_isSharedCheck_1169_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diseqs_1159_);
                    leanh::lean_inc(v_basis_1158_);
                    leanh::lean_inc(v_queue_1157_);
                    leanh::lean_inc(v_denoteEntries_1156_);
                    leanh::lean_inc(v_denote_1155_);
                    leanh::lean_inc(v_varMap_1154_);
                    leanh::lean_inc(v_vars_1153_);
                    leanh::lean_inc(v_nextId_1152_);
                    leanh::lean_inc(v_neutralInst_x3f_1151_);
                    leanh::lean_inc(v_commInst_x3f_1150_);
                    leanh::lean_inc(v_idempotentInst_x3f_1149_);
                    leanh::lean_inc(v_assocInst_1148_);
                    leanh::lean_inc(v_neutral_x3f_1147_);
                    leanh::lean_inc(v_op_1146_);
                    leanh::lean_inc(v_u_1145_);
                    leanh::lean_inc(v_type_1144_);
                    leanh::lean_inc(v_id_1143_);
                    leanh::lean_dec(v_s_1142_);
                    v___x_1161_ = leanh::lean_box(0);
                    v_isShared_1162_ = v_isSharedCheck_1169_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_a_1140_);
                leanh::lean_inc_ref(v_e_1139_);
                v___x_1163_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(v_denote_1155_, v_e_1139_, v_a_1140_);
                v___x_1164_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1164_, 0, v_e_1139_);
                leanh::lean_ctor_set(v___x_1164_, 1, v_a_1140_);
                v___x_1165_ =
                    l_Lean_PersistentArray_push___redArg(v_denoteEntries_1156_, v___x_1164_);
                if v_isShared_1162_ == 0 {
                    leanh::lean_ctor_set(v___x_1161_, 13, v___x_1165_);
                    leanh::lean_ctor_set(v___x_1161_, 12, v___x_1163_);
                    v___x_1167_ = v___x_1161_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = leanh::lean_alloc_ctor(0, 17, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_id_1143_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_type_1144_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_u_1145_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 3, v_op_1146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 4, v_neutral_x3f_1147_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 5, v_assocInst_1148_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1168_,
                        6,
                        v_idempotentInst_x3f_1149_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 7, v_commInst_x3f_1150_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 8, v_neutralInst_x3f_1151_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 9, v_nextId_1152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 10, v_vars_1153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 11, v_varMap_1154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 12, v___x_1163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 13, v___x_1165_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 14, v_queue_1157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 15, v_basis_1158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 16, v_diseqs_1159_);
                    v___x_1167_ = v_reuseFailAlloc_1168_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1167_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 17) as u32,
                    v_ac_1141_,
                );
                return v___x_1167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_internalize___lam__0___boxed(
    mut v_e_1170_: *mut leanh::LeanObject,
    mut v_a_1171_: *mut leanh::LeanObject,
    mut v_ac_1172_: *mut leanh::LeanObject,
    mut v_s_1173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ac_boxed_1174_: u8 = 0;
    let mut v_res_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ac_boxed_1174_ = (leanh::lean_unbox(v_ac_1172_) as u8);
    v_res_1175_ = l_Lean_Meta_Grind_AC_internalize___lam__0(
        v_e_1170_,
        v_a_1171_,
        v_ac_boxed_1174_,
        v_s_1173_,
    );
    return v_res_1175_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(
    mut v_msgData_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
    mut v___y_1179_: *mut leanh::LeanObject,
    mut v___y_1180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = lean_st_ref_get(v___y_1180_);
    v_env_1183_ = leanh::lean_ctor_get(v___x_1182_, 0);
    leanh::lean_inc_ref(v_env_1183_);
    leanh::lean_dec(v___x_1182_);
    v___x_1184_ = lean_st_ref_get(v___y_1178_);
    v_mctx_1185_ = leanh::lean_ctor_get(v___x_1184_, 0);
    leanh::lean_inc_ref(v_mctx_1185_);
    leanh::lean_dec(v___x_1184_);
    v_lctx_1186_ = leanh::lean_ctor_get(v___y_1177_, 2);
    v_options_1187_ = leanh::lean_ctor_get(v___y_1179_, 2);
    leanh::lean_inc_ref(v_options_1187_);
    leanh::lean_inc_ref(v_lctx_1186_);
    v___x_1188_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1188_, 0, v_env_1183_);
    leanh::lean_ctor_set(v___x_1188_, 1, v_mctx_1185_);
    leanh::lean_ctor_set(v___x_1188_, 2, v_lctx_1186_);
    leanh::lean_ctor_set(v___x_1188_, 3, v_options_1187_);
    v___x_1189_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1189_, 0, v___x_1188_);
    leanh::lean_ctor_set(v___x_1189_, 1, v_msgData_1176_);
    v___x_1190_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1190_, 0, v___x_1189_);
    return v___x_1190_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5___boxed(
    mut v_msgData_1191_: *mut leanh::LeanObject,
    mut v___y_1192_: *mut leanh::LeanObject,
    mut v___y_1193_: *mut leanh::LeanObject,
    mut v___y_1194_: *mut leanh::LeanObject,
    mut v___y_1195_: *mut leanh::LeanObject,
    mut v___y_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1197_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msgData_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
    leanh::lean_dec(v___y_1195_);
    leanh::lean_dec_ref(v___y_1194_);
    leanh::lean_dec(v___y_1193_);
    leanh::lean_dec_ref(v___y_1192_);
    return v_res_1197_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0()
-> f64 {
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: f64 = 0.0;
    v___x_1198_ = leanh::lean_unsigned_to_nat(0);
    v___x_1199_ = lean_float_of_nat(v___x_1198_);
    return v___x_1199_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(
    mut v_cls_1203_: *mut leanh::LeanObject,
    mut v_msg_1204_: *mut leanh::LeanObject,
    mut v___y_1205_: *mut leanh::LeanObject,
    mut v___y_1206_: *mut leanh::LeanObject,
    mut v___y_1207_: *mut leanh::LeanObject,
    mut v___y_1208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1215_: u8 = 0;
    let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1228_: u8 = 0;
    let mut v_tid_1229_: u64 = 0;
    let mut v_traces_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1233_: u8 = 0;
    let mut v___x_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: f64 = 0.0;
    let mut v___x_1236_: u8 = 0;
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1254_: u8 = 0;
    let mut v_isSharedCheck_1255_: u8 = 0;
    let mut v_isSharedCheck_1256_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1210_ = leanh::lean_ctor_get(v___y_1207_, 5);
                v___x_1211_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3_spec__5(v_msg_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
                v_a_1212_ = leanh::lean_ctor_get(v___x_1211_, 0);
                v_isSharedCheck_1256_ = (!leanh::lean_is_exclusive(v___x_1211_)) as u8;
                if v_isSharedCheck_1256_ == 0 {
                    v___x_1214_ = v___x_1211_;
                    v_isShared_1215_ = v_isSharedCheck_1256_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1212_);
                    leanh::lean_dec(v___x_1211_);
                    v___x_1214_ = leanh::lean_box(0);
                    v_isShared_1215_ = v_isSharedCheck_1256_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1216_ = lean_st_ref_take(v___y_1208_);
                v_traceState_1217_ = leanh::lean_ctor_get(v___x_1216_, 4);
                v_env_1218_ = leanh::lean_ctor_get(v___x_1216_, 0);
                v_nextMacroScope_1219_ = leanh::lean_ctor_get(v___x_1216_, 1);
                v_ngen_1220_ = leanh::lean_ctor_get(v___x_1216_, 2);
                v_auxDeclNGen_1221_ = leanh::lean_ctor_get(v___x_1216_, 3);
                v_cache_1222_ = leanh::lean_ctor_get(v___x_1216_, 5);
                v_messages_1223_ = leanh::lean_ctor_get(v___x_1216_, 6);
                v_infoState_1224_ = leanh::lean_ctor_get(v___x_1216_, 7);
                v_snapshotTasks_1225_ = leanh::lean_ctor_get(v___x_1216_, 8);
                v_isSharedCheck_1255_ = (!leanh::lean_is_exclusive(v___x_1216_)) as u8;
                if v_isSharedCheck_1255_ == 0 {
                    v___x_1227_ = v___x_1216_;
                    v_isShared_1228_ = v_isSharedCheck_1255_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_1225_);
                    leanh::lean_inc(v_infoState_1224_);
                    leanh::lean_inc(v_messages_1223_);
                    leanh::lean_inc(v_cache_1222_);
                    leanh::lean_inc(v_traceState_1217_);
                    leanh::lean_inc(v_auxDeclNGen_1221_);
                    leanh::lean_inc(v_ngen_1220_);
                    leanh::lean_inc(v_nextMacroScope_1219_);
                    leanh::lean_inc(v_env_1218_);
                    leanh::lean_dec(v___x_1216_);
                    v___x_1227_ = leanh::lean_box(0);
                    v_isShared_1228_ = v_isSharedCheck_1255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1229_ = leanh::lean_ctor_get_uint64(
                    v_traceState_1217_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1230_ = leanh::lean_ctor_get(v_traceState_1217_, 0);
                v_isSharedCheck_1254_ =
                    (!leanh::lean_is_exclusive(v_traceState_1217_)) as u8;
                if v_isSharedCheck_1254_ == 0 {
                    v___x_1232_ = v_traceState_1217_;
                    v_isShared_1233_ = v_isSharedCheck_1254_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_1230_);
                    leanh::lean_dec(v_traceState_1217_);
                    v___x_1232_ = leanh::lean_box(0);
                    v_isShared_1233_ = v_isSharedCheck_1254_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1234_ = leanh::lean_box(0);
                v___x_1235_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__0);
                v___x_1236_ = 0;
                v___x_1237_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__1;
                v___x_1238_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_1238_, 0, v_cls_1203_);
                leanh::lean_ctor_set(v___x_1238_, 1, v___x_1234_);
                leanh::lean_ctor_set(v___x_1238_, 2, v___x_1237_);
                leanh::lean_ctor_set_float(
                    v___x_1238_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1235_,
                );
                leanh::lean_ctor_set_float(
                    v___x_1238_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1235_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1238_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1236_,
                );
                v___x_1239_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___closed__2;
                v___x_1240_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1240_, 0, v___x_1238_);
                leanh::lean_ctor_set(v___x_1240_, 1, v_a_1212_);
                leanh::lean_ctor_set(v___x_1240_, 2, v___x_1239_);
                leanh::lean_inc(v_ref_1210_);
                v___x_1241_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1241_, 0, v_ref_1210_);
                leanh::lean_ctor_set(v___x_1241_, 1, v___x_1240_);
                v___x_1242_ = l_Lean_PersistentArray_push___redArg(v_traces_1230_, v___x_1241_);
                if v_isShared_1233_ == 0 {
                    leanh::lean_ctor_set(v___x_1232_, 0, v___x_1242_);
                    v___x_1244_ = v___x_1232_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1253_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1242_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1253_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_1229_,
                    );
                    v___x_1244_ = v_reuseFailAlloc_1253_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1228_ == 0 {
                    leanh::lean_ctor_set(v___x_1227_, 4, v___x_1244_);
                    v___x_1246_ = v___x_1227_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1252_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_env_1218_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 1, v_nextMacroScope_1219_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 2, v_ngen_1220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 3, v_auxDeclNGen_1221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 4, v___x_1244_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 5, v_cache_1222_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 6, v_messages_1223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 7, v_infoState_1224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1252_, 8, v_snapshotTasks_1225_);
                    v___x_1246_ = v_reuseFailAlloc_1252_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1247_ = lean_st_ref_set(v___y_1208_, v___x_1246_);
                v___x_1248_ = leanh::lean_box(0);
                if v_isShared_1215_ == 0 {
                    leanh::lean_ctor_set(v___x_1214_, 0, v___x_1248_);
                    v___x_1250_ = v___x_1214_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
                    v___x_1250_ = v_reuseFailAlloc_1251_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg___boxed(
    mut v_cls_1257_: *mut leanh::LeanObject,
    mut v_msg_1258_: *mut leanh::LeanObject,
    mut v___y_1259_: *mut leanh::LeanObject,
    mut v___y_1260_: *mut leanh::LeanObject,
    mut v___y_1261_: *mut leanh::LeanObject,
    mut v___y_1262_: *mut leanh::LeanObject,
    mut v___y_1263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1264_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(
        v_cls_1257_,
        v_msg_1258_,
        v___y_1259_,
        v___y_1260_,
        v___y_1261_,
        v___y_1262_,
    );
    leanh::lean_dec(v___y_1262_);
    leanh::lean_dec_ref(v___y_1261_);
    leanh::lean_dec(v___y_1260_);
    leanh::lean_dec_ref(v___y_1259_);
    return v_res_1264_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1265_: *mut leanh::LeanObject,
    mut v_i_1266_: *mut leanh::LeanObject,
    mut v_k_1267_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: u8 = 0;
    let mut v_k_x27_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: u8 = 0;
    let mut v___x_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1268_ = lean_array_get_size(v_keys_1265_);
                v___x_1269_ = lean_nat_dec_lt(v_i_1266_, v___x_1268_);
                if v___x_1269_ == 0 {
                    leanh::lean_dec(v_i_1266_);
                    return v___x_1269_;
                } else {
                    v_k_x27_1270_ = lean_array_fget_borrowed(v_keys_1265_, v_i_1266_);
                    v___x_1271_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1267_,
                            v_k_x27_1270_,
                        );
                    if v___x_1271_ == 0 {
                        v___x_1272_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1273_ = lean_nat_add(v_i_1266_, v___x_1272_);
                        leanh::lean_dec(v_i_1266_);
                        v_i_1266_ = v___x_1273_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_1266_);
                        return v___x_1271_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1275_: *mut leanh::LeanObject,
    mut v_i_1276_: *mut leanh::LeanObject,
    mut v_k_1277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1278_: u8 = 0;
    let mut v_r_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1278_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_1275_, v_i_1276_, v_k_1277_);
    leanh::lean_dec_ref(v_k_1277_);
    leanh::lean_dec_ref(v_keys_1275_);
    v_r_1279_ = leanh::lean_box((v_res_1278_) as usize);
    return v_r_1279_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(
    mut v_x_1280_: *mut leanh::LeanObject,
    mut v_x_1281_: usize,
    mut v_x_1282_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: usize = 0;
    let mut v___x_1286_: usize = 0;
    let mut v___x_1287_: usize = 0;
    let mut v_j_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    let mut v_node_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: usize = 0;
    let mut v___x_1295_: u8 = 0;
    let mut v_ks_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1280_) == 0 {
                    v_es_1283_ = leanh::lean_ctor_get(v_x_1280_, 0);
                    v___x_1284_ = leanh::lean_box(2);
                    v___x_1285_ = 5usize;
                    v___x_1286_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg___closed__1);
                    v___x_1287_ = lean_usize_land(v_x_1281_, v___x_1286_);
                    v_j_1288_ = lean_usize_to_nat(v___x_1287_);
                    v___x_1289_ = lean_array_get_borrowed(v___x_1284_, v_es_1283_, v_j_1288_);
                    leanh::lean_dec(v_j_1288_);
                    match leanh::lean_obj_tag(v___x_1289_) {
                        0 => {
                            v_key_1290_ = leanh::lean_ctor_get(v___x_1289_, 0);
                            v___x_1291_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1282_, v_key_1290_);
                            return v___x_1291_;
                        }
                        1 => {
                            v_node_1292_ = leanh::lean_ctor_get(v___x_1289_, 0);
                            v___x_1293_ = lean_usize_shift_right(v_x_1281_, v___x_1285_);
                            v_x_1280_ = v_node_1292_;
                            v_x_1281_ = v___x_1293_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1295_ = 0;
                            return v___x_1295_;
                        }
                    }
                } else {
                    v_ks_1296_ = leanh::lean_ctor_get(v_x_1280_, 0);
                    v___x_1297_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1298_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_ks_1296_, v___x_1297_, v_x_1282_);
                    return v___x_1298_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg___boxed(
    mut v_x_1299_: *mut leanh::LeanObject,
    mut v_x_1300_: *mut leanh::LeanObject,
    mut v_x_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_56016__boxed_1302_: usize = 0;
    let mut v_res_1303_: u8 = 0;
    let mut v_r_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_56016__boxed_1302_ = leanh::lean_unbox_usize(v_x_1300_);
    leanh::lean_dec(v_x_1300_);
    v_res_1303_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_1299_, v_x_56016__boxed_1302_, v_x_1301_);
    leanh::lean_dec_ref(v_x_1301_);
    leanh::lean_dec_ref(v_x_1299_);
    v_r_1304_ = leanh::lean_box((v_res_1303_) as usize);
    return v_r_1304_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(
    mut v_x_1305_: *mut leanh::LeanObject,
    mut v_x_1306_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1307_: u64 = 0;
    let mut v___x_1308_: usize = 0;
    let mut v___x_1309_: u8 = 0;
    v___x_1307_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1306_);
    v___x_1308_ = lean_uint64_to_usize(v___x_1307_);
    v___x_1309_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_1305_, v___x_1308_, v_x_1306_);
    return v___x_1309_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg___boxed(
    mut v_x_1310_: *mut leanh::LeanObject,
    mut v_x_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1312_: u8 = 0;
    let mut v_r_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1312_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(
            v_x_1310_, v_x_1311_,
        );
    leanh::lean_dec_ref(v_x_1311_);
    leanh::lean_dec_ref(v_x_1310_);
    v_r_1313_ = leanh::lean_box((v_res_1312_) as usize);
    return v_r_1313_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(
    mut v_e_1314_: *mut leanh::LeanObject,
    mut v___y_1315_: *mut leanh::LeanObject,
    mut v___y_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
    mut v___y_1318_: *mut leanh::LeanObject,
    mut v___y_1319_: *mut leanh::LeanObject,
    mut v___y_1320_: *mut leanh::LeanObject,
    mut v___y_1321_: *mut leanh::LeanObject,
    mut v___y_1322_: *mut leanh::LeanObject,
    mut v___y_1323_: *mut leanh::LeanObject,
    mut v___y_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v_vars_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: u8 = 0;
    let mut v___x_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1345_: u8 = 0;
    let mut v_a_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1349_: u8 = 0;
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1353_: u8 = 0;
    let mut v_lhs_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1364_: u8 = 0;
    let mut v_op_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1370_: u8 = 0;
    let mut v_a_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1374_: u8 = 0;
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_1314_) == 0 {
                    v_x_1327_ = leanh::lean_ctor_get(v_e_1314_, 0);
                    v___x_1328_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                        v___y_1315_,
                        v___y_1316_,
                        v___y_1317_,
                        v___y_1318_,
                        v___y_1319_,
                        v___y_1320_,
                        v___y_1321_,
                        v___y_1322_,
                        v___y_1323_,
                        v___y_1324_,
                        v___y_1325_,
                    );
                    if leanh::lean_obj_tag(v___x_1328_) == 0 {
                        v_a_1329_ = leanh::lean_ctor_get(v___x_1328_, 0);
                        v_isSharedCheck_1345_ =
                            (!leanh::lean_is_exclusive(v___x_1328_)) as u8;
                        if v_isSharedCheck_1345_ == 0 {
                            v___x_1331_ = v___x_1328_;
                            v_isShared_1332_ = v_isSharedCheck_1345_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1329_);
                            leanh::lean_dec(v___x_1328_);
                            v___x_1331_ = leanh::lean_box(0);
                            v_isShared_1332_ = v_isSharedCheck_1345_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1346_ = leanh::lean_ctor_get(v___x_1328_, 0);
                        v_isSharedCheck_1353_ =
                            (!leanh::lean_is_exclusive(v___x_1328_)) as u8;
                        if v_isSharedCheck_1353_ == 0 {
                            v___x_1348_ = v___x_1328_;
                            v_isShared_1349_ = v_isSharedCheck_1353_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1346_);
                            leanh::lean_dec(v___x_1328_);
                            v___x_1348_ = leanh::lean_box(0);
                            v_isShared_1349_ = v_isSharedCheck_1353_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_lhs_1354_ = leanh::lean_ctor_get(v_e_1314_, 0);
                    v_rhs_1355_ = leanh::lean_ctor_get(v_e_1314_, 1);
                    v___x_1356_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                        v___y_1315_,
                        v___y_1316_,
                        v___y_1317_,
                        v___y_1318_,
                        v___y_1319_,
                        v___y_1320_,
                        v___y_1321_,
                        v___y_1322_,
                        v___y_1323_,
                        v___y_1324_,
                        v___y_1325_,
                    );
                    if leanh::lean_obj_tag(v___x_1356_) == 0 {
                        v_a_1357_ = leanh::lean_ctor_get(v___x_1356_, 0);
                        leanh::lean_inc(v_a_1357_);
                        leanh::lean_dec_ref_known(v___x_1356_, 1);
                        v___x_1358_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_lhs_1354_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
                        if leanh::lean_obj_tag(v___x_1358_) == 0 {
                            v_a_1359_ = leanh::lean_ctor_get(v___x_1358_, 0);
                            leanh::lean_inc(v_a_1359_);
                            leanh::lean_dec_ref_known(v___x_1358_, 1);
                            v___x_1360_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_rhs_1355_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
                            if leanh::lean_obj_tag(v___x_1360_) == 0 {
                                v_a_1361_ = leanh::lean_ctor_get(v___x_1360_, 0);
                                v_isSharedCheck_1370_ =
                                    (!leanh::lean_is_exclusive(v___x_1360_)) as u8;
                                if v_isSharedCheck_1370_ == 0 {
                                    v___x_1363_ = v___x_1360_;
                                    v_isShared_1364_ = v_isSharedCheck_1370_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1361_);
                                    leanh::lean_dec(v___x_1360_);
                                    v___x_1363_ = leanh::lean_box(0);
                                    v_isShared_1364_ = v_isSharedCheck_1370_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_1359_);
                                leanh::lean_dec(v_a_1357_);
                                return v___x_1360_;
                            }
                        } else {
                            leanh::lean_dec(v_a_1357_);
                            return v___x_1358_;
                        }
                    } else {
                        v_a_1371_ = leanh::lean_ctor_get(v___x_1356_, 0);
                        v_isSharedCheck_1378_ =
                            (!leanh::lean_is_exclusive(v___x_1356_)) as u8;
                        if v_isSharedCheck_1378_ == 0 {
                            v___x_1373_ = v___x_1356_;
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1371_);
                            leanh::lean_dec(v___x_1356_);
                            v___x_1373_ = leanh::lean_box(0);
                            v_isShared_1374_ = v_isSharedCheck_1378_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_vars_1333_ = leanh::lean_ctor_get(v_a_1329_, 10);
                leanh::lean_inc_ref(v_vars_1333_);
                leanh::lean_dec(v_a_1329_);
                v_size_1334_ = leanh::lean_ctor_get(v_vars_1333_, 2);
                v___x_1335_ = l_Lean_instInhabitedExpr;
                v___x_1336_ = lean_nat_dec_lt(v_x_1327_, v_size_1334_);
                if v___x_1336_ == 0 {
                    leanh::lean_dec_ref(v_vars_1333_);
                    v___x_1337_ = l_outOfBounds___redArg(v___x_1335_);
                    if v_isShared_1332_ == 0 {
                        leanh::lean_ctor_set(v___x_1331_, 0, v___x_1337_);
                        v___x_1339_ = v___x_1331_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1340_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1337_);
                        v___x_1339_ = v_reuseFailAlloc_1340_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1341_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1335_,
                        v_vars_1333_,
                        v_x_1327_,
                    );
                    leanh::lean_dec_ref(v_vars_1333_);
                    if v_isShared_1332_ == 0 {
                        leanh::lean_ctor_set(v___x_1331_, 0, v___x_1341_);
                        v___x_1343_ = v___x_1331_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1344_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1344_, 0, v___x_1341_);
                        v___x_1343_ = v_reuseFailAlloc_1344_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1339_;
            }
            3 => {
                return v___x_1343_;
            }
            4 => {
                if v_isShared_1349_ == 0 {
                    v___x_1351_ = v___x_1348_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1352_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
                    v___x_1351_ = v_reuseFailAlloc_1352_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1351_;
            }
            6 => {
                v_op_1365_ = leanh::lean_ctor_get(v_a_1357_, 3);
                leanh::lean_inc_ref(v_op_1365_);
                leanh::lean_dec(v_a_1357_);
                v___x_1366_ = l_Lean_mkAppB(v_op_1365_, v_a_1359_, v_a_1361_);
                if v_isShared_1364_ == 0 {
                    leanh::lean_ctor_set(v___x_1363_, 0, v___x_1366_);
                    v___x_1368_ = v___x_1363_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1366_);
                    v___x_1368_ = v_reuseFailAlloc_1369_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1368_;
            }
            8 => {
                if v_isShared_1374_ == 0 {
                    v___x_1376_ = v___x_1373_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
                    v___x_1376_ = v_reuseFailAlloc_1377_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1376_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2___boxed(
    mut v_e_1379_: *mut leanh::LeanObject,
    mut v___y_1380_: *mut leanh::LeanObject,
    mut v___y_1381_: *mut leanh::LeanObject,
    mut v___y_1382_: *mut leanh::LeanObject,
    mut v___y_1383_: *mut leanh::LeanObject,
    mut v___y_1384_: *mut leanh::LeanObject,
    mut v___y_1385_: *mut leanh::LeanObject,
    mut v___y_1386_: *mut leanh::LeanObject,
    mut v___y_1387_: *mut leanh::LeanObject,
    mut v___y_1388_: *mut leanh::LeanObject,
    mut v___y_1389_: *mut leanh::LeanObject,
    mut v___y_1390_: *mut leanh::LeanObject,
    mut v___y_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1392_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(
        v_e_1379_,
        v___y_1380_,
        v___y_1381_,
        v___y_1382_,
        v___y_1383_,
        v___y_1384_,
        v___y_1385_,
        v___y_1386_,
        v___y_1387_,
        v___y_1388_,
        v___y_1389_,
        v___y_1390_,
    );
    leanh::lean_dec(v___y_1390_);
    leanh::lean_dec_ref(v___y_1389_);
    leanh::lean_dec(v___y_1388_);
    leanh::lean_dec_ref(v___y_1387_);
    leanh::lean_dec(v___y_1386_);
    leanh::lean_dec_ref(v___y_1385_);
    leanh::lean_dec(v___y_1384_);
    leanh::lean_dec_ref(v___y_1383_);
    leanh::lean_dec(v___y_1382_);
    leanh::lean_dec(v___y_1381_);
    leanh::lean_dec(v___y_1380_);
    leanh::lean_dec_ref(v_e_1379_);
    return v_res_1392_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_internalize___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1403_ = l_Lean_Meta_Grind_AC_internalize___closed__3;
    v___x_1404_ = l_Lean_Meta_Grind_AC_internalize___closed__5;
    v___x_1405_ = l_Lean_Name_append(v___x_1404_, v___x_1403_);
    return v___x_1405_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_internalize___closed__8() -> *mut leanh::LeanObject
{
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1407_ = l_Lean_Meta_Grind_AC_internalize___closed__7;
    v___x_1408_ = l_Lean_stringToMessageData(v___x_1407_);
    return v___x_1408_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_AC_internalize___closed__10() -> *mut leanh::LeanObject
{
    let mut v___x_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1410_ = l_Lean_Meta_Grind_AC_internalize___closed__9;
    v___x_1411_ = l_Lean_stringToMessageData(v___x_1410_);
    return v___x_1411_;
}
pub unsafe fn l_Lean_Meta_Grind_AC_internalize(
    mut v_e_1412_: *mut leanh::LeanObject,
    mut v_parent_x3f_1413_: *mut leanh::LeanObject,
    mut v_a_1414_: *mut leanh::LeanObject,
    mut v_a_1415_: *mut leanh::LeanObject,
    mut v_a_1416_: *mut leanh::LeanObject,
    mut v_a_1417_: *mut leanh::LeanObject,
    mut v_a_1418_: *mut leanh::LeanObject,
    mut v_a_1419_: *mut leanh::LeanObject,
    mut v_a_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
    mut v_a_1422_: *mut leanh::LeanObject,
    mut v_a_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1444_: u8 = 0;
    let mut v_ac_1445_: u8 = 0;
    let mut v___y_1447_: u8 = 0;
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1458_: u8 = 0;
    let mut v_val_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1464_: u8 = 0;
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1470_: u8 = 0;
    let mut v_denote_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v_options_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1482_: u8 = 0;
    let mut v_inheritedTraceOptions_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: u8 = 0;
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1504_: u8 = 0;
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1508_: u8 = 0;
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v_unused_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1514_: u8 = 0;
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1518_: u8 = 0;
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1523_: u8 = 0;
    let mut v_a_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1527_: u8 = 0;
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1531_: u8 = 0;
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1536_: u8 = 0;
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1541_: u8 = 0;
    let mut v_a_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1545_: u8 = 0;
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1549_: u8 = 0;
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: u8 = 0;
    let mut v_isSharedCheck_1555_: u8 = 0;
    let mut v_a_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1559_: u8 = 0;
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1440_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1416_);
                if leanh::lean_obj_tag(v___x_1440_) == 0 {
                    v_a_1441_ = leanh::lean_ctor_get(v___x_1440_, 0);
                    v_isSharedCheck_1555_ = (!leanh::lean_is_exclusive(v___x_1440_)) as u8;
                    if v_isSharedCheck_1555_ == 0 {
                        v___x_1443_ = v___x_1440_;
                        v_isShared_1444_ = v_isSharedCheck_1555_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1441_);
                        leanh::lean_dec(v___x_1440_);
                        v___x_1443_ = leanh::lean_box(0);
                        v_isShared_1444_ = v_isSharedCheck_1555_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_parent_x3f_1413_);
                    leanh::lean_dec_ref(v_e_1412_);
                    v_a_1556_ = leanh::lean_ctor_get(v___x_1440_, 0);
                    v_isSharedCheck_1563_ = (!leanh::lean_is_exclusive(v___x_1440_)) as u8;
                    if v_isSharedCheck_1563_ == 0 {
                        v___x_1558_ = v___x_1440_;
                        v_isShared_1559_ = v_isSharedCheck_1563_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1556_);
                        leanh::lean_dec(v___x_1440_);
                        v___x_1558_ = leanh::lean_box(0);
                        v_isShared_1559_ = v_isSharedCheck_1563_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v_e_1412_);
                v___x_1437_ =
                    l_Lean_Meta_Grind_AC_addTermOpId___redArg(v_e_1412_, v___y_1426_, v___y_1427_);
                leanh::lean_dec(v___y_1426_);
                if leanh::lean_obj_tag(v___x_1437_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1437_, 1);
                    v___x_1438_ = l_Lean_Meta_Grind_AC_acExt;
                    v___x_1439_ = l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                        v___x_1438_,
                        v_e_1412_,
                        v___y_1427_,
                        v___y_1428_,
                        v___y_1429_,
                        v___y_1430_,
                        v___y_1431_,
                        v___y_1432_,
                        v___y_1433_,
                        v___y_1434_,
                        v___y_1435_,
                        v___y_1436_,
                    );
                    return v___x_1439_;
                } else {
                    leanh::lean_dec_ref(v_e_1412_);
                    return v___x_1437_;
                }
            }
            2 => {
                v_ac_1445_ = leanh::lean_ctor_get_uint8(
                    v_a_1441_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 13 + 24) as u32,
                );
                leanh::lean_dec(v_a_1441_);
                if v_ac_1445_ == 0 {
                    leanh::lean_del_object(v___x_1443_);
                    leanh::lean_dec(v_parent_x3f_1413_);
                    leanh::lean_dec_ref(v_e_1412_);
                    v___x_1550_ = leanh::lean_box(0);
                    v___x_1551_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1551_, 0, v___x_1550_);
                    return v___x_1551_;
                } else {
                    v___x_1552_ = l_Lean_Expr_isApp(v_e_1412_);
                    if v___x_1552_ == 0 {
                        v___y_1447_ = v___x_1552_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1553_ = l_Lean_Expr_appFn_x21(v_e_1412_);
                        v___x_1554_ = l_Lean_Expr_isApp(v___x_1553_);
                        leanh::lean_dec_ref(v___x_1553_);
                        v___y_1447_ = v___x_1554_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v___y_1447_ == 0 {
                    leanh::lean_dec(v_parent_x3f_1413_);
                    leanh::lean_dec_ref(v_e_1412_);
                    v___x_1448_ = leanh::lean_box(0);
                    if v_isShared_1444_ == 0 {
                        leanh::lean_ctor_set(v___x_1443_, 0, v___x_1448_);
                        v___x_1450_ = v___x_1443_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1451_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1448_);
                        v___x_1450_ = v_reuseFailAlloc_1451_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1443_);
                    v___x_1452_ = l_Lean_Expr_appFn_x21(v_e_1412_);
                    v___x_1453_ = l_Lean_Expr_appFn_x21(v___x_1452_);
                    leanh::lean_dec_ref(v___x_1452_);
                    leanh::lean_inc_ref(v___x_1453_);
                    v___x_1454_ = l_Lean_Meta_Grind_AC_getOpId_x3f(
                        v___x_1453_,
                        v_a_1414_,
                        v_a_1415_,
                        v_a_1416_,
                        v_a_1417_,
                        v_a_1418_,
                        v_a_1419_,
                        v_a_1420_,
                        v_a_1421_,
                        v_a_1422_,
                        v_a_1423_,
                    );
                    if leanh::lean_obj_tag(v___x_1454_) == 0 {
                        v_a_1455_ = leanh::lean_ctor_get(v___x_1454_, 0);
                        v_isSharedCheck_1541_ =
                            (!leanh::lean_is_exclusive(v___x_1454_)) as u8;
                        if v_isSharedCheck_1541_ == 0 {
                            v___x_1457_ = v___x_1454_;
                            v_isShared_1458_ = v_isSharedCheck_1541_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1455_);
                            leanh::lean_dec(v___x_1454_);
                            v___x_1457_ = leanh::lean_box(0);
                            v_isShared_1458_ = v_isSharedCheck_1541_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_1453_);
                        leanh::lean_dec(v_parent_x3f_1413_);
                        leanh::lean_dec_ref(v_e_1412_);
                        v_a_1542_ = leanh::lean_ctor_get(v___x_1454_, 0);
                        v_isSharedCheck_1549_ =
                            (!leanh::lean_is_exclusive(v___x_1454_)) as u8;
                        if v_isSharedCheck_1549_ == 0 {
                            v___x_1544_ = v___x_1454_;
                            v_isShared_1545_ = v_isSharedCheck_1549_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1542_);
                            leanh::lean_dec(v___x_1454_);
                            v___x_1544_ = leanh::lean_box(0);
                            v_isShared_1545_ = v_isSharedCheck_1549_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_1450_;
            }
            5 => {
                if leanh::lean_obj_tag(v_a_1455_) == 1 {
                    leanh::lean_del_object(v___x_1457_);
                    v_val_1459_ = leanh::lean_ctor_get(v_a_1455_, 0);
                    leanh::lean_inc(v_val_1459_);
                    leanh::lean_dec_ref_known(v_a_1455_, 1);
                    v___x_1460_ = l___private_Lean_Meta_Tactic_Grind_AC_Internalize_0__Lean_Meta_Grind_AC_isParentSameOpApp___redArg(v_parent_x3f_1413_, v___x_1453_);
                    leanh::lean_dec_ref(v___x_1453_);
                    v_a_1461_ = leanh::lean_ctor_get(v___x_1460_, 0);
                    v_isSharedCheck_1536_ = (!leanh::lean_is_exclusive(v___x_1460_)) as u8;
                    if v_isSharedCheck_1536_ == 0 {
                        v___x_1463_ = v___x_1460_;
                        v_isShared_1464_ = v_isSharedCheck_1536_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1461_);
                        leanh::lean_dec(v___x_1460_);
                        v___x_1463_ = leanh::lean_box(0);
                        v_isShared_1464_ = v_isSharedCheck_1536_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1455_);
                    leanh::lean_dec_ref(v___x_1453_);
                    leanh::lean_dec(v_parent_x3f_1413_);
                    leanh::lean_dec_ref(v_e_1412_);
                    v___x_1537_ = leanh::lean_box(0);
                    if v_isShared_1458_ == 0 {
                        leanh::lean_ctor_set(v___x_1457_, 0, v___x_1537_);
                        v___x_1539_ = v___x_1457_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_1540_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1537_);
                        v___x_1539_ = v_reuseFailAlloc_1540_;
                        state = 18;
                        continue;
                    }
                }
            }
            6 => {
                v___x_1465_ = (leanh::lean_unbox(v_a_1461_) as u8);
                leanh::lean_dec(v_a_1461_);
                if v___x_1465_ == 0 {
                    leanh::lean_del_object(v___x_1463_);
                    v___x_1466_ = l_Lean_Meta_Grind_AC_ACM_getStruct(
                        v_val_1459_,
                        v_a_1414_,
                        v_a_1415_,
                        v_a_1416_,
                        v_a_1417_,
                        v_a_1418_,
                        v_a_1419_,
                        v_a_1420_,
                        v_a_1421_,
                        v_a_1422_,
                        v_a_1423_,
                    );
                    if leanh::lean_obj_tag(v___x_1466_) == 0 {
                        v_a_1467_ = leanh::lean_ctor_get(v___x_1466_, 0);
                        v_isSharedCheck_1523_ =
                            (!leanh::lean_is_exclusive(v___x_1466_)) as u8;
                        if v_isSharedCheck_1523_ == 0 {
                            v___x_1469_ = v___x_1466_;
                            v_isShared_1470_ = v_isSharedCheck_1523_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1467_);
                            leanh::lean_dec(v___x_1466_);
                            v___x_1469_ = leanh::lean_box(0);
                            v_isShared_1470_ = v_isSharedCheck_1523_;
                            state = 7;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_val_1459_);
                        leanh::lean_dec_ref(v_e_1412_);
                        v_a_1524_ = leanh::lean_ctor_get(v___x_1466_, 0);
                        v_isSharedCheck_1531_ =
                            (!leanh::lean_is_exclusive(v___x_1466_)) as u8;
                        if v_isSharedCheck_1531_ == 0 {
                            v___x_1526_ = v___x_1466_;
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 15;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1524_);
                            leanh::lean_dec(v___x_1466_);
                            v___x_1526_ = leanh::lean_box(0);
                            v_isShared_1527_ = v_isSharedCheck_1531_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_val_1459_);
                    leanh::lean_dec_ref(v_e_1412_);
                    v___x_1532_ = leanh::lean_box(0);
                    if v_isShared_1464_ == 0 {
                        leanh::lean_ctor_set(v___x_1463_, 0, v___x_1532_);
                        v___x_1534_ = v___x_1463_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_1535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1535_, 0, v___x_1532_);
                        v___x_1534_ = v_reuseFailAlloc_1535_;
                        state = 17;
                        continue;
                    }
                }
            }
            7 => {
                v_denote_1471_ = leanh::lean_ctor_get(v_a_1467_, 12);
                leanh::lean_inc_ref(v_denote_1471_);
                leanh::lean_dec(v_a_1467_);
                v___x_1472_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(v_denote_1471_, v_e_1412_);
                leanh::lean_dec_ref(v_denote_1471_);
                if v___x_1472_ == 0 {
                    leanh::lean_del_object(v___x_1469_);
                    leanh::lean_inc_ref(v_e_1412_);
                    v___x_1473_ = l_Lean_Meta_Grind_AC_reify(
                        v_e_1412_,
                        v_val_1459_,
                        v_a_1414_,
                        v_a_1415_,
                        v_a_1416_,
                        v_a_1417_,
                        v_a_1418_,
                        v_a_1419_,
                        v_a_1420_,
                        v_a_1421_,
                        v_a_1422_,
                        v_a_1423_,
                    );
                    if leanh::lean_obj_tag(v___x_1473_) == 0 {
                        v_a_1474_ = leanh::lean_ctor_get(v___x_1473_, 0);
                        leanh::lean_inc_n(v_a_1474_, 2);
                        leanh::lean_dec_ref_known(v___x_1473_, 1);
                        v___x_1475_ = leanh::lean_box((v_ac_1445_) as usize);
                        leanh::lean_inc_ref(v_e_1412_);
                        v___f_1476_ = leanh::lean_alloc_closure(
                            l_Lean_Meta_Grind_AC_internalize___lam__0___boxed
                                as *mut core::ffi::c_void,
                            4,
                            3,
                        );
                        leanh::lean_closure_set(v___f_1476_, 0, v_e_1412_);
                        leanh::lean_closure_set(v___f_1476_, 1, v_a_1474_);
                        leanh::lean_closure_set(v___f_1476_, 2, v___x_1475_);
                        v___x_1477_ = l_Lean_Meta_Grind_AC_modifyStruct___redArg(
                            v___f_1476_,
                            v_val_1459_,
                            v_a_1414_,
                        );
                        if leanh::lean_obj_tag(v___x_1477_) == 0 {
                            v_isSharedCheck_1509_ =
                                (!leanh::lean_is_exclusive(v___x_1477_)) as u8;
                            if v_isSharedCheck_1509_ == 0 {
                                v_unused_1510_ = leanh::lean_ctor_get(v___x_1477_, 0);
                                leanh::lean_dec(v_unused_1510_);
                                v___x_1479_ = v___x_1477_;
                                v_isShared_1480_ = v_isSharedCheck_1509_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_1477_);
                                v___x_1479_ = leanh::lean_box(0);
                                v_isShared_1480_ = v_isSharedCheck_1509_;
                                state = 8;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1474_);
                            leanh::lean_dec(v_val_1459_);
                            leanh::lean_dec_ref(v_e_1412_);
                            return v___x_1477_;
                        }
                    } else {
                        leanh::lean_dec(v_val_1459_);
                        leanh::lean_dec_ref(v_e_1412_);
                        v_a_1511_ = leanh::lean_ctor_get(v___x_1473_, 0);
                        v_isSharedCheck_1518_ =
                            (!leanh::lean_is_exclusive(v___x_1473_)) as u8;
                        if v_isSharedCheck_1518_ == 0 {
                            v___x_1513_ = v___x_1473_;
                            v_isShared_1514_ = v_isSharedCheck_1518_;
                            state = 12;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1511_);
                            leanh::lean_dec(v___x_1473_);
                            v___x_1513_ = leanh::lean_box(0);
                            v_isShared_1514_ = v_isSharedCheck_1518_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_val_1459_);
                    leanh::lean_dec_ref(v_e_1412_);
                    v___x_1519_ = leanh::lean_box(0);
                    if v_isShared_1470_ == 0 {
                        leanh::lean_ctor_set(v___x_1469_, 0, v___x_1519_);
                        v___x_1521_ = v___x_1469_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_1522_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1522_, 0, v___x_1519_);
                        v___x_1521_ = v_reuseFailAlloc_1522_;
                        state = 14;
                        continue;
                    }
                }
            }
            8 => {
                v_options_1481_ = leanh::lean_ctor_get(v_a_1422_, 2);
                v_hasTrace_1482_ = leanh::lean_ctor_get_uint8(
                    v_options_1481_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_1482_ == 0 {
                    leanh::lean_del_object(v___x_1479_);
                    leanh::lean_dec(v_a_1474_);
                    v___y_1426_ = v_val_1459_;
                    v___y_1427_ = v_a_1414_;
                    v___y_1428_ = v_a_1415_;
                    v___y_1429_ = v_a_1416_;
                    v___y_1430_ = v_a_1417_;
                    v___y_1431_ = v_a_1418_;
                    v___y_1432_ = v_a_1419_;
                    v___y_1433_ = v_a_1420_;
                    v___y_1434_ = v_a_1421_;
                    v___y_1435_ = v_a_1422_;
                    v___y_1436_ = v_a_1423_;
                    state = 1;
                    continue;
                } else {
                    v_inheritedTraceOptions_1483_ = leanh::lean_ctor_get(v_a_1422_, 13);
                    v___x_1484_ = l_Lean_Meta_Grind_AC_internalize___closed__3;
                    v___x_1485_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_internalize___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_internalize___closed__6_once),
                        _init_l_Lean_Meta_Grind_AC_internalize___closed__6,
                    );
                    v___x_1486_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_1483_,
                        v_options_1481_,
                        v___x_1485_,
                    );
                    if v___x_1486_ == 0 {
                        leanh::lean_del_object(v___x_1479_);
                        leanh::lean_dec(v_a_1474_);
                        v___y_1426_ = v_val_1459_;
                        v___y_1427_ = v_a_1414_;
                        v___y_1428_ = v_a_1415_;
                        v___y_1429_ = v_a_1416_;
                        v___y_1430_ = v_a_1417_;
                        v___y_1431_ = v_a_1418_;
                        v___y_1432_ = v_a_1419_;
                        v___y_1433_ = v_a_1420_;
                        v___y_1434_ = v_a_1421_;
                        v___y_1435_ = v_a_1422_;
                        v___y_1436_ = v_a_1423_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1487_ = l_Lean_Grind_AC_Expr_denoteExpr___at___00Lean_Meta_Grind_AC_internalize_spec__2(v_a_1474_, v_val_1459_, v_a_1414_, v_a_1415_, v_a_1416_, v_a_1417_, v_a_1418_, v_a_1419_, v_a_1420_, v_a_1421_, v_a_1422_, v_a_1423_);
                        leanh::lean_dec(v_a_1474_);
                        if leanh::lean_obj_tag(v___x_1487_) == 0 {
                            v_a_1488_ = leanh::lean_ctor_get(v___x_1487_, 0);
                            leanh::lean_inc(v_a_1488_);
                            leanh::lean_dec_ref_known(v___x_1487_, 1);
                            v___x_1489_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_AC_internalize___closed__8
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_AC_internalize___closed__8_once
                                ),
                                _init_l_Lean_Meta_Grind_AC_internalize___closed__8,
                            );
                            leanh::lean_inc(v_val_1459_);
                            v___x_1490_ = l_Nat_reprFast(v_val_1459_);
                            if v_isShared_1480_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_1479_, 3);
                                leanh::lean_ctor_set(v___x_1479_, 0, v___x_1490_);
                                v___x_1492_ = v___x_1479_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1500_ =
                                    leanh::lean_alloc_ctor(3, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v___x_1490_);
                                v___x_1492_ = v_reuseFailAlloc_1500_;
                                state = 9;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1479_);
                            leanh::lean_dec(v_val_1459_);
                            leanh::lean_dec_ref(v_e_1412_);
                            v_a_1501_ = leanh::lean_ctor_get(v___x_1487_, 0);
                            v_isSharedCheck_1508_ =
                                (!leanh::lean_is_exclusive(v___x_1487_)) as u8;
                            if v_isSharedCheck_1508_ == 0 {
                                v___x_1503_ = v___x_1487_;
                                v_isShared_1504_ = v_isSharedCheck_1508_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1501_);
                                leanh::lean_dec(v___x_1487_);
                                v___x_1503_ = leanh::lean_box(0);
                                v_isShared_1504_ = v_isSharedCheck_1508_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            9 => {
                v___x_1493_ = l_Lean_MessageData_ofFormat(v___x_1492_);
                v___x_1494_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1494_, 0, v___x_1489_);
                leanh::lean_ctor_set(v___x_1494_, 1, v___x_1493_);
                v___x_1495_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_internalize___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_AC_internalize___closed__10_once),
                    _init_l_Lean_Meta_Grind_AC_internalize___closed__10,
                );
                v___x_1496_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1496_, 0, v___x_1494_);
                leanh::lean_ctor_set(v___x_1496_, 1, v___x_1495_);
                v___x_1497_ = l_Lean_MessageData_ofExpr(v_a_1488_);
                v___x_1498_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1498_, 0, v___x_1496_);
                leanh::lean_ctor_set(v___x_1498_, 1, v___x_1497_);
                v___x_1499_ =
                    l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(
                        v___x_1484_,
                        v___x_1498_,
                        v_a_1420_,
                        v_a_1421_,
                        v_a_1422_,
                        v_a_1423_,
                    );
                if leanh::lean_obj_tag(v___x_1499_) == 0 {
                    leanh::lean_dec_ref_known(v___x_1499_, 1);
                    v___y_1426_ = v_val_1459_;
                    v___y_1427_ = v_a_1414_;
                    v___y_1428_ = v_a_1415_;
                    v___y_1429_ = v_a_1416_;
                    v___y_1430_ = v_a_1417_;
                    v___y_1431_ = v_a_1418_;
                    v___y_1432_ = v_a_1419_;
                    v___y_1433_ = v_a_1420_;
                    v___y_1434_ = v_a_1421_;
                    v___y_1435_ = v_a_1422_;
                    v___y_1436_ = v_a_1423_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1459_);
                    leanh::lean_dec_ref(v_e_1412_);
                    return v___x_1499_;
                }
            }
            10 => {
                if v_isShared_1504_ == 0 {
                    v___x_1506_ = v___x_1503_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1507_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1507_, 0, v_a_1501_);
                    v___x_1506_ = v_reuseFailAlloc_1507_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1506_;
            }
            12 => {
                if v_isShared_1514_ == 0 {
                    v___x_1516_ = v___x_1513_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1517_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
                    v___x_1516_ = v_reuseFailAlloc_1517_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1516_;
            }
            14 => {
                return v___x_1521_;
            }
            15 => {
                if v_isShared_1527_ == 0 {
                    v___x_1529_ = v___x_1526_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1530_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1530_, 0, v_a_1524_);
                    v___x_1529_ = v_reuseFailAlloc_1530_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1529_;
            }
            17 => {
                return v___x_1534_;
            }
            18 => {
                return v___x_1539_;
            }
            19 => {
                if v_isShared_1545_ == 0 {
                    v___x_1547_ = v___x_1544_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1548_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1548_, 0, v_a_1542_);
                    v___x_1547_ = v_reuseFailAlloc_1548_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1547_;
            }
            21 => {
                if v_isShared_1559_ == 0 {
                    v___x_1561_ = v___x_1558_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_a_1556_);
                    v___x_1561_ = v_reuseFailAlloc_1562_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_AC_internalize___boxed(
    mut v_e_1564_: *mut leanh::LeanObject,
    mut v_parent_x3f_1565_: *mut leanh::LeanObject,
    mut v_a_1566_: *mut leanh::LeanObject,
    mut v_a_1567_: *mut leanh::LeanObject,
    mut v_a_1568_: *mut leanh::LeanObject,
    mut v_a_1569_: *mut leanh::LeanObject,
    mut v_a_1570_: *mut leanh::LeanObject,
    mut v_a_1571_: *mut leanh::LeanObject,
    mut v_a_1572_: *mut leanh::LeanObject,
    mut v_a_1573_: *mut leanh::LeanObject,
    mut v_a_1574_: *mut leanh::LeanObject,
    mut v_a_1575_: *mut leanh::LeanObject,
    mut v_a_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1577_ = l_Lean_Meta_Grind_AC_internalize(
        v_e_1564_,
        v_parent_x3f_1565_,
        v_a_1566_,
        v_a_1567_,
        v_a_1568_,
        v_a_1569_,
        v_a_1570_,
        v_a_1571_,
        v_a_1572_,
        v_a_1573_,
        v_a_1574_,
        v_a_1575_,
    );
    leanh::lean_dec(v_a_1575_);
    leanh::lean_dec_ref(v_a_1574_);
    leanh::lean_dec(v_a_1573_);
    leanh::lean_dec_ref(v_a_1572_);
    leanh::lean_dec(v_a_1571_);
    leanh::lean_dec_ref(v_a_1570_);
    leanh::lean_dec(v_a_1569_);
    leanh::lean_dec_ref(v_a_1568_);
    leanh::lean_dec(v_a_1567_);
    leanh::lean_dec(v_a_1566_);
    return v_res_1577_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(
    mut v_00_u03b2_1578_: *mut leanh::LeanObject,
    mut v_x_1579_: *mut leanh::LeanObject,
    mut v_x_1580_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1581_: u8 = 0;
    v___x_1581_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___redArg(
            v_x_1579_, v_x_1580_,
        );
    return v___x_1581_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0___boxed(
    mut v_00_u03b2_1582_: *mut leanh::LeanObject,
    mut v_x_1583_: *mut leanh::LeanObject,
    mut v_x_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1585_: u8 = 0;
    let mut v_r_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1585_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0(
        v_00_u03b2_1582_,
        v_x_1583_,
        v_x_1584_,
    );
    leanh::lean_dec_ref(v_x_1584_);
    leanh::lean_dec_ref(v_x_1583_);
    v_r_1586_ = leanh::lean_box((v_res_1585_) as usize);
    return v_r_1586_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1(
    mut v_00_u03b2_1587_: *mut leanh::LeanObject,
    mut v_x_1588_: *mut leanh::LeanObject,
    mut v_x_1589_: *mut leanh::LeanObject,
    mut v_x_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1591_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1___redArg(
            v_x_1588_, v_x_1589_, v_x_1590_,
        );
    return v___x_1591_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(
    mut v_cls_1592_: *mut leanh::LeanObject,
    mut v_msg_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
    mut v___y_1597_: *mut leanh::LeanObject,
    mut v___y_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
    mut v___y_1601_: *mut leanh::LeanObject,
    mut v___y_1602_: *mut leanh::LeanObject,
    mut v___y_1603_: *mut leanh::LeanObject,
    mut v___y_1604_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1606_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___redArg(
        v_cls_1592_,
        v_msg_1593_,
        v___y_1601_,
        v___y_1602_,
        v___y_1603_,
        v___y_1604_,
    );
    return v___x_1606_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3___boxed(
    mut v_cls_1607_: *mut leanh::LeanObject,
    mut v_msg_1608_: *mut leanh::LeanObject,
    mut v___y_1609_: *mut leanh::LeanObject,
    mut v___y_1610_: *mut leanh::LeanObject,
    mut v___y_1611_: *mut leanh::LeanObject,
    mut v___y_1612_: *mut leanh::LeanObject,
    mut v___y_1613_: *mut leanh::LeanObject,
    mut v___y_1614_: *mut leanh::LeanObject,
    mut v___y_1615_: *mut leanh::LeanObject,
    mut v___y_1616_: *mut leanh::LeanObject,
    mut v___y_1617_: *mut leanh::LeanObject,
    mut v___y_1618_: *mut leanh::LeanObject,
    mut v___y_1619_: *mut leanh::LeanObject,
    mut v___y_1620_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1621_ = l_Lean_addTrace___at___00Lean_Meta_Grind_AC_internalize_spec__3(
        v_cls_1607_,
        v_msg_1608_,
        v___y_1609_,
        v___y_1610_,
        v___y_1611_,
        v___y_1612_,
        v___y_1613_,
        v___y_1614_,
        v___y_1615_,
        v___y_1616_,
        v___y_1617_,
        v___y_1618_,
        v___y_1619_,
    );
    leanh::lean_dec(v___y_1619_);
    leanh::lean_dec_ref(v___y_1618_);
    leanh::lean_dec(v___y_1617_);
    leanh::lean_dec_ref(v___y_1616_);
    leanh::lean_dec(v___y_1615_);
    leanh::lean_dec_ref(v___y_1614_);
    leanh::lean_dec(v___y_1613_);
    leanh::lean_dec_ref(v___y_1612_);
    leanh::lean_dec(v___y_1611_);
    leanh::lean_dec(v___y_1610_);
    leanh::lean_dec(v___y_1609_);
    return v_res_1621_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(
    mut v_00_u03b2_1622_: *mut leanh::LeanObject,
    mut v_x_1623_: *mut leanh::LeanObject,
    mut v_x_1624_: usize,
    mut v_x_1625_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1626_: u8 = 0;
    v___x_1626_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___redArg(v_x_1623_, v_x_1624_, v_x_1625_);
    return v___x_1626_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0___boxed(
    mut v_00_u03b2_1627_: *mut leanh::LeanObject,
    mut v_x_1628_: *mut leanh::LeanObject,
    mut v_x_1629_: *mut leanh::LeanObject,
    mut v_x_1630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_56595__boxed_1631_: usize = 0;
    let mut v_res_1632_: u8 = 0;
    let mut v_r_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_56595__boxed_1631_ = leanh::lean_unbox_usize(v_x_1629_);
    leanh::lean_dec(v_x_1629_);
    v_res_1632_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0(v_00_u03b2_1627_, v_x_1628_, v_x_56595__boxed_1631_, v_x_1630_);
    leanh::lean_dec_ref(v_x_1630_);
    leanh::lean_dec_ref(v_x_1628_);
    v_r_1633_ = leanh::lean_box((v_res_1632_) as usize);
    return v_r_1633_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(
    mut v_00_u03b2_1634_: *mut leanh::LeanObject,
    mut v_x_1635_: *mut leanh::LeanObject,
    mut v_x_1636_: usize,
    mut v_x_1637_: usize,
    mut v_x_1638_: *mut leanh::LeanObject,
    mut v_x_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___redArg(v_x_1635_, v_x_1636_, v_x_1637_, v_x_1638_, v_x_1639_);
    return v___x_1640_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2___boxed(
    mut v_00_u03b2_1641_: *mut leanh::LeanObject,
    mut v_x_1642_: *mut leanh::LeanObject,
    mut v_x_1643_: *mut leanh::LeanObject,
    mut v_x_1644_: *mut leanh::LeanObject,
    mut v_x_1645_: *mut leanh::LeanObject,
    mut v_x_1646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_56606__boxed_1647_: usize = 0;
    let mut v_x_56607__boxed_1648_: usize = 0;
    let mut v_res_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_56606__boxed_1647_ = leanh::lean_unbox_usize(v_x_1643_);
    leanh::lean_dec(v_x_1643_);
    v_x_56607__boxed_1648_ = leanh::lean_unbox_usize(v_x_1644_);
    leanh::lean_dec(v_x_1644_);
    v_res_1649_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2(v_00_u03b2_1641_, v_x_1642_, v_x_56606__boxed_1647_, v_x_56607__boxed_1648_, v_x_1645_, v_x_1646_);
    return v_res_1649_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1650_: *mut leanh::LeanObject,
    mut v_keys_1651_: *mut leanh::LeanObject,
    mut v_vals_1652_: *mut leanh::LeanObject,
    mut v_heq_1653_: *mut leanh::LeanObject,
    mut v_i_1654_: *mut leanh::LeanObject,
    mut v_k_1655_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1656_: u8 = 0;
    v___x_1656_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___redArg(v_keys_1651_, v_i_1654_, v_k_1655_);
    return v___x_1656_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1657_: *mut leanh::LeanObject,
    mut v_keys_1658_: *mut leanh::LeanObject,
    mut v_vals_1659_: *mut leanh::LeanObject,
    mut v_heq_1660_: *mut leanh::LeanObject,
    mut v_i_1661_: *mut leanh::LeanObject,
    mut v_k_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1663_: u8 = 0;
    let mut v_r_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Grind_AC_internalize_spec__0_spec__0_spec__1(v_00_u03b2_1657_, v_keys_1658_, v_vals_1659_, v_heq_1660_, v_i_1661_, v_k_1662_);
    leanh::lean_dec_ref(v_k_1662_);
    leanh::lean_dec_ref(v_vals_1659_);
    leanh::lean_dec_ref(v_keys_1658_);
    v_r_1664_ = leanh::lean_box((v_res_1663_) as usize);
    return v_r_1664_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1665_: *mut leanh::LeanObject,
    mut v_n_1666_: *mut leanh::LeanObject,
    mut v_k_1667_: *mut leanh::LeanObject,
    mut v_v_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1669_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4___redArg(v_n_1666_, v_k_1667_, v_v_1668_);
    return v___x_1669_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(
    mut v_00_u03b2_1670_: *mut leanh::LeanObject,
    mut v_depth_1671_: usize,
    mut v_keys_1672_: *mut leanh::LeanObject,
    mut v_vals_1673_: *mut leanh::LeanObject,
    mut v_heq_1674_: *mut leanh::LeanObject,
    mut v_i_1675_: *mut leanh::LeanObject,
    mut v_entries_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1677_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___redArg(v_depth_1671_, v_keys_1672_, v_vals_1673_, v_i_1675_, v_entries_1676_);
    return v___x_1677_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_1678_: *mut leanh::LeanObject,
    mut v_depth_1679_: *mut leanh::LeanObject,
    mut v_keys_1680_: *mut leanh::LeanObject,
    mut v_vals_1681_: *mut leanh::LeanObject,
    mut v_heq_1682_: *mut leanh::LeanObject,
    mut v_i_1683_: *mut leanh::LeanObject,
    mut v_entries_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1685_: usize = 0;
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1685_ = leanh::lean_unbox_usize(v_depth_1679_);
    leanh::lean_dec(v_depth_1679_);
    v_res_1686_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__5(v_00_u03b2_1678_, v_depth_boxed_1685_, v_keys_1680_, v_vals_1681_, v_heq_1682_, v_i_1683_, v_entries_1684_);
    leanh::lean_dec_ref(v_vals_1681_);
    leanh::lean_dec_ref(v_keys_1680_);
    return v_res_1686_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8(
    mut v_00_u03b2_1687_: *mut leanh::LeanObject,
    mut v_x_1688_: *mut leanh::LeanObject,
    mut v_x_1689_: *mut leanh::LeanObject,
    mut v_x_1690_: *mut leanh::LeanObject,
    mut v_x_1691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_AC_internalize_spec__1_spec__2_spec__4_spec__8___redArg(v_x_1688_, v_x_1689_, v_x_1690_, v_x_1691_);
    return v___x_1692_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_AC_Internalize(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_AC_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_AC_DenoteExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_AC_Internalize(builtin);
}