// Lean compiler output
// Module: Lean.Elab.Tactic.Grind.Anchor
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::ffi::{
    lean_mk_empty_array_with_capacity, lean_nat_dec_le, lean_st_ref_get, lean_uint64_of_nat,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_TSyntax_getHexNumSize, l_Lean_TSyntax_getHexNumVal};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__1_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 97, 110, 99, 104, 111, 114, 44, 32, 118, 97, 108,
        117, 101, 32, 105, 115, 32, 116, 111, 111, 32, 98, 105, 103, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_100_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_100_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_101_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__0);
    v___x_102_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_102_, 0, v___x_101_);
    return v___x_102_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_103_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__1);
    v___x_104_ = leanh::lean_unsigned_to_nat(0);
    v___x_105_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_105_, 0, v___x_104_);
    leanh::lean_ctor_set(v___x_105_, 1, v___x_104_);
    leanh::lean_ctor_set(v___x_105_, 2, v___x_104_);
    leanh::lean_ctor_set(v___x_105_, 3, v___x_104_);
    leanh::lean_ctor_set(v___x_105_, 4, v___x_103_);
    leanh::lean_ctor_set(v___x_105_, 5, v___x_103_);
    leanh::lean_ctor_set(v___x_105_, 6, v___x_103_);
    leanh::lean_ctor_set(v___x_105_, 7, v___x_103_);
    leanh::lean_ctor_set(v___x_105_, 8, v___x_103_);
    leanh::lean_ctor_set(v___x_105_, 9, v___x_103_);
    return v___x_105_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_106_ = leanh::lean_unsigned_to_nat(32);
    v___x_107_ = lean_mk_empty_array_with_capacity(v___x_106_);
    v___x_108_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_108_, 0, v___x_107_);
    return v___x_108_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_109_: usize = 0;
    let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_109_ = 5usize;
    v___x_110_ = leanh::lean_unsigned_to_nat(0);
    v___x_111_ = leanh::lean_unsigned_to_nat(32);
    v___x_112_ = lean_mk_empty_array_with_capacity(v___x_111_);
    v___x_113_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__3);
    v___x_114_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_114_, 0, v___x_113_);
    leanh::lean_ctor_set(v___x_114_, 1, v___x_112_);
    leanh::lean_ctor_set(v___x_114_, 2, v___x_110_);
    leanh::lean_ctor_set(v___x_114_, 3, v___x_110_);
    leanh::lean_ctor_set_usize(v___x_114_, 4, v___x_109_);
    return v___x_114_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_115_ = leanh::lean_box(1);
    v___x_116_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__4);
    v___x_117_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__1);
    v___x_118_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_118_, 0, v___x_117_);
    leanh::lean_ctor_set(v___x_118_, 1, v___x_116_);
    leanh::lean_ctor_set(v___x_118_, 2, v___x_115_);
    return v___x_118_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0(
    mut v_msgData_119_: *mut leanh::LeanObject,
    mut v___y_120_: *mut leanh::LeanObject,
    mut v___y_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_123_ = lean_st_ref_get(v___y_121_);
    v_env_124_ = leanh::lean_ctor_get(v___x_123_, 0);
    leanh::lean_inc_ref(v_env_124_);
    leanh::lean_dec(v___x_123_);
    v_options_125_ = leanh::lean_ctor_get(v___y_120_, 2);
    v___x_126_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__2);
    v___x_127_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_125_);
    v___x_128_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_128_, 0, v_env_124_);
    leanh::lean_ctor_set(v___x_128_, 1, v___x_126_);
    leanh::lean_ctor_set(v___x_128_, 2, v___x_127_);
    leanh::lean_ctor_set(v___x_128_, 3, v_options_125_);
    v___x_129_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_129_, 0, v___x_128_);
    leanh::lean_ctor_set(v___x_129_, 1, v_msgData_119_);
    v___x_130_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_130_, 0, v___x_129_);
    return v___x_130_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0___boxed(
    mut v_msgData_131_: *mut leanh::LeanObject,
    mut v___y_132_: *mut leanh::LeanObject,
    mut v___y_133_: *mut leanh::LeanObject,
    mut v___y_134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_135_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0(v_msgData_131_, v___y_132_, v___y_133_);
    leanh::lean_dec(v___y_133_);
    leanh::lean_dec_ref(v___y_132_);
    return v_res_135_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0___redArg(
    mut v_msg_136_: *mut leanh::LeanObject,
    mut v___y_137_: *mut leanh::LeanObject,
    mut v___y_138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_145_: u8 = 0;
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_150_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_140_ = leanh::lean_ctor_get(v___y_137_, 5);
                v___x_141_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0_spec__0(v_msg_136_, v___y_137_, v___y_138_);
                v_a_142_ = leanh::lean_ctor_get(v___x_141_, 0);
                v_isSharedCheck_150_ = (!leanh::lean_is_exclusive(v___x_141_)) as u8;
                if v_isSharedCheck_150_ == 0 {
                    v___x_144_ = v___x_141_;
                    v_isShared_145_ = v_isSharedCheck_150_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_142_);
                    leanh::lean_dec(v___x_141_);
                    v___x_144_ = leanh::lean_box(0);
                    v_isShared_145_ = v_isSharedCheck_150_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_140_);
                v___x_146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_146_, 0, v_ref_140_);
                leanh::lean_ctor_set(v___x_146_, 1, v_a_142_);
                if v_isShared_145_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_144_, 1);
                    leanh::lean_ctor_set(v___x_144_, 0, v___x_146_);
                    v___x_148_ = v___x_144_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_149_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_146_);
                    v___x_148_ = v_reuseFailAlloc_149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0___redArg___boxed(
    mut v_msg_151_: *mut leanh::LeanObject,
    mut v___y_152_: *mut leanh::LeanObject,
    mut v___y_153_: *mut leanh::LeanObject,
    mut v___y_154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_155_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0___redArg(
        v_msg_151_, v___y_152_, v___y_153_,
    );
    leanh::lean_dec(v___y_153_);
    leanh::lean_dec_ref(v___y_152_);
    return v_res_155_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_156_ = leanh::lean_cstr_to_nat(b"18446744073709551616\0".as_ptr().cast());
    return v___x_156_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_158_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__1;
    v___x_159_ = l_Lean_stringToMessageData(v___x_158_);
    return v___x_159_;
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabAnchorRef(
    mut v_anchor_160_: *mut leanh::LeanObject,
    mut v_a_161_: *mut leanh::LeanObject,
    mut v_a_162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_numDigits_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_anchorPrefix_167_: u64 = 0;
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: u8 = 0;
    let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_177_: u8 = 0;
    let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numDigits_164_ = l_Lean_TSyntax_getHexNumSize(v_anchor_160_);
                v_val_165_ = l_Lean_TSyntax_getHexNumVal(v_anchor_160_);
                v___x_170_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__0),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__0_once
                    ),
                    _init_l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__0,
                );
                v___x_171_ = lean_nat_dec_le(v___x_170_, v_val_165_);
                if v___x_171_ == 0 {
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_val_165_);
                    leanh::lean_dec(v_numDigits_164_);
                    v___x_172_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__2_once
                        ),
                        _init_l_Lean_Elab_Tactic_Grind_elabAnchorRef___closed__2,
                    );
                    v___x_173_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0___redArg(v___x_172_, v_a_161_, v_a_162_);
                    v_a_174_ = leanh::lean_ctor_get(v___x_173_, 0);
                    v_isSharedCheck_181_ = (!leanh::lean_is_exclusive(v___x_173_)) as u8;
                    if v_isSharedCheck_181_ == 0 {
                        v___x_176_ = v___x_173_;
                        v_isShared_177_ = v_isSharedCheck_181_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_174_);
                        leanh::lean_dec(v___x_173_);
                        v___x_176_ = leanh::lean_box(0);
                        v_isShared_177_ = v_isSharedCheck_181_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v_anchorPrefix_167_ = lean_uint64_of_nat(v_val_165_);
                leanh::lean_dec(v_val_165_);
                v___x_168_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_168_, 0, v_numDigits_164_);
                leanh::lean_ctor_set_uint64(
                    v___x_168_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_anchorPrefix_167_,
                );
                v___x_169_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_169_, 0, v___x_168_);
                return v___x_169_;
            }
            2 => {
                if v_isShared_177_ == 0 {
                    v___x_179_ = v___x_176_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_180_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_180_, 0, v_a_174_);
                    v___x_179_ = v_reuseFailAlloc_180_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Grind_elabAnchorRef___boxed(
    mut v_anchor_182_: *mut leanh::LeanObject,
    mut v_a_183_: *mut leanh::LeanObject,
    mut v_a_184_: *mut leanh::LeanObject,
    mut v_a_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_186_ = l_Lean_Elab_Tactic_Grind_elabAnchorRef(v_anchor_182_, v_a_183_, v_a_184_);
    leanh::lean_dec(v_a_184_);
    leanh::lean_dec_ref(v_a_183_);
    leanh::lean_dec(v_anchor_182_);
    return v_res_186_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0(
    mut v_00_u03b1_187_: *mut leanh::LeanObject,
    mut v_msg_188_: *mut leanh::LeanObject,
    mut v___y_189_: *mut leanh::LeanObject,
    mut v___y_190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_192_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0___redArg(
        v_msg_188_, v___y_189_, v___y_190_,
    );
    return v___x_192_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0___boxed(
    mut v_00_u03b1_193_: *mut leanh::LeanObject,
    mut v_msg_194_: *mut leanh::LeanObject,
    mut v___y_195_: *mut leanh::LeanObject,
    mut v___y_196_: *mut leanh::LeanObject,
    mut v___y_197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_198_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Grind_elabAnchorRef_spec__0(
        v_00_u03b1_193_,
        v_msg_194_,
        v___y_195_,
        v___y_196_,
    );
    leanh::lean_dec(v___y_196_);
    leanh::lean_dec_ref(v___y_195_);
    return v_res_198_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Grind_Anchor(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Grind_Anchor(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Grind_Anchor(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Grind_Anchor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Grind_Anchor(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Grind_Anchor(builtin);
}