// Lean compiler output
// Module: Lean.Meta.RecExt
// Imports: Lean.Attributes
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::EnvExtension::{
    l_Lean_TagDeclarationExtension_isTagged, l_Lean_TagDeclarationExtension_tag,
    l_Lean_mkTagDeclarationExtension,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [114, 101, 99, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3474255721224650759 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 3 }, m_objs: [1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_recExt: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_markAsRecursive___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_markAsRecursive___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_markAsRecursive___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_markAsRecursive___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_markAsRecursive___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_markAsRecursive___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_88_ = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_;
    v___x_89_ = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_;
    v___x_90_ = l_Lean_mkTagDeclarationExtension(v___x_88_, v___x_89_);
    return v___x_90_;
}
pub unsafe fn l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2____boxed(
    mut v_a_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_92_ = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
    return v_res_92_;
}
pub unsafe fn _init_l_Lean_Meta_markAsRecursive___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_93_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_93_;
}
pub unsafe fn _init_l_Lean_Meta_markAsRecursive___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_94_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_markAsRecursive___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_markAsRecursive___redArg___closed__0_once),
        _init_l_Lean_Meta_markAsRecursive___redArg___closed__0,
    );
    v___x_95_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_95_, 0, v___x_94_);
    return v___x_95_;
}
pub unsafe fn _init_l_Lean_Meta_markAsRecursive___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_markAsRecursive___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_markAsRecursive___redArg___closed__1_once),
        _init_l_Lean_Meta_markAsRecursive___redArg___closed__1,
    );
    v___x_97_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_97_, 0, v___x_96_);
    crate::leanh::lean_ctor_set(v___x_97_, 1, v___x_96_);
    return v___x_97_;
}
pub unsafe fn l_Lean_Meta_markAsRecursive___redArg(
    mut v_declName_98_: *mut crate::leanh::LeanObject,
    mut v_a_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_112_: u8 = 0;
    let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_122_: u8 = 0;
    let mut v_unused_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_101_ = lean_st_ref_take(v_a_99_);
                v_env_102_ = crate::leanh::lean_ctor_get(v___x_101_, 0);
                v_nextMacroScope_103_ = crate::leanh::lean_ctor_get(v___x_101_, 1);
                v_ngen_104_ = crate::leanh::lean_ctor_get(v___x_101_, 2);
                v_auxDeclNGen_105_ = crate::leanh::lean_ctor_get(v___x_101_, 3);
                v_traceState_106_ = crate::leanh::lean_ctor_get(v___x_101_, 4);
                v_messages_107_ = crate::leanh::lean_ctor_get(v___x_101_, 6);
                v_infoState_108_ = crate::leanh::lean_ctor_get(v___x_101_, 7);
                v_snapshotTasks_109_ = crate::leanh::lean_ctor_get(v___x_101_, 8);
                v_isSharedCheck_122_ = (!crate::leanh::lean_is_exclusive(v___x_101_)) as u8;
                if v_isSharedCheck_122_ == 0 {
                    v_unused_123_ = crate::leanh::lean_ctor_get(v___x_101_, 5);
                    crate::leanh::lean_dec(v_unused_123_);
                    v___x_111_ = v___x_101_;
                    v_isShared_112_ = v_isSharedCheck_122_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_109_);
                    crate::leanh::lean_inc(v_infoState_108_);
                    crate::leanh::lean_inc(v_messages_107_);
                    crate::leanh::lean_inc(v_traceState_106_);
                    crate::leanh::lean_inc(v_auxDeclNGen_105_);
                    crate::leanh::lean_inc(v_ngen_104_);
                    crate::leanh::lean_inc(v_nextMacroScope_103_);
                    crate::leanh::lean_inc(v_env_102_);
                    crate::leanh::lean_dec(v___x_101_);
                    v___x_111_ = crate::leanh::lean_box(0);
                    v_isShared_112_ = v_isSharedCheck_122_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_113_ = l_Lean_Meta_recExt;
                v___x_114_ =
                    l_Lean_TagDeclarationExtension_tag(v___x_113_, v_env_102_, v_declName_98_);
                v___x_115_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_markAsRecursive___redArg___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_Meta_markAsRecursive___redArg___closed__2_once),
                    _init_l_Lean_Meta_markAsRecursive___redArg___closed__2,
                );
                if v_isShared_112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_111_, 5, v___x_115_);
                    crate::leanh::lean_ctor_set(v___x_111_, 0, v___x_114_);
                    v___x_117_ = v___x_111_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_121_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_121_, 0, v___x_114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_121_, 1, v_nextMacroScope_103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_121_, 2, v_ngen_104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_121_, 3, v_auxDeclNGen_105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_121_, 4, v_traceState_106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_121_, 5, v___x_115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_121_, 6, v_messages_107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_121_, 7, v_infoState_108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_121_, 8, v_snapshotTasks_109_);
                    v___x_117_ = v_reuseFailAlloc_121_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_118_ = lean_st_ref_set(v_a_99_, v___x_117_);
                v___x_119_ = crate::leanh::lean_box(0);
                v___x_120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_120_, 0, v___x_119_);
                return v___x_120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_markAsRecursive___redArg___boxed(
    mut v_declName_124_: *mut crate::leanh::LeanObject,
    mut v_a_125_: *mut crate::leanh::LeanObject,
    mut v_a_126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_127_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_124_, v_a_125_);
    crate::leanh::lean_dec(v_a_125_);
    return v_res_127_;
}
pub unsafe fn l_Lean_Meta_markAsRecursive(
    mut v_declName_128_: *mut crate::leanh::LeanObject,
    mut v_a_129_: *mut crate::leanh::LeanObject,
    mut v_a_130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_132_ = l_Lean_Meta_markAsRecursive___redArg(v_declName_128_, v_a_130_);
    return v___x_132_;
}
pub unsafe fn l_Lean_Meta_markAsRecursive___boxed(
    mut v_declName_133_: *mut crate::leanh::LeanObject,
    mut v_a_134_: *mut crate::leanh::LeanObject,
    mut v_a_135_: *mut crate::leanh::LeanObject,
    mut v_a_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_137_ = l_Lean_Meta_markAsRecursive(v_declName_133_, v_a_134_, v_a_135_);
    crate::leanh::lean_dec(v_a_135_);
    crate::leanh::lean_dec_ref(v_a_134_);
    return v_res_137_;
}
pub unsafe fn l_Lean_Meta_isRecursiveDefinition___redArg(
    mut v_declName_138_: *mut crate::leanh::LeanObject,
    mut v_a_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: u8 = 0;
    let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_141_ = lean_st_ref_get(v_a_139_);
    v_env_142_ = crate::leanh::lean_ctor_get(v___x_141_, 0);
    crate::leanh::lean_inc_ref(v_env_142_);
    crate::leanh::lean_dec(v___x_141_);
    v___x_143_ = l_Lean_Meta_recExt;
    v_toEnvExtension_144_ = crate::leanh::lean_ctor_get(v___x_143_, 0);
    v_asyncMode_145_ = crate::leanh::lean_ctor_get(v_toEnvExtension_144_, 2);
    v___x_146_ = l_Lean_TagDeclarationExtension_isTagged(
        v___x_143_,
        v_env_142_,
        v_declName_138_,
        v_asyncMode_145_,
    );
    v___x_147_ = crate::leanh::lean_box((v___x_146_) as usize);
    v___x_148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_148_, 0, v___x_147_);
    return v___x_148_;
}
pub unsafe fn l_Lean_Meta_isRecursiveDefinition___redArg___boxed(
    mut v_declName_149_: *mut crate::leanh::LeanObject,
    mut v_a_150_: *mut crate::leanh::LeanObject,
    mut v_a_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_152_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_149_, v_a_150_);
    crate::leanh::lean_dec(v_a_150_);
    return v_res_152_;
}
pub unsafe fn l_Lean_Meta_isRecursiveDefinition(
    mut v_declName_153_: *mut crate::leanh::LeanObject,
    mut v_a_154_: *mut crate::leanh::LeanObject,
    mut v_a_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_157_ = l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_153_, v_a_155_);
    return v___x_157_;
}
pub unsafe fn l_Lean_Meta_isRecursiveDefinition___boxed(
    mut v_declName_158_: *mut crate::leanh::LeanObject,
    mut v_a_159_: *mut crate::leanh::LeanObject,
    mut v_a_160_: *mut crate::leanh::LeanObject,
    mut v_a_161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_162_ = l_Lean_Meta_isRecursiveDefinition(v_declName_158_, v_a_159_, v_a_160_);
    crate::leanh::lean_dec(v_a_160_);
    crate::leanh::lean_dec_ref(v_a_159_);
    return v_res_162_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_RecExt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_RecExt_0__Lean_Meta_initFn_00___x40_Lean_Meta_RecExt_2067193597____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_recExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_recExt);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_RecExt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_RecExt(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_RecExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_RecExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_RecExt(builtin);
}
