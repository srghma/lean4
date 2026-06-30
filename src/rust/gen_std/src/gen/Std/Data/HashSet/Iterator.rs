// Lean compiler output
// Module: Std.Data.HashSet.Iterator
// Imports: Std.Data.HashMap.Iterator Std.Data.HashSet.Basic Std.Data.HashSet.Raw Init.Data.Iterators.Combinators.FilterMap
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Std::Data::HashMap::Iterator::{
    initialize_Std_Data_HashMap_Iterator, runtime_initialize_Std_Data_HashMap_Iterator,
};
use crate::r#gen::Std::Data::HashSet::Basic::{
    initialize_Std_Data_HashSet_Basic, runtime_initialize_Std_Data_HashSet_Basic,
};
use crate::r#gen::Std::Data::HashSet::Raw::{
    initialize_Std_Data_HashSet_Raw, runtime_initialize_Std_Data_HashSet_Raw,
};
pub unsafe fn l_Std_HashSet_Raw_iter___redArg(
    mut v_m_62_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_63_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_66_: u8 = 0;
    let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_73_: u8 = 0;
    let mut v_unused_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_63_ = leanh::lean_ctor_get(v_m_62_, 1);
                v_isSharedCheck_73_ = (!leanh::lean_is_exclusive(v_m_62_)) as u8;
                if v_isSharedCheck_73_ == 0 {
                    v_unused_74_ = leanh::lean_ctor_get(v_m_62_, 0);
                    leanh::lean_dec(v_unused_74_);
                    v___x_65_ = v_m_62_;
                    v_isShared_66_ = v_isSharedCheck_73_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_63_);
                    leanh::lean_dec(v_m_62_);
                    v___x_65_ = leanh::lean_box(0);
                    v_isShared_66_ = v_isSharedCheck_73_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_67_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_66_ == 0 {
                    leanh::lean_ctor_set(v___x_65_, 1, v___x_67_);
                    leanh::lean_ctor_set(v___x_65_, 0, v_buckets_63_);
                    v___x_69_ = v___x_65_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_72_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_72_, 0, v_buckets_63_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_72_, 1, v___x_67_);
                    v___x_69_ = v_reuseFailAlloc_72_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_70_ = leanh::lean_box(0);
                v___x_71_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_71_, 0, v___x_69_);
                leanh::lean_ctor_set(v___x_71_, 1, v___x_70_);
                return v___x_71_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_Raw_iter(
    mut v_00_u03b1_75_: *mut leanh::LeanObject,
    mut v_m_76_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_77_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_80_: u8 = 0;
    let mut v___x_81_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_86_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_87_: u8 = 0;
    let mut v_unused_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_77_ = leanh::lean_ctor_get(v_m_76_, 1);
                v_isSharedCheck_87_ = (!leanh::lean_is_exclusive(v_m_76_)) as u8;
                if v_isSharedCheck_87_ == 0 {
                    v_unused_88_ = leanh::lean_ctor_get(v_m_76_, 0);
                    leanh::lean_dec(v_unused_88_);
                    v___x_79_ = v_m_76_;
                    v_isShared_80_ = v_isSharedCheck_87_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_77_);
                    leanh::lean_dec(v_m_76_);
                    v___x_79_ = leanh::lean_box(0);
                    v_isShared_80_ = v_isSharedCheck_87_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_81_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_80_ == 0 {
                    leanh::lean_ctor_set(v___x_79_, 1, v___x_81_);
                    leanh::lean_ctor_set(v___x_79_, 0, v_buckets_77_);
                    v___x_83_ = v___x_79_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_86_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_86_, 0, v_buckets_77_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_86_, 1, v___x_81_);
                    v___x_83_ = v_reuseFailAlloc_86_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_84_ = leanh::lean_box(0);
                v___x_85_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_85_, 0, v___x_83_);
                leanh::lean_ctor_set(v___x_85_, 1, v___x_84_);
                return v___x_85_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_iter___redArg(
    mut v_m_89_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_92_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_93_: u8 = 0;
    let mut v___x_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_100_: u8 = 0;
    let mut v_unused_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_90_ = leanh::lean_ctor_get(v_m_89_, 1);
                v_isSharedCheck_100_ = (!leanh::lean_is_exclusive(v_m_89_)) as u8;
                if v_isSharedCheck_100_ == 0 {
                    v_unused_101_ = leanh::lean_ctor_get(v_m_89_, 0);
                    leanh::lean_dec(v_unused_101_);
                    v___x_92_ = v_m_89_;
                    v_isShared_93_ = v_isSharedCheck_100_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_90_);
                    leanh::lean_dec(v_m_89_);
                    v___x_92_ = leanh::lean_box(0);
                    v_isShared_93_ = v_isSharedCheck_100_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_94_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_93_ == 0 {
                    leanh::lean_ctor_set(v___x_92_, 1, v___x_94_);
                    leanh::lean_ctor_set(v___x_92_, 0, v_buckets_90_);
                    v___x_96_ = v___x_92_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_99_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_99_, 0, v_buckets_90_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_99_, 1, v___x_94_);
                    v___x_96_ = v_reuseFailAlloc_99_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_97_ = leanh::lean_box(0);
                v___x_98_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_98_, 0, v___x_96_);
                leanh::lean_ctor_set(v___x_98_, 1, v___x_97_);
                return v___x_98_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_iter(
    mut v_00_u03b1_102_: *mut leanh::LeanObject,
    mut v_inst_103_: *mut leanh::LeanObject,
    mut v_inst_104_: *mut leanh::LeanObject,
    mut v_m_105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_109_: u8 = 0;
    let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_116_: u8 = 0;
    let mut v_unused_117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_106_ = leanh::lean_ctor_get(v_m_105_, 1);
                v_isSharedCheck_116_ = (!leanh::lean_is_exclusive(v_m_105_)) as u8;
                if v_isSharedCheck_116_ == 0 {
                    v_unused_117_ = leanh::lean_ctor_get(v_m_105_, 0);
                    leanh::lean_dec(v_unused_117_);
                    v___x_108_ = v_m_105_;
                    v_isShared_109_ = v_isSharedCheck_116_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_106_);
                    leanh::lean_dec(v_m_105_);
                    v___x_108_ = leanh::lean_box(0);
                    v_isShared_109_ = v_isSharedCheck_116_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_110_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_109_ == 0 {
                    leanh::lean_ctor_set(v___x_108_, 1, v___x_110_);
                    leanh::lean_ctor_set(v___x_108_, 0, v_buckets_106_);
                    v___x_112_ = v___x_108_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_115_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_115_, 0, v_buckets_106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_115_, 1, v___x_110_);
                    v___x_112_ = v_reuseFailAlloc_115_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_113_ = leanh::lean_box(0);
                v___x_114_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_114_, 0, v___x_112_);
                leanh::lean_ctor_set(v___x_114_, 1, v___x_113_);
                return v___x_114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_HashSet_iter___boxed(
    mut v_00_u03b1_118_: *mut leanh::LeanObject,
    mut v_inst_119_: *mut leanh::LeanObject,
    mut v_inst_120_: *mut leanh::LeanObject,
    mut v_m_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = l_Std_HashSet_iter(v_00_u03b1_118_, v_inst_119_, v_inst_120_, v_m_121_);
    leanh::lean_dec_ref(v_inst_120_);
    leanh::lean_dec_ref(v_inst_119_);
    return v_res_122_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_HashSet_Iterator(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_HashMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_HashSet_Iterator(
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
pub unsafe fn initialize_Std_Data_HashSet_Iterator(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_HashMap_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Data_HashSet_Raw(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_HashSet_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_HashSet_Iterator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_HashSet_Iterator(builtin);
}