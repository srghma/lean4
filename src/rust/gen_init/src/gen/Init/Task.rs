// Lean compiler output
// Module: Init.Task
// Imports: Init.Core Init.Data.List.Basic Init.Data.Nat.Bitwise.Basic
use crate::ffi::{lean_task_bind, lean_task_map, lean_task_pure, lean_task_spawn};
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::r#gen::Init::Data::List::Basic::{
    initialize_Init_Data_List_Basic, l_List_reverse___redArg,
    runtime_initialize_Init_Data_List_Basic,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
pub unsafe fn l___private_Init_Task_0__Task_mapList_go___redArg___lam__0(
    mut v_x_97_: *mut crate::leanh::LeanObject,
    mut v_f_98_: *mut crate::leanh::LeanObject,
    mut v_x_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_100_ = l_List_reverse___redArg(v_x_97_);
    v___x_101_ = crate::leanh::lean_apply_1(v_f_98_, v___x_100_);
    return v___x_101_;
}
pub unsafe fn l___private_Init_Task_0__Task_mapList_go___redArg___lam__1(
    mut v_x_102_: *mut crate::leanh::LeanObject,
    mut v_f_103_: *mut crate::leanh::LeanObject,
    mut v_a_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_105_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_105_, 0, v_a_104_);
    crate::leanh::lean_ctor_set(v___x_105_, 1, v_x_102_);
    v___x_106_ = l_List_reverse___redArg(v___x_105_);
    v___x_107_ = crate::leanh::lean_apply_1(v_f_103_, v___x_106_);
    return v___x_107_;
}
pub unsafe fn l___private_Init_Task_0__Task_mapList_go___redArg___lam__2___boxed(
    mut v_x_108_: *mut crate::leanh::LeanObject,
    mut v_f_109_: *mut crate::leanh::LeanObject,
    mut v_prio_110_: *mut crate::leanh::LeanObject,
    mut v_sync_111_: *mut crate::leanh::LeanObject,
    mut v_tail_112_: *mut crate::leanh::LeanObject,
    mut v_a_113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_114_: u8 = 0;
    let mut v_res_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_114_ = (crate::leanh::lean_unbox(v_sync_111_) as u8);
    v_res_115_ = l___private_Init_Task_0__Task_mapList_go___redArg___lam__2(
        v_x_108_,
        v_f_109_,
        v_prio_110_,
        v_sync_boxed_114_,
        v_tail_112_,
        v_a_113_,
    );
    return v_res_115_;
}
pub unsafe fn l___private_Init_Task_0__Task_mapList_go___redArg(
    mut v_f_116_: *mut crate::leanh::LeanObject,
    mut v_prio_117_: *mut crate::leanh::LeanObject,
    mut v_sync_118_: u8,
    mut v_x_119_: *mut crate::leanh::LeanObject,
    mut v_x_120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_119_) == 0 {
        if v_sync_118_ == 0 {
            let mut v___f_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___f_121_ = crate::leanh::lean_alloc_closure(
                l___private_Init_Task_0__Task_mapList_go___redArg___lam__0
                    as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_121_, 0, v_x_120_);
            crate::leanh::lean_closure_set(v___f_121_, 1, v_f_116_);
            v___x_122_ = lean_task_spawn(v___f_121_, v_prio_117_);
            return v___x_122_;
        } else {
            let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_prio_117_);
            v___x_123_ = l_List_reverse___redArg(v_x_120_);
            v___x_124_ = crate::leanh::lean_apply_1(v_f_116_, v___x_123_);
            v___x_125_ = lean_task_pure(v___x_124_);
            return v___x_125_;
        }
    } else {
        let mut v_tail_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_126_ = crate::leanh::lean_ctor_get(v_x_119_, 1);
        if crate::leanh::lean_obj_tag(v_tail_126_) == 0 {
            let mut v_head_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_127_ = crate::leanh::lean_ctor_get(v_x_119_, 0);
            crate::leanh::lean_inc(v_head_127_);
            crate::leanh::lean_dec_ref_known(v_x_119_, 2);
            v___f_128_ = crate::leanh::lean_alloc_closure(
                l___private_Init_Task_0__Task_mapList_go___redArg___lam__1
                    as *mut core::ffi::c_void,
                3,
                2,
            );
            crate::leanh::lean_closure_set(v___f_128_, 0, v_x_120_);
            crate::leanh::lean_closure_set(v___f_128_, 1, v_f_116_);
            v___x_129_ = lean_task_map(v___f_128_, v_head_127_, v_prio_117_, v_sync_118_);
            return v___x_129_;
        } else {
            let mut v_head_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_126_);
            v_head_130_ = crate::leanh::lean_ctor_get(v_x_119_, 0);
            crate::leanh::lean_inc(v_head_130_);
            crate::leanh::lean_dec_ref_known(v_x_119_, 2);
            v___x_131_ = crate::leanh::lean_box((v_sync_118_) as usize);
            crate::leanh::lean_inc(v_prio_117_);
            v___f_132_ = crate::leanh::lean_alloc_closure(
                l___private_Init_Task_0__Task_mapList_go___redArg___lam__2___boxed
                    as *mut core::ffi::c_void,
                6,
                5,
            );
            crate::leanh::lean_closure_set(v___f_132_, 0, v_x_120_);
            crate::leanh::lean_closure_set(v___f_132_, 1, v_f_116_);
            crate::leanh::lean_closure_set(v___f_132_, 2, v_prio_117_);
            crate::leanh::lean_closure_set(v___f_132_, 3, v___x_131_);
            crate::leanh::lean_closure_set(v___f_132_, 4, v_tail_126_);
            v___x_133_ = lean_task_bind(v_head_130_, v___f_132_, v_prio_117_, v_sync_118_);
            return v___x_133_;
        }
    }
}
pub unsafe fn l___private_Init_Task_0__Task_mapList_go___redArg___lam__2(
    mut v_x_134_: *mut crate::leanh::LeanObject,
    mut v_f_135_: *mut crate::leanh::LeanObject,
    mut v_prio_136_: *mut crate::leanh::LeanObject,
    mut v_sync_137_: u8,
    mut v_tail_138_: *mut crate::leanh::LeanObject,
    mut v_a_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_140_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_140_, 0, v_a_139_);
    crate::leanh::lean_ctor_set(v___x_140_, 1, v_x_134_);
    v___x_141_ = l___private_Init_Task_0__Task_mapList_go___redArg(
        v_f_135_,
        v_prio_136_,
        v_sync_137_,
        v_tail_138_,
        v___x_140_,
    );
    return v___x_141_;
}
pub unsafe fn l___private_Init_Task_0__Task_mapList_go___redArg___boxed(
    mut v_f_142_: *mut crate::leanh::LeanObject,
    mut v_prio_143_: *mut crate::leanh::LeanObject,
    mut v_sync_144_: *mut crate::leanh::LeanObject,
    mut v_x_145_: *mut crate::leanh::LeanObject,
    mut v_x_146_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_147_: u8 = 0;
    let mut v_res_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_147_ = (crate::leanh::lean_unbox(v_sync_144_) as u8);
    v_res_148_ = l___private_Init_Task_0__Task_mapList_go___redArg(
        v_f_142_,
        v_prio_143_,
        v_sync_boxed_147_,
        v_x_145_,
        v_x_146_,
    );
    return v_res_148_;
}
pub unsafe fn l___private_Init_Task_0__Task_mapList_go(
    mut v_00_u03b1_149_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_150_: *mut crate::leanh::LeanObject,
    mut v_f_151_: *mut crate::leanh::LeanObject,
    mut v_prio_152_: *mut crate::leanh::LeanObject,
    mut v_sync_153_: u8,
    mut v_x_154_: *mut crate::leanh::LeanObject,
    mut v_x_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_156_ = l___private_Init_Task_0__Task_mapList_go___redArg(
        v_f_151_,
        v_prio_152_,
        v_sync_153_,
        v_x_154_,
        v_x_155_,
    );
    return v___x_156_;
}
pub unsafe fn l___private_Init_Task_0__Task_mapList_go___boxed(
    mut v_00_u03b1_157_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_158_: *mut crate::leanh::LeanObject,
    mut v_f_159_: *mut crate::leanh::LeanObject,
    mut v_prio_160_: *mut crate::leanh::LeanObject,
    mut v_sync_161_: *mut crate::leanh::LeanObject,
    mut v_x_162_: *mut crate::leanh::LeanObject,
    mut v_x_163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_164_: u8 = 0;
    let mut v_res_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_164_ = (crate::leanh::lean_unbox(v_sync_161_) as u8);
    v_res_165_ = l___private_Init_Task_0__Task_mapList_go(
        v_00_u03b1_157_,
        v_00_u03b2_158_,
        v_f_159_,
        v_prio_160_,
        v_sync_boxed_164_,
        v_x_162_,
        v_x_163_,
    );
    return v_res_165_;
}
pub unsafe fn l_Task_mapList___redArg(
    mut v_f_166_: *mut crate::leanh::LeanObject,
    mut v_tasks_167_: *mut crate::leanh::LeanObject,
    mut v_prio_168_: *mut crate::leanh::LeanObject,
    mut v_sync_169_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_170_ = crate::leanh::lean_box(0);
    v___x_171_ = l___private_Init_Task_0__Task_mapList_go___redArg(
        v_f_166_,
        v_prio_168_,
        v_sync_169_,
        v_tasks_167_,
        v___x_170_,
    );
    return v___x_171_;
}
pub unsafe fn l_Task_mapList___redArg___boxed(
    mut v_f_172_: *mut crate::leanh::LeanObject,
    mut v_tasks_173_: *mut crate::leanh::LeanObject,
    mut v_prio_174_: *mut crate::leanh::LeanObject,
    mut v_sync_175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_176_: u8 = 0;
    let mut v_res_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_176_ = (crate::leanh::lean_unbox(v_sync_175_) as u8);
    v_res_177_ = l_Task_mapList___redArg(v_f_172_, v_tasks_173_, v_prio_174_, v_sync_boxed_176_);
    return v_res_177_;
}
pub unsafe fn l_Task_mapList(
    mut v_00_u03b1_178_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_179_: *mut crate::leanh::LeanObject,
    mut v_f_180_: *mut crate::leanh::LeanObject,
    mut v_tasks_181_: *mut crate::leanh::LeanObject,
    mut v_prio_182_: *mut crate::leanh::LeanObject,
    mut v_sync_183_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_184_ = l_Task_mapList___redArg(v_f_180_, v_tasks_181_, v_prio_182_, v_sync_183_);
    return v___x_184_;
}
pub unsafe fn l_Task_mapList___boxed(
    mut v_00_u03b1_185_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_186_: *mut crate::leanh::LeanObject,
    mut v_f_187_: *mut crate::leanh::LeanObject,
    mut v_tasks_188_: *mut crate::leanh::LeanObject,
    mut v_prio_189_: *mut crate::leanh::LeanObject,
    mut v_sync_190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sync_boxed_191_: u8 = 0;
    let mut v_res_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sync_boxed_191_ = (crate::leanh::lean_unbox(v_sync_190_) as u8);
    v_res_192_ = l_Task_mapList(
        v_00_u03b1_185_,
        v_00_u03b2_186_,
        v_f_187_,
        v_tasks_188_,
        v_prio_189_,
        v_sync_boxed_191_,
    );
    return v_res_192_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Task(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Task(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Task(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Task(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Task(builtin);
}
