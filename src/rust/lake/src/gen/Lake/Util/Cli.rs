// Lean compiler output
// Module: Lake.Util.Cli
// Imports: Init.Data.String.TakeDrop Init.Data.String.Search Init.Data.String.Length
use crate::ffi::{
    lean_array_push, lean_array_to_list, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
    lean_string_utf8_at_end, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
    lean_uint32_dec_eq,
};
use crate::r#gen::Init::Data::Char::Basic::l_Char_isWhitespace___boxed;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_nextn;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::String::Pattern::Pred::l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_Pos_skipWhile___redArg;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub static l_Lake_ArgsT_run_x27___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_ArgsT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ArgsT_run_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ArgsT_run_x27___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_takeArg_x3f___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_takeArg_x3f___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_takeArg_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_takeArg_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_takeArgs___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_takeArgs___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_takeArgs___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_takeArgs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_shortOptionWithSpace___redArg___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Char_isWhitespace___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_shortOptionWithSpace___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_shortOptionWithSpace___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lake_shortOptionWithSpace___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_shortOptionWithSpace___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_collectArgs___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_collectArgs___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_collectArgs___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_collectArgs___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_processOptions___redArg___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lake_processOptions___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_processOptions___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_ArgList_mk(
    mut v_args_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_args_1326_);
    return v_args_1326_;
}
pub unsafe fn l_Lake_ArgList_mk___boxed(
    mut v_args_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1328_ = l_Lake_ArgList_mk(v_args_1327_);
    leanh::lean_dec(v_args_1327_);
    return v_res_1328_;
}
pub unsafe fn l_Lake_ArgsT_run___redArg(
    mut v_args_1329_: *mut leanh::LeanObject,
    mut v_self_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1331_ = leanh::lean_apply_1(v_self_1330_, v_args_1329_);
    return v___x_1331_;
}
pub unsafe fn l_Lake_ArgsT_run(
    mut v_m_1332_: *mut leanh::LeanObject,
    mut v_00_u03b1_1333_: *mut leanh::LeanObject,
    mut v_args_1334_: *mut leanh::LeanObject,
    mut v_self_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1336_ = leanh::lean_apply_1(v_self_1335_, v_args_1334_);
    return v___x_1336_;
}
pub unsafe fn l_Lake_ArgsT_run_x27___redArg___lam__0(
    mut v_x_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1338_ = leanh::lean_ctor_get(v_x_1337_, 0);
    leanh::lean_inc(v_fst_1338_);
    return v_fst_1338_;
}
pub unsafe fn l_Lake_ArgsT_run_x27___redArg___lam__0___boxed(
    mut v_x_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lake_ArgsT_run_x27___redArg___lam__0(v_x_1339_);
    leanh::lean_dec_ref(v_x_1339_);
    return v_res_1340_;
}
pub unsafe fn l_Lake_ArgsT_run_x27___redArg(
    mut v_inst_1342_: *mut leanh::LeanObject,
    mut v_args_1343_: *mut leanh::LeanObject,
    mut v_self_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1345_ = leanh::lean_ctor_get(v_inst_1342_, 0);
    leanh::lean_inc(v_map_1345_);
    leanh::lean_dec_ref(v_inst_1342_);
    v___f_1346_ = l_Lake_ArgsT_run_x27___redArg___closed__0;
    v___x_1347_ = leanh::lean_apply_1(v_self_1344_, v_args_1343_);
    v___x_1348_ = leanh::lean_apply_4(
        v_map_1345_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1346_,
        v___x_1347_,
    );
    return v___x_1348_;
}
pub unsafe fn l_Lake_ArgsT_run_x27(
    mut v_m_1349_: *mut leanh::LeanObject,
    mut v_00_u03b1_1350_: *mut leanh::LeanObject,
    mut v_inst_1351_: *mut leanh::LeanObject,
    mut v_args_1352_: *mut leanh::LeanObject,
    mut v_self_1353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1354_ = leanh::lean_ctor_get(v_inst_1351_, 0);
    leanh::lean_inc(v_map_1354_);
    leanh::lean_dec_ref(v_inst_1351_);
    v___f_1355_ = l_Lake_ArgsT_run_x27___redArg___closed__0;
    v___x_1356_ = leanh::lean_apply_1(v_self_1353_, v_args_1352_);
    v___x_1357_ = leanh::lean_apply_4(
        v_map_1354_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_1355_,
        v___x_1356_,
    );
    return v___x_1357_;
}
pub unsafe fn l_Lake_getArgs___redArg(
    mut v_inst_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_get_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_get_1359_ = leanh::lean_ctor_get(v_inst_1358_, 0);
    leanh::lean_inc(v_get_1359_);
    return v_get_1359_;
}
pub unsafe fn l_Lake_getArgs___redArg___boxed(
    mut v_inst_1360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Lake_getArgs___redArg(v_inst_1360_);
    leanh::lean_dec_ref(v_inst_1360_);
    return v_res_1361_;
}
pub unsafe fn l_Lake_getArgs(
    mut v_m_1362_: *mut leanh::LeanObject,
    mut v_inst_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_get_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_get_1364_ = leanh::lean_ctor_get(v_inst_1363_, 0);
    leanh::lean_inc(v_get_1364_);
    return v_get_1364_;
}
pub unsafe fn l_Lake_getArgs___boxed(
    mut v_m_1365_: *mut leanh::LeanObject,
    mut v_inst_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Lake_getArgs(v_m_1365_, v_inst_1366_);
    leanh::lean_dec_ref(v_inst_1366_);
    return v_res_1367_;
}
pub unsafe fn l_Lake_setArgs___redArg(
    mut v_inst_1368_: *mut leanh::LeanObject,
    mut v_args_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_set_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_set_1370_ = leanh::lean_ctor_get(v_inst_1368_, 1);
    leanh::lean_inc(v_set_1370_);
    leanh::lean_dec_ref(v_inst_1368_);
    v___x_1371_ = leanh::lean_apply_1(v_set_1370_, v_args_1369_);
    return v___x_1371_;
}
pub unsafe fn l_Lake_setArgs(
    mut v_m_1372_: *mut leanh::LeanObject,
    mut v_inst_1373_: *mut leanh::LeanObject,
    mut v_args_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_set_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_set_1375_ = leanh::lean_ctor_get(v_inst_1373_, 1);
    leanh::lean_inc(v_set_1375_);
    leanh::lean_dec_ref(v_inst_1373_);
    v___x_1376_ = leanh::lean_apply_1(v_set_1375_, v_args_1374_);
    return v___x_1376_;
}
pub unsafe fn l_Lake_takeArg_x3f___redArg___lam__0(
    mut v_x_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1384_: u8 = 0;
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1377_) == 0 {
                    v___x_1378_ = leanh::lean_box(0);
                    v___x_1379_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1379_, 0, v___x_1378_);
                    leanh::lean_ctor_set(v___x_1379_, 1, v_x_1377_);
                    return v___x_1379_;
                } else {
                    v_head_1380_ = leanh::lean_ctor_get(v_x_1377_, 0);
                    v_tail_1381_ = leanh::lean_ctor_get(v_x_1377_, 1);
                    v_isSharedCheck_1389_ = (!leanh::lean_is_exclusive(v_x_1377_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1383_ = v_x_1377_;
                        v_isShared_1384_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1381_);
                        leanh::lean_inc(v_head_1380_);
                        leanh::lean_dec(v_x_1377_);
                        v___x_1383_ = leanh::lean_box(0);
                        v_isShared_1384_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1385_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1385_, 0, v_head_1380_);
                if v_isShared_1384_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1383_, 0);
                    leanh::lean_ctor_set(v___x_1383_, 0, v___x_1385_);
                    v___x_1387_ = v___x_1383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_tail_1381_);
                    v___x_1387_ = v_reuseFailAlloc_1388_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1387_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_takeArg_x3f___redArg(
    mut v_inst_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyGet_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_1392_ = leanh::lean_ctor_get(v_inst_1391_, 2);
    leanh::lean_inc(v_modifyGet_1392_);
    leanh::lean_dec_ref(v_inst_1391_);
    v___f_1393_ = l_Lake_takeArg_x3f___redArg___closed__0;
    v___x_1394_ =
        leanh::lean_apply_2(v_modifyGet_1392_, leanh::lean_box(0), v___f_1393_);
    return v___x_1394_;
}
pub unsafe fn l_Lake_takeArg_x3f(
    mut v_m_1395_: *mut leanh::LeanObject,
    mut v_inst_1396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyGet_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_1397_ = leanh::lean_ctor_get(v_inst_1396_, 2);
    leanh::lean_inc(v_modifyGet_1397_);
    leanh::lean_dec_ref(v_inst_1396_);
    v___f_1398_ = l_Lake_takeArg_x3f___redArg___closed__0;
    v___x_1399_ =
        leanh::lean_apply_2(v_modifyGet_1397_, leanh::lean_box(0), v___f_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lake_takeArgD___redArg___lam__0(
    mut v_default_1400_: *mut leanh::LeanObject,
    mut v_x_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1401_) == 0 {
                    v___x_1402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1402_, 0, v_default_1400_);
                    leanh::lean_ctor_set(v___x_1402_, 1, v_x_1401_);
                    return v___x_1402_;
                } else {
                    leanh::lean_dec_ref(v_default_1400_);
                    v_head_1403_ = leanh::lean_ctor_get(v_x_1401_, 0);
                    v_tail_1404_ = leanh::lean_ctor_get(v_x_1401_, 1);
                    v_isSharedCheck_1411_ = (!leanh::lean_is_exclusive(v_x_1401_)) as u8;
                    if v_isSharedCheck_1411_ == 0 {
                        v___x_1406_ = v_x_1401_;
                        v_isShared_1407_ = v_isSharedCheck_1411_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1404_);
                        leanh::lean_inc(v_head_1403_);
                        leanh::lean_dec(v_x_1401_);
                        v___x_1406_ = leanh::lean_box(0);
                        v_isShared_1407_ = v_isSharedCheck_1411_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1407_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1406_, 0);
                    v___x_1409_ = v___x_1406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_head_1403_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_tail_1404_);
                    v___x_1409_ = v_reuseFailAlloc_1410_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1409_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_takeArgD___redArg(
    mut v_inst_1412_: *mut leanh::LeanObject,
    mut v_default_1413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyGet_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_1414_ = leanh::lean_ctor_get(v_inst_1412_, 2);
    leanh::lean_inc(v_modifyGet_1414_);
    leanh::lean_dec_ref(v_inst_1412_);
    v___f_1415_ = leanh::lean_alloc_closure(
        l_Lake_takeArgD___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1415_, 0, v_default_1413_);
    v___x_1416_ =
        leanh::lean_apply_2(v_modifyGet_1414_, leanh::lean_box(0), v___f_1415_);
    return v___x_1416_;
}
pub unsafe fn l_Lake_takeArgD(
    mut v_m_1417_: *mut leanh::LeanObject,
    mut v_inst_1418_: *mut leanh::LeanObject,
    mut v_default_1419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyGet_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_1420_ = leanh::lean_ctor_get(v_inst_1418_, 2);
    leanh::lean_inc(v_modifyGet_1420_);
    leanh::lean_dec_ref(v_inst_1418_);
    v___f_1421_ = leanh::lean_alloc_closure(
        l_Lake_takeArgD___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1421_, 0, v_default_1419_);
    v___x_1422_ =
        leanh::lean_apply_2(v_modifyGet_1420_, leanh::lean_box(0), v___f_1421_);
    return v___x_1422_;
}
pub unsafe fn l_Lake_takeArgs___redArg___lam__0(
    mut v_args_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = leanh::lean_box(0);
    v___x_1425_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1425_, 0, v_args_1423_);
    leanh::lean_ctor_set(v___x_1425_, 1, v___x_1424_);
    return v___x_1425_;
}
pub unsafe fn l_Lake_takeArgs___redArg(
    mut v_inst_1427_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyGet_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_1428_ = leanh::lean_ctor_get(v_inst_1427_, 2);
    leanh::lean_inc(v_modifyGet_1428_);
    leanh::lean_dec_ref(v_inst_1427_);
    v___f_1429_ = l_Lake_takeArgs___redArg___closed__0;
    v___x_1430_ =
        leanh::lean_apply_2(v_modifyGet_1428_, leanh::lean_box(0), v___f_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Lake_takeArgs(
    mut v_m_1431_: *mut leanh::LeanObject,
    mut v_inst_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyGet_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_1433_ = leanh::lean_ctor_get(v_inst_1432_, 2);
    leanh::lean_inc(v_modifyGet_1433_);
    leanh::lean_dec_ref(v_inst_1432_);
    v___f_1434_ = l_Lake_takeArgs___redArg___closed__0;
    v___x_1435_ =
        leanh::lean_apply_2(v_modifyGet_1433_, leanh::lean_box(0), v___f_1434_);
    return v___x_1435_;
}
pub unsafe fn l_Lake_consArg___redArg___lam__0(
    mut v_arg_1436_: *mut leanh::LeanObject,
    mut v_s_1437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = leanh::lean_box(0);
    v___x_1439_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1439_, 0, v_arg_1436_);
    leanh::lean_ctor_set(v___x_1439_, 1, v_s_1437_);
    v___x_1440_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1440_, 0, v___x_1438_);
    leanh::lean_ctor_set(v___x_1440_, 1, v___x_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Lake_consArg___redArg(
    mut v_inst_1441_: *mut leanh::LeanObject,
    mut v_arg_1442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyGet_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_1443_ = leanh::lean_ctor_get(v_inst_1441_, 2);
    leanh::lean_inc(v_modifyGet_1443_);
    leanh::lean_dec_ref(v_inst_1441_);
    v___f_1444_ = leanh::lean_alloc_closure(
        l_Lake_consArg___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1444_, 0, v_arg_1442_);
    v___x_1445_ =
        leanh::lean_apply_2(v_modifyGet_1443_, leanh::lean_box(0), v___f_1444_);
    return v___x_1445_;
}
pub unsafe fn l_Lake_consArg(
    mut v_m_1446_: *mut leanh::LeanObject,
    mut v_inst_1447_: *mut leanh::LeanObject,
    mut v_arg_1448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modifyGet_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modifyGet_1449_ = leanh::lean_ctor_get(v_inst_1447_, 2);
    leanh::lean_inc(v_modifyGet_1449_);
    leanh::lean_dec_ref(v_inst_1447_);
    v___f_1450_ = leanh::lean_alloc_closure(
        l_Lake_consArg___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1450_, 0, v_arg_1448_);
    v___x_1451_ =
        leanh::lean_apply_2(v_modifyGet_1449_, leanh::lean_box(0), v___f_1450_);
    return v___x_1451_;
}
pub unsafe fn l_Lake_shortOptionWithEq___redArg___lam__0(
    mut v_opt_1452_: *mut leanh::LeanObject,
    mut v_handle_1453_: *mut leanh::LeanObject,
    mut v_____r_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: u32 = 0;
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ = leanh::lean_unsigned_to_nat(1);
    v___x_1456_ = lean_string_utf8_get(v_opt_1452_, v___x_1455_);
    v___x_1457_ = leanh::lean_box_uint32(v___x_1456_);
    v___x_1458_ = leanh::lean_apply_1(v_handle_1453_, v___x_1457_);
    return v___x_1458_;
}
pub unsafe fn l_Lake_shortOptionWithEq___redArg___lam__0___boxed(
    mut v_opt_1459_: *mut leanh::LeanObject,
    mut v_handle_1460_: *mut leanh::LeanObject,
    mut v_____r_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1462_ =
        l_Lake_shortOptionWithEq___redArg___lam__0(v_opt_1459_, v_handle_1460_, v_____r_1461_);
    leanh::lean_dec_ref(v_opt_1459_);
    return v_res_1462_;
}
pub unsafe fn l_Lake_shortOptionWithEq___redArg___lam__1(
    mut v___x_1463_: *mut leanh::LeanObject,
    mut v_s_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1465_ = leanh::lean_box(0);
    v___x_1466_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1466_, 0, v___x_1463_);
    leanh::lean_ctor_set(v___x_1466_, 1, v_s_1464_);
    v___x_1467_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1465_);
    leanh::lean_ctor_set(v___x_1467_, 1, v___x_1466_);
    return v___x_1467_;
}
pub unsafe fn l_Lake_shortOptionWithEq___redArg(
    mut v_inst_1468_: *mut leanh::LeanObject,
    mut v_inst_1469_: *mut leanh::LeanObject,
    mut v_handle_1470_: *mut leanh::LeanObject,
    mut v_opt_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_unused_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1472_ = leanh::lean_ctor_get(v_inst_1468_, 1);
                leanh::lean_inc(v_toBind_1472_);
                leanh::lean_dec_ref(v_inst_1468_);
                v___x_1473_ = lean_string_utf8_byte_size(v_opt_1471_);
                v_modifyGet_1474_ = leanh::lean_ctor_get(v_inst_1469_, 2);
                v_isSharedCheck_1489_ = (!leanh::lean_is_exclusive(v_inst_1469_)) as u8;
                if v_isSharedCheck_1489_ == 0 {
                    v_unused_1490_ = leanh::lean_ctor_get(v_inst_1469_, 1);
                    leanh::lean_dec(v_unused_1490_);
                    v_unused_1491_ = leanh::lean_ctor_get(v_inst_1469_, 0);
                    leanh::lean_dec(v_unused_1491_);
                    v___x_1476_ = v_inst_1469_;
                    v_isShared_1477_ = v_isSharedCheck_1489_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyGet_1474_);
                    leanh::lean_dec(v_inst_1469_);
                    v___x_1476_ = leanh::lean_box(0);
                    v_isShared_1477_ = v_isSharedCheck_1489_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1478_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_opt_1471_);
                if v_isShared_1477_ == 0 {
                    leanh::lean_ctor_set(v___x_1476_, 2, v___x_1473_);
                    leanh::lean_ctor_set(v___x_1476_, 1, v___x_1478_);
                    leanh::lean_ctor_set(v___x_1476_, 0, v_opt_1471_);
                    v___x_1480_ = v___x_1476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1488_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_opt_1471_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1478_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1488_, 2, v___x_1473_);
                    v___x_1480_ = v_reuseFailAlloc_1488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_opt_1471_);
                v___f_1481_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1481_, 0, v_opt_1471_);
                leanh::lean_closure_set(v___f_1481_, 1, v_handle_1470_);
                v___x_1482_ = leanh::lean_unsigned_to_nat(3);
                v___x_1483_ = l_String_Slice_Pos_nextn(v___x_1480_, v___x_1478_, v___x_1482_);
                leanh::lean_dec_ref(v___x_1480_);
                v___x_1484_ = lean_string_utf8_extract(v_opt_1471_, v___x_1483_, v___x_1473_);
                leanh::lean_dec(v___x_1483_);
                leanh::lean_dec_ref(v_opt_1471_);
                v___f_1485_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1485_, 0, v___x_1484_);
                v___x_1486_ = leanh::lean_apply_2(
                    v_modifyGet_1474_,
                    leanh::lean_box(0),
                    v___f_1485_,
                );
                v___x_1487_ = leanh::lean_apply_4(
                    v_toBind_1472_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1486_,
                    v___f_1481_,
                );
                return v___x_1487_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_shortOptionWithEq(
    mut v_m_1492_: *mut leanh::LeanObject,
    mut v_inst_1493_: *mut leanh::LeanObject,
    mut v_inst_1494_: *mut leanh::LeanObject,
    mut v_00_u03b1_1495_: *mut leanh::LeanObject,
    mut v_handle_1496_: *mut leanh::LeanObject,
    mut v_opt_1497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1503_: u8 = 0;
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut v_unused_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1498_ = leanh::lean_ctor_get(v_inst_1493_, 1);
                leanh::lean_inc(v_toBind_1498_);
                leanh::lean_dec_ref(v_inst_1493_);
                v___x_1499_ = lean_string_utf8_byte_size(v_opt_1497_);
                v_modifyGet_1500_ = leanh::lean_ctor_get(v_inst_1494_, 2);
                v_isSharedCheck_1515_ = (!leanh::lean_is_exclusive(v_inst_1494_)) as u8;
                if v_isSharedCheck_1515_ == 0 {
                    v_unused_1516_ = leanh::lean_ctor_get(v_inst_1494_, 1);
                    leanh::lean_dec(v_unused_1516_);
                    v_unused_1517_ = leanh::lean_ctor_get(v_inst_1494_, 0);
                    leanh::lean_dec(v_unused_1517_);
                    v___x_1502_ = v_inst_1494_;
                    v_isShared_1503_ = v_isSharedCheck_1515_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyGet_1500_);
                    leanh::lean_dec(v_inst_1494_);
                    v___x_1502_ = leanh::lean_box(0);
                    v_isShared_1503_ = v_isSharedCheck_1515_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1504_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_opt_1497_);
                if v_isShared_1503_ == 0 {
                    leanh::lean_ctor_set(v___x_1502_, 2, v___x_1499_);
                    leanh::lean_ctor_set(v___x_1502_, 1, v___x_1504_);
                    leanh::lean_ctor_set(v___x_1502_, 0, v_opt_1497_);
                    v___x_1506_ = v___x_1502_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_opt_1497_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 2, v___x_1499_);
                    v___x_1506_ = v_reuseFailAlloc_1514_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_opt_1497_);
                v___f_1507_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1507_, 0, v_opt_1497_);
                leanh::lean_closure_set(v___f_1507_, 1, v_handle_1496_);
                v___x_1508_ = leanh::lean_unsigned_to_nat(3);
                v___x_1509_ = l_String_Slice_Pos_nextn(v___x_1506_, v___x_1504_, v___x_1508_);
                leanh::lean_dec_ref(v___x_1506_);
                v___x_1510_ = lean_string_utf8_extract(v_opt_1497_, v___x_1509_, v___x_1499_);
                leanh::lean_dec(v___x_1509_);
                leanh::lean_dec_ref(v_opt_1497_);
                v___f_1511_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1511_, 0, v___x_1510_);
                v___x_1512_ = leanh::lean_apply_2(
                    v_modifyGet_1500_,
                    leanh::lean_box(0),
                    v___f_1511_,
                );
                v___x_1513_ = leanh::lean_apply_4(
                    v_toBind_1498_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1512_,
                    v___f_1507_,
                );
                return v___x_1513_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_shortOptionWithSpace___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1519_ = l_Lake_shortOptionWithSpace___redArg___closed__0;
    v___x_1520_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn l_Lake_shortOptionWithSpace___redArg(
    mut v_inst_1521_: *mut leanh::LeanObject,
    mut v_inst_1522_: *mut leanh::LeanObject,
    mut v_handle_1523_: *mut leanh::LeanObject,
    mut v_opt_1524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_unused_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1525_ = leanh::lean_ctor_get(v_inst_1521_, 1);
                leanh::lean_inc(v_toBind_1525_);
                leanh::lean_dec_ref(v_inst_1521_);
                v___x_1526_ = leanh::lean_unsigned_to_nat(0);
                v___x_1527_ = lean_string_utf8_byte_size(v_opt_1524_);
                leanh::lean_inc_ref(v_opt_1524_);
                v___x_1528_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1528_, 0, v_opt_1524_);
                leanh::lean_ctor_set(v___x_1528_, 1, v___x_1526_);
                leanh::lean_ctor_set(v___x_1528_, 2, v___x_1527_);
                v___x_1529_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_shortOptionWithSpace___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_shortOptionWithSpace___redArg___closed__1_once),
                    _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                );
                v_modifyGet_1530_ = leanh::lean_ctor_get(v_inst_1522_, 2);
                v_isSharedCheck_1546_ = (!leanh::lean_is_exclusive(v_inst_1522_)) as u8;
                if v_isSharedCheck_1546_ == 0 {
                    v_unused_1547_ = leanh::lean_ctor_get(v_inst_1522_, 1);
                    leanh::lean_dec(v_unused_1547_);
                    v_unused_1548_ = leanh::lean_ctor_get(v_inst_1522_, 0);
                    leanh::lean_dec(v_unused_1548_);
                    v___x_1532_ = v_inst_1522_;
                    v_isShared_1533_ = v_isSharedCheck_1546_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyGet_1530_);
                    leanh::lean_dec(v_inst_1522_);
                    v___x_1532_ = leanh::lean_box(0);
                    v_isShared_1533_ = v_isSharedCheck_1546_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1534_ = leanh::lean_unsigned_to_nat(2);
                v___x_1535_ = l_String_Slice_Pos_nextn(v___x_1528_, v___x_1526_, v___x_1534_);
                leanh::lean_dec_ref_known(v___x_1528_, 3);
                leanh::lean_inc_ref_n(v_opt_1524_, 2);
                v___f_1536_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1536_, 0, v_opt_1524_);
                leanh::lean_closure_set(v___f_1536_, 1, v_handle_1523_);
                leanh::lean_inc(v___x_1535_);
                if v_isShared_1533_ == 0 {
                    leanh::lean_ctor_set(v___x_1532_, 2, v___x_1527_);
                    leanh::lean_ctor_set(v___x_1532_, 1, v___x_1535_);
                    leanh::lean_ctor_set(v___x_1532_, 0, v_opt_1524_);
                    v___x_1538_ = v___x_1532_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_opt_1524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___x_1535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 2, v___x_1527_);
                    v___x_1538_ = v_reuseFailAlloc_1545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1539_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_1538_, v___x_1526_, v___x_1529_);
                leanh::lean_dec_ref(v___x_1538_);
                v___x_1540_ = lean_nat_add(v___x_1535_, v___x_1539_);
                leanh::lean_dec(v___x_1539_);
                leanh::lean_dec(v___x_1535_);
                v___x_1541_ = lean_string_utf8_extract(v_opt_1524_, v___x_1540_, v___x_1527_);
                leanh::lean_dec(v___x_1540_);
                leanh::lean_dec_ref(v_opt_1524_);
                v___f_1542_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1542_, 0, v___x_1541_);
                v___x_1543_ = leanh::lean_apply_2(
                    v_modifyGet_1530_,
                    leanh::lean_box(0),
                    v___f_1542_,
                );
                v___x_1544_ = leanh::lean_apply_4(
                    v_toBind_1525_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1543_,
                    v___f_1536_,
                );
                return v___x_1544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_shortOptionWithSpace(
    mut v_m_1549_: *mut leanh::LeanObject,
    mut v_inst_1550_: *mut leanh::LeanObject,
    mut v_inst_1551_: *mut leanh::LeanObject,
    mut v_00_u03b1_1552_: *mut leanh::LeanObject,
    mut v_handle_1553_: *mut leanh::LeanObject,
    mut v_opt_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_unused_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1555_ = leanh::lean_ctor_get(v_inst_1550_, 1);
                leanh::lean_inc(v_toBind_1555_);
                leanh::lean_dec_ref(v_inst_1550_);
                v___x_1556_ = leanh::lean_unsigned_to_nat(0);
                v___x_1557_ = lean_string_utf8_byte_size(v_opt_1554_);
                leanh::lean_inc_ref(v_opt_1554_);
                v___x_1558_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1558_, 0, v_opt_1554_);
                leanh::lean_ctor_set(v___x_1558_, 1, v___x_1556_);
                leanh::lean_ctor_set(v___x_1558_, 2, v___x_1557_);
                v___x_1559_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_shortOptionWithSpace___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_shortOptionWithSpace___redArg___closed__1_once),
                    _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                );
                v_modifyGet_1560_ = leanh::lean_ctor_get(v_inst_1551_, 2);
                v_isSharedCheck_1576_ = (!leanh::lean_is_exclusive(v_inst_1551_)) as u8;
                if v_isSharedCheck_1576_ == 0 {
                    v_unused_1577_ = leanh::lean_ctor_get(v_inst_1551_, 1);
                    leanh::lean_dec(v_unused_1577_);
                    v_unused_1578_ = leanh::lean_ctor_get(v_inst_1551_, 0);
                    leanh::lean_dec(v_unused_1578_);
                    v___x_1562_ = v_inst_1551_;
                    v_isShared_1563_ = v_isSharedCheck_1576_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyGet_1560_);
                    leanh::lean_dec(v_inst_1551_);
                    v___x_1562_ = leanh::lean_box(0);
                    v_isShared_1563_ = v_isSharedCheck_1576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1564_ = leanh::lean_unsigned_to_nat(2);
                v___x_1565_ = l_String_Slice_Pos_nextn(v___x_1558_, v___x_1556_, v___x_1564_);
                leanh::lean_dec_ref_known(v___x_1558_, 3);
                leanh::lean_inc_ref_n(v_opt_1554_, 2);
                v___f_1566_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1566_, 0, v_opt_1554_);
                leanh::lean_closure_set(v___f_1566_, 1, v_handle_1553_);
                leanh::lean_inc(v___x_1565_);
                if v_isShared_1563_ == 0 {
                    leanh::lean_ctor_set(v___x_1562_, 2, v___x_1557_);
                    leanh::lean_ctor_set(v___x_1562_, 1, v___x_1565_);
                    leanh::lean_ctor_set(v___x_1562_, 0, v_opt_1554_);
                    v___x_1568_ = v___x_1562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_opt_1554_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1565_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1575_, 2, v___x_1557_);
                    v___x_1568_ = v_reuseFailAlloc_1575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1569_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_1568_, v___x_1556_, v___x_1559_);
                leanh::lean_dec_ref(v___x_1568_);
                v___x_1570_ = lean_nat_add(v___x_1565_, v___x_1569_);
                leanh::lean_dec(v___x_1569_);
                leanh::lean_dec(v___x_1565_);
                v___x_1571_ = lean_string_utf8_extract(v_opt_1554_, v___x_1570_, v___x_1557_);
                leanh::lean_dec(v___x_1570_);
                leanh::lean_dec_ref(v_opt_1554_);
                v___f_1572_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1572_, 0, v___x_1571_);
                v___x_1573_ = leanh::lean_apply_2(
                    v_modifyGet_1560_,
                    leanh::lean_box(0),
                    v___f_1572_,
                );
                v___x_1574_ = leanh::lean_apply_4(
                    v_toBind_1555_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1573_,
                    v___f_1566_,
                );
                return v___x_1574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_shortOptionWithArg___redArg(
    mut v_inst_1579_: *mut leanh::LeanObject,
    mut v_inst_1580_: *mut leanh::LeanObject,
    mut v_handle_1581_: *mut leanh::LeanObject,
    mut v_opt_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut v_unused_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1583_ = leanh::lean_ctor_get(v_inst_1579_, 1);
                leanh::lean_inc(v_toBind_1583_);
                leanh::lean_dec_ref(v_inst_1579_);
                v___x_1584_ = lean_string_utf8_byte_size(v_opt_1582_);
                v_modifyGet_1585_ = leanh::lean_ctor_get(v_inst_1580_, 2);
                v_isSharedCheck_1600_ = (!leanh::lean_is_exclusive(v_inst_1580_)) as u8;
                if v_isSharedCheck_1600_ == 0 {
                    v_unused_1601_ = leanh::lean_ctor_get(v_inst_1580_, 1);
                    leanh::lean_dec(v_unused_1601_);
                    v_unused_1602_ = leanh::lean_ctor_get(v_inst_1580_, 0);
                    leanh::lean_dec(v_unused_1602_);
                    v___x_1587_ = v_inst_1580_;
                    v_isShared_1588_ = v_isSharedCheck_1600_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyGet_1585_);
                    leanh::lean_dec(v_inst_1580_);
                    v___x_1587_ = leanh::lean_box(0);
                    v_isShared_1588_ = v_isSharedCheck_1600_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1589_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_opt_1582_);
                if v_isShared_1588_ == 0 {
                    leanh::lean_ctor_set(v___x_1587_, 2, v___x_1584_);
                    leanh::lean_ctor_set(v___x_1587_, 1, v___x_1589_);
                    leanh::lean_ctor_set(v___x_1587_, 0, v_opt_1582_);
                    v___x_1591_ = v___x_1587_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1599_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_opt_1582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1589_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1599_, 2, v___x_1584_);
                    v___x_1591_ = v_reuseFailAlloc_1599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_opt_1582_);
                v___f_1592_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1592_, 0, v_opt_1582_);
                leanh::lean_closure_set(v___f_1592_, 1, v_handle_1581_);
                v___x_1593_ = leanh::lean_unsigned_to_nat(2);
                v___x_1594_ = l_String_Slice_Pos_nextn(v___x_1591_, v___x_1589_, v___x_1593_);
                leanh::lean_dec_ref(v___x_1591_);
                v___x_1595_ = lean_string_utf8_extract(v_opt_1582_, v___x_1594_, v___x_1584_);
                leanh::lean_dec(v___x_1594_);
                leanh::lean_dec_ref(v_opt_1582_);
                v___f_1596_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1596_, 0, v___x_1595_);
                v___x_1597_ = leanh::lean_apply_2(
                    v_modifyGet_1585_,
                    leanh::lean_box(0),
                    v___f_1596_,
                );
                v___x_1598_ = leanh::lean_apply_4(
                    v_toBind_1583_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1597_,
                    v___f_1592_,
                );
                return v___x_1598_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_shortOptionWithArg(
    mut v_m_1603_: *mut leanh::LeanObject,
    mut v_inst_1604_: *mut leanh::LeanObject,
    mut v_inst_1605_: *mut leanh::LeanObject,
    mut v_00_u03b1_1606_: *mut leanh::LeanObject,
    mut v_handle_1607_: *mut leanh::LeanObject,
    mut v_opt_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1614_: u8 = 0;
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut v_unused_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1609_ = leanh::lean_ctor_get(v_inst_1604_, 1);
                leanh::lean_inc(v_toBind_1609_);
                leanh::lean_dec_ref(v_inst_1604_);
                v___x_1610_ = lean_string_utf8_byte_size(v_opt_1608_);
                v_modifyGet_1611_ = leanh::lean_ctor_get(v_inst_1605_, 2);
                v_isSharedCheck_1626_ = (!leanh::lean_is_exclusive(v_inst_1605_)) as u8;
                if v_isSharedCheck_1626_ == 0 {
                    v_unused_1627_ = leanh::lean_ctor_get(v_inst_1605_, 1);
                    leanh::lean_dec(v_unused_1627_);
                    v_unused_1628_ = leanh::lean_ctor_get(v_inst_1605_, 0);
                    leanh::lean_dec(v_unused_1628_);
                    v___x_1613_ = v_inst_1605_;
                    v_isShared_1614_ = v_isSharedCheck_1626_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_modifyGet_1611_);
                    leanh::lean_dec(v_inst_1605_);
                    v___x_1613_ = leanh::lean_box(0);
                    v_isShared_1614_ = v_isSharedCheck_1626_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1615_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_opt_1608_);
                if v_isShared_1614_ == 0 {
                    leanh::lean_ctor_set(v___x_1613_, 2, v___x_1610_);
                    leanh::lean_ctor_set(v___x_1613_, 1, v___x_1615_);
                    leanh::lean_ctor_set(v___x_1613_, 0, v_opt_1608_);
                    v___x_1617_ = v___x_1613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1625_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_opt_1608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 1, v___x_1615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1625_, 2, v___x_1610_);
                    v___x_1617_ = v_reuseFailAlloc_1625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_ref(v_opt_1608_);
                v___f_1618_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_1618_, 0, v_opt_1608_);
                leanh::lean_closure_set(v___f_1618_, 1, v_handle_1607_);
                v___x_1619_ = leanh::lean_unsigned_to_nat(2);
                v___x_1620_ = l_String_Slice_Pos_nextn(v___x_1617_, v___x_1615_, v___x_1619_);
                leanh::lean_dec_ref(v___x_1617_);
                v___x_1621_ = lean_string_utf8_extract(v_opt_1608_, v___x_1620_, v___x_1610_);
                leanh::lean_dec(v___x_1620_);
                leanh::lean_dec_ref(v_opt_1608_);
                v___f_1622_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_1622_, 0, v___x_1621_);
                v___x_1623_ = leanh::lean_apply_2(
                    v_modifyGet_1611_,
                    leanh::lean_box(0),
                    v___f_1622_,
                );
                v___x_1624_ = leanh::lean_apply_4(
                    v_toBind_1609_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1623_,
                    v___f_1618_,
                );
                return v___x_1624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed(
    mut v_opt_1629_: *mut leanh::LeanObject,
    mut v_p_1630_: *mut leanh::LeanObject,
    mut v_inst_1631_: *mut leanh::LeanObject,
    mut v_handle_1632_: *mut leanh::LeanObject,
    mut v_____r_1633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1634_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(
        v_opt_1629_,
        v_p_1630_,
        v_inst_1631_,
        v_handle_1632_,
        v_____r_1633_,
    );
    leanh::lean_dec(v_p_1630_);
    return v_res_1634_;
}
pub unsafe fn l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(
    mut v_inst_1635_: *mut leanh::LeanObject,
    mut v_handle_1636_: *mut leanh::LeanObject,
    mut v_opt_1637_: *mut leanh::LeanObject,
    mut v_p_1638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1639_: u8 = 0;
    v___x_1639_ = lean_string_utf8_at_end(v_opt_1637_, v_p_1638_);
    if v___x_1639_ == 0 {
        let mut v_toBind_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: u32 = 0;
        let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_toBind_1640_ = leanh::lean_ctor_get(v_inst_1635_, 1);
        leanh::lean_inc(v_toBind_1640_);
        leanh::lean_inc(v_handle_1636_);
        leanh::lean_inc(v_p_1638_);
        leanh::lean_inc_ref(v_opt_1637_);
        v___f_1641_ = leanh::lean_alloc_closure(
            l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            5,
            4,
        );
        leanh::lean_closure_set(v___f_1641_, 0, v_opt_1637_);
        leanh::lean_closure_set(v___f_1641_, 1, v_p_1638_);
        leanh::lean_closure_set(v___f_1641_, 2, v_inst_1635_);
        leanh::lean_closure_set(v___f_1641_, 3, v_handle_1636_);
        v___x_1642_ = lean_string_utf8_get_fast(v_opt_1637_, v_p_1638_);
        leanh::lean_dec(v_p_1638_);
        leanh::lean_dec_ref(v_opt_1637_);
        v___x_1643_ = leanh::lean_box_uint32(v___x_1642_);
        v___x_1644_ = leanh::lean_apply_1(v_handle_1636_, v___x_1643_);
        v___x_1645_ = leanh::lean_apply_4(
            v_toBind_1640_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_1644_,
            v___f_1641_,
        );
        return v___x_1645_;
    } else {
        let mut v_toApplicative_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_p_1638_);
        leanh::lean_dec_ref(v_opt_1637_);
        leanh::lean_dec(v_handle_1636_);
        v_toApplicative_1646_ = leanh::lean_ctor_get(v_inst_1635_, 0);
        leanh::lean_inc_ref(v_toApplicative_1646_);
        leanh::lean_dec_ref(v_inst_1635_);
        v_toPure_1647_ = leanh::lean_ctor_get(v_toApplicative_1646_, 1);
        leanh::lean_inc(v_toPure_1647_);
        leanh::lean_dec_ref(v_toApplicative_1646_);
        v___x_1648_ = leanh::lean_box(0);
        v___x_1649_ =
            leanh::lean_apply_2(v_toPure_1647_, leanh::lean_box(0), v___x_1648_);
        return v___x_1649_;
    }
}
pub unsafe fn l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(
    mut v_opt_1650_: *mut leanh::LeanObject,
    mut v_p_1651_: *mut leanh::LeanObject,
    mut v_inst_1652_: *mut leanh::LeanObject,
    mut v_handle_1653_: *mut leanh::LeanObject,
    mut v_____r_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1655_ = lean_string_utf8_next_fast(v_opt_1650_, v_p_1651_);
    v___x_1656_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(
        v_inst_1652_,
        v_handle_1653_,
        v_opt_1650_,
        v___x_1655_,
    );
    return v___x_1656_;
}
pub unsafe fn l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop(
    mut v_m_1657_: *mut leanh::LeanObject,
    mut v_inst_1658_: *mut leanh::LeanObject,
    mut v_handle_1659_: *mut leanh::LeanObject,
    mut v_opt_1660_: *mut leanh::LeanObject,
    mut v_p_1661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1662_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(
        v_inst_1658_,
        v_handle_1659_,
        v_opt_1660_,
        v_p_1661_,
    );
    return v___x_1662_;
}
pub unsafe fn l_Lake_multiShortOption___redArg(
    mut v_inst_1663_: *mut leanh::LeanObject,
    mut v_handle_1664_: *mut leanh::LeanObject,
    mut v_opt_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1666_ = leanh::lean_unsigned_to_nat(1);
    v___x_1667_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(
        v_inst_1663_,
        v_handle_1664_,
        v_opt_1665_,
        v___x_1666_,
    );
    return v___x_1667_;
}
pub unsafe fn l_Lake_multiShortOption(
    mut v_m_1668_: *mut leanh::LeanObject,
    mut v_inst_1669_: *mut leanh::LeanObject,
    mut v_handle_1670_: *mut leanh::LeanObject,
    mut v_opt_1671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1672_ = leanh::lean_unsigned_to_nat(1);
    v___x_1673_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(
        v_inst_1669_,
        v_handle_1670_,
        v_opt_1671_,
        v___x_1672_,
    );
    return v___x_1673_;
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg___lam__0(
    mut v_opt_1674_: *mut leanh::LeanObject,
    mut v___y_1675_: *mut leanh::LeanObject,
    mut v_handle_1676_: *mut leanh::LeanObject,
    mut v_____r_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1678_ = leanh::lean_unsigned_to_nat(0);
    v___x_1679_ = lean_string_utf8_extract(v_opt_1674_, v___x_1678_, v___y_1675_);
    v___x_1680_ = leanh::lean_apply_1(v_handle_1676_, v___x_1679_);
    return v___x_1680_;
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg___lam__0___boxed(
    mut v_opt_1681_: *mut leanh::LeanObject,
    mut v___y_1682_: *mut leanh::LeanObject,
    mut v_handle_1683_: *mut leanh::LeanObject,
    mut v_____r_1684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1685_ = l_Lake_longOptionOrSpace___redArg___lam__0(
        v_opt_1681_,
        v___y_1682_,
        v_handle_1683_,
        v_____r_1684_,
    );
    leanh::lean_dec(v___y_1682_);
    leanh::lean_dec_ref(v_opt_1681_);
    return v_res_1685_;
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg___lam__2(
    mut v___x_1686_: *mut leanh::LeanObject,
    mut v_opt_1687_: *mut leanh::LeanObject,
    mut v___x_1688_: *mut leanh::LeanObject,
    mut v_it_1689_: *mut leanh::LeanObject,
    mut v_acc_1690_: *mut leanh::LeanObject,
    mut v_hP_1691_: *mut leanh::LeanObject,
    mut v_recur_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1693_: u8 = 0;
    v___x_1693_ = lean_nat_dec_eq(v_it_1689_, v___x_1686_);
    if v___x_1693_ == 0 {
        let mut v___x_1694_: u32 = 0;
        let mut v___x_1695_: u32 = 0;
        let mut v___x_1696_: u8 = 0;
        v___x_1694_ = lean_string_utf8_get_fast(v_opt_1687_, v_it_1689_);
        v___x_1695_ = 32;
        v___x_1696_ = lean_uint32_dec_eq(v___x_1694_, v___x_1695_);
        if v___x_1696_ == 0 {
            let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1697_ = lean_string_utf8_next_fast(v_opt_1687_, v_it_1689_);
            leanh::lean_dec(v_it_1689_);
            v___x_1698_ = leanh::lean_apply_4(
                v_recur_1692_,
                v___x_1697_,
                v___x_1688_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1698_;
        } else {
            let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_recur_1692_);
            leanh::lean_dec(v___x_1688_);
            v___x_1699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1699_, 0, v_it_1689_);
            return v___x_1699_;
        }
    } else {
        leanh::lean_dec_ref(v_recur_1692_);
        leanh::lean_dec(v_it_1689_);
        leanh::lean_dec(v___x_1688_);
        leanh::lean_inc(v_acc_1690_);
        return v_acc_1690_;
    }
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg___lam__2___boxed(
    mut v___x_1700_: *mut leanh::LeanObject,
    mut v_opt_1701_: *mut leanh::LeanObject,
    mut v___x_1702_: *mut leanh::LeanObject,
    mut v_it_1703_: *mut leanh::LeanObject,
    mut v_acc_1704_: *mut leanh::LeanObject,
    mut v_hP_1705_: *mut leanh::LeanObject,
    mut v_recur_1706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1707_ = l_Lake_longOptionOrSpace___redArg___lam__2(
        v___x_1700_,
        v_opt_1701_,
        v___x_1702_,
        v_it_1703_,
        v_acc_1704_,
        v_hP_1705_,
        v_recur_1706_,
    );
    leanh::lean_dec(v_acc_1704_);
    leanh::lean_dec_ref(v_opt_1701_);
    leanh::lean_dec(v___x_1700_);
    return v_res_1707_;
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg(
    mut v_inst_1708_: *mut leanh::LeanObject,
    mut v_inst_1709_: *mut leanh::LeanObject,
    mut v_handle_1710_: *mut leanh::LeanObject,
    mut v_opt_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v_toBind_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1725_ = leanh::lean_unsigned_to_nat(0);
                v___x_1726_ = lean_string_utf8_byte_size(v_opt_1711_);
                v___x_1727_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_opt_1711_);
                v___f_1728_ = leanh::lean_alloc_closure(
                    l_Lake_longOptionOrSpace___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_1728_, 0, v___x_1726_);
                leanh::lean_closure_set(v___f_1728_, 1, v_opt_1711_);
                leanh::lean_closure_set(v___f_1728_, 2, v___x_1727_);
                v___x_1729_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1728_,
                    v_searcher_1725_,
                    v___x_1727_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1729_) == 0 {
                    v___y_1713_ = v___x_1726_;
                    state = 1;
                    continue;
                } else {
                    v_val_1730_ = leanh::lean_ctor_get(v___x_1729_, 0);
                    leanh::lean_inc(v_val_1730_);
                    leanh::lean_dec_ref_known(v___x_1729_, 1);
                    v___y_1713_ = v_val_1730_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1714_ = lean_string_utf8_byte_size(v_opt_1711_);
                v___x_1715_ = lean_nat_dec_eq(v___y_1713_, v___x_1714_);
                if v___x_1715_ == 0 {
                    v_toBind_1716_ = leanh::lean_ctor_get(v_inst_1708_, 1);
                    leanh::lean_inc(v_toBind_1716_);
                    leanh::lean_dec_ref(v_inst_1708_);
                    v_modifyGet_1717_ = leanh::lean_ctor_get(v_inst_1709_, 2);
                    leanh::lean_inc(v_modifyGet_1717_);
                    leanh::lean_dec_ref(v_inst_1709_);
                    leanh::lean_inc(v___y_1713_);
                    leanh::lean_inc_ref(v_opt_1711_);
                    v___f_1718_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1718_, 0, v_opt_1711_);
                    leanh::lean_closure_set(v___f_1718_, 1, v___y_1713_);
                    leanh::lean_closure_set(v___f_1718_, 2, v_handle_1710_);
                    v___x_1719_ = lean_string_utf8_next_fast(v_opt_1711_, v___y_1713_);
                    leanh::lean_dec(v___y_1713_);
                    v___x_1720_ = lean_string_utf8_extract(v_opt_1711_, v___x_1719_, v___x_1714_);
                    leanh::lean_dec_ref(v_opt_1711_);
                    v___f_1721_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1721_, 0, v___x_1720_);
                    v___x_1722_ = leanh::lean_apply_2(
                        v_modifyGet_1717_,
                        leanh::lean_box(0),
                        v___f_1721_,
                    );
                    v___x_1723_ = leanh::lean_apply_4(
                        v_toBind_1716_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1722_,
                        v___f_1718_,
                    );
                    return v___x_1723_;
                } else {
                    leanh::lean_dec(v___y_1713_);
                    leanh::lean_dec_ref(v_inst_1709_);
                    leanh::lean_dec_ref(v_inst_1708_);
                    v___x_1724_ = leanh::lean_apply_1(v_handle_1710_, v_opt_1711_);
                    return v___x_1724_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOptionOrSpace(
    mut v_m_1731_: *mut leanh::LeanObject,
    mut v_inst_1732_: *mut leanh::LeanObject,
    mut v_inst_1733_: *mut leanh::LeanObject,
    mut v_00_u03b1_1734_: *mut leanh::LeanObject,
    mut v_handle_1735_: *mut leanh::LeanObject,
    mut v_opt_1736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v_toBind_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1750_ = leanh::lean_unsigned_to_nat(0);
                v___x_1751_ = lean_string_utf8_byte_size(v_opt_1736_);
                v___x_1752_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_opt_1736_);
                v___f_1753_ = leanh::lean_alloc_closure(
                    l_Lake_longOptionOrSpace___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_1753_, 0, v___x_1751_);
                leanh::lean_closure_set(v___f_1753_, 1, v_opt_1736_);
                leanh::lean_closure_set(v___f_1753_, 2, v___x_1752_);
                v___x_1754_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1753_,
                    v_searcher_1750_,
                    v___x_1752_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1754_) == 0 {
                    v___y_1738_ = v___x_1751_;
                    state = 1;
                    continue;
                } else {
                    v_val_1755_ = leanh::lean_ctor_get(v___x_1754_, 0);
                    leanh::lean_inc(v_val_1755_);
                    leanh::lean_dec_ref_known(v___x_1754_, 1);
                    v___y_1738_ = v_val_1755_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1739_ = lean_string_utf8_byte_size(v_opt_1736_);
                v___x_1740_ = lean_nat_dec_eq(v___y_1738_, v___x_1739_);
                if v___x_1740_ == 0 {
                    v_toBind_1741_ = leanh::lean_ctor_get(v_inst_1732_, 1);
                    leanh::lean_inc(v_toBind_1741_);
                    leanh::lean_dec_ref(v_inst_1732_);
                    v_modifyGet_1742_ = leanh::lean_ctor_get(v_inst_1733_, 2);
                    leanh::lean_inc(v_modifyGet_1742_);
                    leanh::lean_dec_ref(v_inst_1733_);
                    leanh::lean_inc(v___y_1738_);
                    leanh::lean_inc_ref(v_opt_1736_);
                    v___f_1743_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1743_, 0, v_opt_1736_);
                    leanh::lean_closure_set(v___f_1743_, 1, v___y_1738_);
                    leanh::lean_closure_set(v___f_1743_, 2, v_handle_1735_);
                    v___x_1744_ = lean_string_utf8_next_fast(v_opt_1736_, v___y_1738_);
                    leanh::lean_dec(v___y_1738_);
                    v___x_1745_ = lean_string_utf8_extract(v_opt_1736_, v___x_1744_, v___x_1739_);
                    leanh::lean_dec_ref(v_opt_1736_);
                    v___f_1746_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1746_, 0, v___x_1745_);
                    v___x_1747_ = leanh::lean_apply_2(
                        v_modifyGet_1742_,
                        leanh::lean_box(0),
                        v___f_1746_,
                    );
                    v___x_1748_ = leanh::lean_apply_4(
                        v_toBind_1741_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1747_,
                        v___f_1743_,
                    );
                    return v___x_1748_;
                } else {
                    leanh::lean_dec(v___y_1738_);
                    leanh::lean_dec_ref(v_inst_1733_);
                    leanh::lean_dec_ref(v_inst_1732_);
                    v___x_1749_ = leanh::lean_apply_1(v_handle_1735_, v_opt_1736_);
                    return v___x_1749_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOptionOrEq___redArg___lam__2(
    mut v___x_1756_: *mut leanh::LeanObject,
    mut v_opt_1757_: *mut leanh::LeanObject,
    mut v___x_1758_: *mut leanh::LeanObject,
    mut v_it_1759_: *mut leanh::LeanObject,
    mut v_acc_1760_: *mut leanh::LeanObject,
    mut v_hP_1761_: *mut leanh::LeanObject,
    mut v_recur_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1763_: u8 = 0;
    v___x_1763_ = lean_nat_dec_eq(v_it_1759_, v___x_1756_);
    if v___x_1763_ == 0 {
        let mut v___x_1764_: u32 = 0;
        let mut v___x_1765_: u32 = 0;
        let mut v___x_1766_: u8 = 0;
        v___x_1764_ = lean_string_utf8_get_fast(v_opt_1757_, v_it_1759_);
        v___x_1765_ = 61;
        v___x_1766_ = lean_uint32_dec_eq(v___x_1764_, v___x_1765_);
        if v___x_1766_ == 0 {
            let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1767_ = lean_string_utf8_next_fast(v_opt_1757_, v_it_1759_);
            leanh::lean_dec(v_it_1759_);
            v___x_1768_ = leanh::lean_apply_4(
                v_recur_1762_,
                v___x_1767_,
                v___x_1758_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1768_;
        } else {
            let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_recur_1762_);
            leanh::lean_dec(v___x_1758_);
            v___x_1769_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1769_, 0, v_it_1759_);
            return v___x_1769_;
        }
    } else {
        leanh::lean_dec_ref(v_recur_1762_);
        leanh::lean_dec(v_it_1759_);
        leanh::lean_dec(v___x_1758_);
        leanh::lean_inc(v_acc_1760_);
        return v_acc_1760_;
    }
}
pub unsafe fn l_Lake_longOptionOrEq___redArg___lam__2___boxed(
    mut v___x_1770_: *mut leanh::LeanObject,
    mut v_opt_1771_: *mut leanh::LeanObject,
    mut v___x_1772_: *mut leanh::LeanObject,
    mut v_it_1773_: *mut leanh::LeanObject,
    mut v_acc_1774_: *mut leanh::LeanObject,
    mut v_hP_1775_: *mut leanh::LeanObject,
    mut v_recur_1776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Lake_longOptionOrEq___redArg___lam__2(
        v___x_1770_,
        v_opt_1771_,
        v___x_1772_,
        v_it_1773_,
        v_acc_1774_,
        v_hP_1775_,
        v_recur_1776_,
    );
    leanh::lean_dec(v_acc_1774_);
    leanh::lean_dec_ref(v_opt_1771_);
    leanh::lean_dec(v___x_1770_);
    return v_res_1777_;
}
pub unsafe fn l_Lake_longOptionOrEq___redArg(
    mut v_inst_1778_: *mut leanh::LeanObject,
    mut v_inst_1779_: *mut leanh::LeanObject,
    mut v_handle_1780_: *mut leanh::LeanObject,
    mut v_opt_1781_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v_toBind_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1795_ = leanh::lean_unsigned_to_nat(0);
                v___x_1796_ = lean_string_utf8_byte_size(v_opt_1781_);
                v___x_1797_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_opt_1781_);
                v___f_1798_ = leanh::lean_alloc_closure(
                    l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_1798_, 0, v___x_1796_);
                leanh::lean_closure_set(v___f_1798_, 1, v_opt_1781_);
                leanh::lean_closure_set(v___f_1798_, 2, v___x_1797_);
                v___x_1799_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1798_,
                    v_searcher_1795_,
                    v___x_1797_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1799_) == 0 {
                    v___y_1783_ = v___x_1796_;
                    state = 1;
                    continue;
                } else {
                    v_val_1800_ = leanh::lean_ctor_get(v___x_1799_, 0);
                    leanh::lean_inc(v_val_1800_);
                    leanh::lean_dec_ref_known(v___x_1799_, 1);
                    v___y_1783_ = v_val_1800_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1784_ = lean_string_utf8_byte_size(v_opt_1781_);
                v___x_1785_ = lean_nat_dec_eq(v___y_1783_, v___x_1784_);
                if v___x_1785_ == 0 {
                    v_toBind_1786_ = leanh::lean_ctor_get(v_inst_1778_, 1);
                    leanh::lean_inc(v_toBind_1786_);
                    leanh::lean_dec_ref(v_inst_1778_);
                    v_modifyGet_1787_ = leanh::lean_ctor_get(v_inst_1779_, 2);
                    leanh::lean_inc(v_modifyGet_1787_);
                    leanh::lean_dec_ref(v_inst_1779_);
                    leanh::lean_inc(v___y_1783_);
                    leanh::lean_inc_ref(v_opt_1781_);
                    v___f_1788_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1788_, 0, v_opt_1781_);
                    leanh::lean_closure_set(v___f_1788_, 1, v___y_1783_);
                    leanh::lean_closure_set(v___f_1788_, 2, v_handle_1780_);
                    v___x_1789_ = lean_string_utf8_next_fast(v_opt_1781_, v___y_1783_);
                    leanh::lean_dec(v___y_1783_);
                    v___x_1790_ = lean_string_utf8_extract(v_opt_1781_, v___x_1789_, v___x_1784_);
                    leanh::lean_dec_ref(v_opt_1781_);
                    v___f_1791_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1791_, 0, v___x_1790_);
                    v___x_1792_ = leanh::lean_apply_2(
                        v_modifyGet_1787_,
                        leanh::lean_box(0),
                        v___f_1791_,
                    );
                    v___x_1793_ = leanh::lean_apply_4(
                        v_toBind_1786_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1792_,
                        v___f_1788_,
                    );
                    return v___x_1793_;
                } else {
                    leanh::lean_dec(v___y_1783_);
                    leanh::lean_dec_ref(v_inst_1779_);
                    leanh::lean_dec_ref(v_inst_1778_);
                    v___x_1794_ = leanh::lean_apply_1(v_handle_1780_, v_opt_1781_);
                    return v___x_1794_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOptionOrEq(
    mut v_m_1801_: *mut leanh::LeanObject,
    mut v_inst_1802_: *mut leanh::LeanObject,
    mut v_inst_1803_: *mut leanh::LeanObject,
    mut v_00_u03b1_1804_: *mut leanh::LeanObject,
    mut v_handle_1805_: *mut leanh::LeanObject,
    mut v_opt_1806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: u8 = 0;
    let mut v_toBind_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1820_ = leanh::lean_unsigned_to_nat(0);
                v___x_1821_ = lean_string_utf8_byte_size(v_opt_1806_);
                v___x_1822_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_opt_1806_);
                v___f_1823_ = leanh::lean_alloc_closure(
                    l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_1823_, 0, v___x_1821_);
                leanh::lean_closure_set(v___f_1823_, 1, v_opt_1806_);
                leanh::lean_closure_set(v___f_1823_, 2, v___x_1822_);
                v___x_1824_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1823_,
                    v_searcher_1820_,
                    v___x_1822_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1824_) == 0 {
                    v___y_1808_ = v___x_1821_;
                    state = 1;
                    continue;
                } else {
                    v_val_1825_ = leanh::lean_ctor_get(v___x_1824_, 0);
                    leanh::lean_inc(v_val_1825_);
                    leanh::lean_dec_ref_known(v___x_1824_, 1);
                    v___y_1808_ = v_val_1825_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1809_ = lean_string_utf8_byte_size(v_opt_1806_);
                v___x_1810_ = lean_nat_dec_eq(v___y_1808_, v___x_1809_);
                if v___x_1810_ == 0 {
                    v_toBind_1811_ = leanh::lean_ctor_get(v_inst_1802_, 1);
                    leanh::lean_inc(v_toBind_1811_);
                    leanh::lean_dec_ref(v_inst_1802_);
                    v_modifyGet_1812_ = leanh::lean_ctor_get(v_inst_1803_, 2);
                    leanh::lean_inc(v_modifyGet_1812_);
                    leanh::lean_dec_ref(v_inst_1803_);
                    leanh::lean_inc(v___y_1808_);
                    leanh::lean_inc_ref(v_opt_1806_);
                    v___f_1813_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1813_, 0, v_opt_1806_);
                    leanh::lean_closure_set(v___f_1813_, 1, v___y_1808_);
                    leanh::lean_closure_set(v___f_1813_, 2, v_handle_1805_);
                    v___x_1814_ = lean_string_utf8_next_fast(v_opt_1806_, v___y_1808_);
                    leanh::lean_dec(v___y_1808_);
                    v___x_1815_ = lean_string_utf8_extract(v_opt_1806_, v___x_1814_, v___x_1809_);
                    leanh::lean_dec_ref(v_opt_1806_);
                    v___f_1816_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1816_, 0, v___x_1815_);
                    v___x_1817_ = leanh::lean_apply_2(
                        v_modifyGet_1812_,
                        leanh::lean_box(0),
                        v___f_1816_,
                    );
                    v___x_1818_ = leanh::lean_apply_4(
                        v_toBind_1811_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1817_,
                        v___f_1813_,
                    );
                    return v___x_1818_;
                } else {
                    leanh::lean_dec(v___y_1808_);
                    leanh::lean_dec_ref(v_inst_1803_);
                    leanh::lean_dec_ref(v_inst_1802_);
                    v___x_1819_ = leanh::lean_apply_1(v_handle_1805_, v_opt_1806_);
                    return v___x_1819_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOption___redArg___lam__2(
    mut v___x_1826_: *mut leanh::LeanObject,
    mut v_searcher_1827_: *mut leanh::LeanObject,
    mut v___y_1828_: *mut leanh::LeanObject,
    mut v_handle_1829_: *mut leanh::LeanObject,
    mut v_____r_1830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1831_ = lean_string_utf8_extract(v___x_1826_, v_searcher_1827_, v___y_1828_);
    v___x_1832_ = leanh::lean_apply_1(v_handle_1829_, v___x_1831_);
    return v___x_1832_;
}
pub unsafe fn l_Lake_longOption___redArg___lam__2___boxed(
    mut v___x_1833_: *mut leanh::LeanObject,
    mut v_searcher_1834_: *mut leanh::LeanObject,
    mut v___y_1835_: *mut leanh::LeanObject,
    mut v_handle_1836_: *mut leanh::LeanObject,
    mut v_____r_1837_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Lake_longOption___redArg___lam__2(
        v___x_1833_,
        v_searcher_1834_,
        v___y_1835_,
        v_handle_1836_,
        v_____r_1837_,
    );
    leanh::lean_dec(v___y_1835_);
    leanh::lean_dec(v_searcher_1834_);
    leanh::lean_dec_ref(v___x_1833_);
    return v_res_1838_;
}
pub unsafe fn l_Lake_longOption___redArg___lam__1(
    mut v___x_1839_: *mut leanh::LeanObject,
    mut v___x_1840_: *mut leanh::LeanObject,
    mut v___x_1841_: *mut leanh::LeanObject,
    mut v_it_1842_: *mut leanh::LeanObject,
    mut v_acc_1843_: *mut leanh::LeanObject,
    mut v_hP_1844_: *mut leanh::LeanObject,
    mut v_recur_1845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1846_: u8 = 0;
    v___x_1846_ = lean_nat_dec_eq(v_it_1842_, v___x_1839_);
    if v___x_1846_ == 0 {
        let mut v___x_1847_: u32 = 0;
        let mut v___x_1848_: u32 = 0;
        let mut v___x_1849_: u8 = 0;
        v___x_1847_ = lean_string_utf8_get_fast(v___x_1840_, v_it_1842_);
        v___x_1848_ = 32;
        v___x_1849_ = lean_uint32_dec_eq(v___x_1847_, v___x_1848_);
        if v___x_1849_ == 0 {
            let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1850_ = lean_string_utf8_next_fast(v___x_1840_, v_it_1842_);
            leanh::lean_dec(v_it_1842_);
            v___x_1851_ = leanh::lean_apply_4(
                v_recur_1845_,
                v___x_1850_,
                v___x_1841_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1851_;
        } else {
            let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_recur_1845_);
            leanh::lean_dec(v___x_1841_);
            v___x_1852_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1852_, 0, v_it_1842_);
            return v___x_1852_;
        }
    } else {
        leanh::lean_dec_ref(v_recur_1845_);
        leanh::lean_dec(v_it_1842_);
        leanh::lean_dec(v___x_1841_);
        leanh::lean_inc(v_acc_1843_);
        return v_acc_1843_;
    }
}
pub unsafe fn l_Lake_longOption___redArg___lam__1___boxed(
    mut v___x_1853_: *mut leanh::LeanObject,
    mut v___x_1854_: *mut leanh::LeanObject,
    mut v___x_1855_: *mut leanh::LeanObject,
    mut v_it_1856_: *mut leanh::LeanObject,
    mut v_acc_1857_: *mut leanh::LeanObject,
    mut v_hP_1858_: *mut leanh::LeanObject,
    mut v_recur_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1860_ = l_Lake_longOption___redArg___lam__1(
        v___x_1853_,
        v___x_1854_,
        v___x_1855_,
        v_it_1856_,
        v_acc_1857_,
        v_hP_1858_,
        v_recur_1859_,
    );
    leanh::lean_dec(v_acc_1857_);
    leanh::lean_dec_ref(v___x_1854_);
    leanh::lean_dec(v___x_1853_);
    return v_res_1860_;
}
pub unsafe fn l_Lake_longOption___redArg___lam__0(
    mut v_opt_1861_: *mut leanh::LeanObject,
    mut v___y_1862_: *mut leanh::LeanObject,
    mut v_handle_1863_: *mut leanh::LeanObject,
    mut v_modifyGet_1864_: *mut leanh::LeanObject,
    mut v_toBind_1865_: *mut leanh::LeanObject,
    mut v_____r_1866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_searcher_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: u8 = 0;
    let mut v___f_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1867_ = leanh::lean_unsigned_to_nat(0);
                v___x_1868_ = lean_string_utf8_extract(v_opt_1861_, v_searcher_1867_, v___y_1862_);
                v___x_1880_ = lean_string_utf8_byte_size(v___x_1868_);
                v___x_1881_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___x_1868_);
                v___f_1882_ = leanh::lean_alloc_closure(
                    l_Lake_longOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_1882_, 0, v___x_1880_);
                leanh::lean_closure_set(v___f_1882_, 1, v___x_1868_);
                leanh::lean_closure_set(v___f_1882_, 2, v___x_1881_);
                v___x_1883_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1882_,
                    v_searcher_1867_,
                    v___x_1881_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1883_) == 0 {
                    v___y_1870_ = v___x_1880_;
                    state = 1;
                    continue;
                } else {
                    v_val_1884_ = leanh::lean_ctor_get(v___x_1883_, 0);
                    leanh::lean_inc(v_val_1884_);
                    leanh::lean_dec_ref_known(v___x_1883_, 1);
                    v___y_1870_ = v_val_1884_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1871_ = lean_string_utf8_byte_size(v___x_1868_);
                v___x_1872_ = lean_nat_dec_eq(v___y_1870_, v___x_1871_);
                if v___x_1872_ == 0 {
                    leanh::lean_inc(v___y_1870_);
                    leanh::lean_inc_ref(v___x_1868_);
                    v___f_1873_ = leanh::lean_alloc_closure(
                        l_Lake_longOption___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    leanh::lean_closure_set(v___f_1873_, 0, v___x_1868_);
                    leanh::lean_closure_set(v___f_1873_, 1, v_searcher_1867_);
                    leanh::lean_closure_set(v___f_1873_, 2, v___y_1870_);
                    leanh::lean_closure_set(v___f_1873_, 3, v_handle_1863_);
                    v___x_1874_ = lean_string_utf8_next_fast(v___x_1868_, v___y_1870_);
                    leanh::lean_dec(v___y_1870_);
                    v___x_1875_ = lean_string_utf8_extract(v___x_1868_, v___x_1874_, v___x_1871_);
                    leanh::lean_dec_ref(v___x_1868_);
                    v___f_1876_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1876_, 0, v___x_1875_);
                    v___x_1877_ = leanh::lean_apply_2(
                        v_modifyGet_1864_,
                        leanh::lean_box(0),
                        v___f_1876_,
                    );
                    v___x_1878_ = leanh::lean_apply_4(
                        v_toBind_1865_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1877_,
                        v___f_1873_,
                    );
                    return v___x_1878_;
                } else {
                    leanh::lean_dec(v___y_1870_);
                    leanh::lean_dec(v_toBind_1865_);
                    leanh::lean_dec(v_modifyGet_1864_);
                    v___x_1879_ = leanh::lean_apply_1(v_handle_1863_, v___x_1868_);
                    return v___x_1879_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOption___redArg___lam__0___boxed(
    mut v_opt_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v_handle_1887_: *mut leanh::LeanObject,
    mut v_modifyGet_1888_: *mut leanh::LeanObject,
    mut v_toBind_1889_: *mut leanh::LeanObject,
    mut v_____r_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1891_ = l_Lake_longOption___redArg___lam__0(
        v_opt_1885_,
        v___y_1886_,
        v_handle_1887_,
        v_modifyGet_1888_,
        v_toBind_1889_,
        v_____r_1890_,
    );
    leanh::lean_dec(v___y_1886_);
    leanh::lean_dec_ref(v_opt_1885_);
    return v_res_1891_;
}
pub unsafe fn l_Lake_longOption___redArg(
    mut v_inst_1892_: *mut leanh::LeanObject,
    mut v_inst_1893_: *mut leanh::LeanObject,
    mut v_handle_1894_: *mut leanh::LeanObject,
    mut v_opt_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: u8 = 0;
    let mut v_toBind_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    let mut v_toBind_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1926_ = leanh::lean_unsigned_to_nat(0);
                v___x_1927_ = lean_string_utf8_byte_size(v_opt_1895_);
                v___x_1928_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_opt_1895_);
                v___f_1929_ = leanh::lean_alloc_closure(
                    l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_1929_, 0, v___x_1927_);
                leanh::lean_closure_set(v___f_1929_, 1, v_opt_1895_);
                leanh::lean_closure_set(v___f_1929_, 2, v___x_1928_);
                v___x_1930_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1929_,
                    v_searcher_1926_,
                    v___x_1928_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1930_) == 0 {
                    v___y_1910_ = v___x_1927_;
                    state = 2;
                    continue;
                } else {
                    v_val_1931_ = leanh::lean_ctor_get(v___x_1930_, 0);
                    leanh::lean_inc(v_val_1931_);
                    leanh::lean_dec_ref_known(v___x_1930_, 1);
                    v___y_1910_ = v_val_1931_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1898_ = lean_string_utf8_byte_size(v_opt_1895_);
                v___x_1899_ = lean_nat_dec_eq(v___y_1897_, v___x_1898_);
                if v___x_1899_ == 0 {
                    v_toBind_1900_ = leanh::lean_ctor_get(v_inst_1892_, 1);
                    leanh::lean_inc(v_toBind_1900_);
                    leanh::lean_dec_ref(v_inst_1892_);
                    v_modifyGet_1901_ = leanh::lean_ctor_get(v_inst_1893_, 2);
                    leanh::lean_inc(v_modifyGet_1901_);
                    leanh::lean_dec_ref(v_inst_1893_);
                    leanh::lean_inc(v___y_1897_);
                    leanh::lean_inc_ref(v_opt_1895_);
                    v___f_1902_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1902_, 0, v_opt_1895_);
                    leanh::lean_closure_set(v___f_1902_, 1, v___y_1897_);
                    leanh::lean_closure_set(v___f_1902_, 2, v_handle_1894_);
                    v___x_1903_ = lean_string_utf8_next_fast(v_opt_1895_, v___y_1897_);
                    leanh::lean_dec(v___y_1897_);
                    v___x_1904_ = lean_string_utf8_extract(v_opt_1895_, v___x_1903_, v___x_1898_);
                    leanh::lean_dec_ref(v_opt_1895_);
                    v___f_1905_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1905_, 0, v___x_1904_);
                    v___x_1906_ = leanh::lean_apply_2(
                        v_modifyGet_1901_,
                        leanh::lean_box(0),
                        v___f_1905_,
                    );
                    v___x_1907_ = leanh::lean_apply_4(
                        v_toBind_1900_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1906_,
                        v___f_1902_,
                    );
                    return v___x_1907_;
                } else {
                    leanh::lean_dec(v___y_1897_);
                    leanh::lean_dec_ref(v_inst_1893_);
                    leanh::lean_dec_ref(v_inst_1892_);
                    v___x_1908_ = leanh::lean_apply_1(v_handle_1894_, v_opt_1895_);
                    return v___x_1908_;
                }
            }
            2 => {
                v___x_1911_ = lean_string_utf8_byte_size(v_opt_1895_);
                v___x_1912_ = lean_nat_dec_eq(v___y_1910_, v___x_1911_);
                if v___x_1912_ == 0 {
                    v_toBind_1913_ = leanh::lean_ctor_get(v_inst_1892_, 1);
                    leanh::lean_inc_n(v_toBind_1913_, 2);
                    leanh::lean_dec_ref(v_inst_1892_);
                    v_modifyGet_1914_ = leanh::lean_ctor_get(v_inst_1893_, 2);
                    leanh::lean_inc_n(v_modifyGet_1914_, 2);
                    leanh::lean_dec_ref(v_inst_1893_);
                    leanh::lean_inc(v___y_1910_);
                    leanh::lean_inc_ref(v_opt_1895_);
                    v___f_1915_ = leanh::lean_alloc_closure(
                        l_Lake_longOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    leanh::lean_closure_set(v___f_1915_, 0, v_opt_1895_);
                    leanh::lean_closure_set(v___f_1915_, 1, v___y_1910_);
                    leanh::lean_closure_set(v___f_1915_, 2, v_handle_1894_);
                    leanh::lean_closure_set(v___f_1915_, 3, v_modifyGet_1914_);
                    leanh::lean_closure_set(v___f_1915_, 4, v_toBind_1913_);
                    v___x_1916_ = lean_string_utf8_next_fast(v_opt_1895_, v___y_1910_);
                    leanh::lean_dec(v___y_1910_);
                    v___x_1917_ = lean_string_utf8_extract(v_opt_1895_, v___x_1916_, v___x_1911_);
                    leanh::lean_dec_ref(v_opt_1895_);
                    v___f_1918_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1918_, 0, v___x_1917_);
                    v___x_1919_ = leanh::lean_apply_2(
                        v_modifyGet_1914_,
                        leanh::lean_box(0),
                        v___f_1918_,
                    );
                    v___x_1920_ = leanh::lean_apply_4(
                        v_toBind_1913_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1919_,
                        v___f_1915_,
                    );
                    return v___x_1920_;
                } else {
                    leanh::lean_dec(v___y_1910_);
                    v_searcher_1921_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1922_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_opt_1895_);
                    v___f_1923_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1923_, 0, v___x_1911_);
                    leanh::lean_closure_set(v___f_1923_, 1, v_opt_1895_);
                    leanh::lean_closure_set(v___f_1923_, 2, v___x_1922_);
                    v___x_1924_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_1923_,
                        v_searcher_1921_,
                        v___x_1922_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1924_) == 0 {
                        v___y_1897_ = v___x_1911_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1925_ = leanh::lean_ctor_get(v___x_1924_, 0);
                        leanh::lean_inc(v_val_1925_);
                        leanh::lean_dec_ref_known(v___x_1924_, 1);
                        v___y_1897_ = v_val_1925_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOption(
    mut v_m_1932_: *mut leanh::LeanObject,
    mut v_inst_1933_: *mut leanh::LeanObject,
    mut v_inst_1934_: *mut leanh::LeanObject,
    mut v_00_u03b1_1935_: *mut leanh::LeanObject,
    mut v_handle_1936_: *mut leanh::LeanObject,
    mut v_opt_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v_toBind_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut v_toBind_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1968_ = leanh::lean_unsigned_to_nat(0);
                v___x_1969_ = lean_string_utf8_byte_size(v_opt_1937_);
                v___x_1970_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_opt_1937_);
                v___f_1971_ = leanh::lean_alloc_closure(
                    l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_1971_, 0, v___x_1969_);
                leanh::lean_closure_set(v___f_1971_, 1, v_opt_1937_);
                leanh::lean_closure_set(v___f_1971_, 2, v___x_1970_);
                v___x_1972_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1971_,
                    v_searcher_1968_,
                    v___x_1970_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1972_) == 0 {
                    v___y_1952_ = v___x_1969_;
                    state = 2;
                    continue;
                } else {
                    v_val_1973_ = leanh::lean_ctor_get(v___x_1972_, 0);
                    leanh::lean_inc(v_val_1973_);
                    leanh::lean_dec_ref_known(v___x_1972_, 1);
                    v___y_1952_ = v_val_1973_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1940_ = lean_string_utf8_byte_size(v_opt_1937_);
                v___x_1941_ = lean_nat_dec_eq(v___y_1939_, v___x_1940_);
                if v___x_1941_ == 0 {
                    v_toBind_1942_ = leanh::lean_ctor_get(v_inst_1933_, 1);
                    leanh::lean_inc(v_toBind_1942_);
                    leanh::lean_dec_ref(v_inst_1933_);
                    v_modifyGet_1943_ = leanh::lean_ctor_get(v_inst_1934_, 2);
                    leanh::lean_inc(v_modifyGet_1943_);
                    leanh::lean_dec_ref(v_inst_1934_);
                    leanh::lean_inc(v___y_1939_);
                    leanh::lean_inc_ref(v_opt_1937_);
                    v___f_1944_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1944_, 0, v_opt_1937_);
                    leanh::lean_closure_set(v___f_1944_, 1, v___y_1939_);
                    leanh::lean_closure_set(v___f_1944_, 2, v_handle_1936_);
                    v___x_1945_ = lean_string_utf8_next_fast(v_opt_1937_, v___y_1939_);
                    leanh::lean_dec(v___y_1939_);
                    v___x_1946_ = lean_string_utf8_extract(v_opt_1937_, v___x_1945_, v___x_1940_);
                    leanh::lean_dec_ref(v_opt_1937_);
                    v___f_1947_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1947_, 0, v___x_1946_);
                    v___x_1948_ = leanh::lean_apply_2(
                        v_modifyGet_1943_,
                        leanh::lean_box(0),
                        v___f_1947_,
                    );
                    v___x_1949_ = leanh::lean_apply_4(
                        v_toBind_1942_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1948_,
                        v___f_1944_,
                    );
                    return v___x_1949_;
                } else {
                    leanh::lean_dec(v___y_1939_);
                    leanh::lean_dec_ref(v_inst_1934_);
                    leanh::lean_dec_ref(v_inst_1933_);
                    v___x_1950_ = leanh::lean_apply_1(v_handle_1936_, v_opt_1937_);
                    return v___x_1950_;
                }
            }
            2 => {
                v___x_1953_ = lean_string_utf8_byte_size(v_opt_1937_);
                v___x_1954_ = lean_nat_dec_eq(v___y_1952_, v___x_1953_);
                if v___x_1954_ == 0 {
                    v_toBind_1955_ = leanh::lean_ctor_get(v_inst_1933_, 1);
                    leanh::lean_inc_n(v_toBind_1955_, 2);
                    leanh::lean_dec_ref(v_inst_1933_);
                    v_modifyGet_1956_ = leanh::lean_ctor_get(v_inst_1934_, 2);
                    leanh::lean_inc_n(v_modifyGet_1956_, 2);
                    leanh::lean_dec_ref(v_inst_1934_);
                    leanh::lean_inc(v___y_1952_);
                    leanh::lean_inc_ref(v_opt_1937_);
                    v___f_1957_ = leanh::lean_alloc_closure(
                        l_Lake_longOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    leanh::lean_closure_set(v___f_1957_, 0, v_opt_1937_);
                    leanh::lean_closure_set(v___f_1957_, 1, v___y_1952_);
                    leanh::lean_closure_set(v___f_1957_, 2, v_handle_1936_);
                    leanh::lean_closure_set(v___f_1957_, 3, v_modifyGet_1956_);
                    leanh::lean_closure_set(v___f_1957_, 4, v_toBind_1955_);
                    v___x_1958_ = lean_string_utf8_next_fast(v_opt_1937_, v___y_1952_);
                    leanh::lean_dec(v___y_1952_);
                    v___x_1959_ = lean_string_utf8_extract(v_opt_1937_, v___x_1958_, v___x_1953_);
                    leanh::lean_dec_ref(v_opt_1937_);
                    v___f_1960_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_1960_, 0, v___x_1959_);
                    v___x_1961_ = leanh::lean_apply_2(
                        v_modifyGet_1956_,
                        leanh::lean_box(0),
                        v___f_1960_,
                    );
                    v___x_1962_ = leanh::lean_apply_4(
                        v_toBind_1955_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_1961_,
                        v___f_1957_,
                    );
                    return v___x_1962_;
                } else {
                    leanh::lean_dec(v___y_1952_);
                    v_searcher_1963_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1964_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_opt_1937_);
                    v___f_1965_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    leanh::lean_closure_set(v___f_1965_, 0, v___x_1953_);
                    leanh::lean_closure_set(v___f_1965_, 1, v_opt_1937_);
                    leanh::lean_closure_set(v___f_1965_, 2, v___x_1964_);
                    v___x_1966_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_1965_,
                        v_searcher_1963_,
                        v___x_1964_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_1966_) == 0 {
                        v___y_1939_ = v___x_1953_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1967_ = leanh::lean_ctor_get(v___x_1966_, 0);
                        leanh::lean_inc(v_val_1967_);
                        leanh::lean_dec_ref_known(v___x_1966_, 1);
                        v___y_1939_ = v_val_1967_;
                        state = 1;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_shortOption___redArg___lam__0(
    mut v___x_1974_: *mut leanh::LeanObject,
    mut v_opt_1975_: *mut leanh::LeanObject,
    mut v_it_1976_: *mut leanh::LeanObject,
    mut v_acc_1977_: *mut leanh::LeanObject,
    mut v_hP_1978_: *mut leanh::LeanObject,
    mut v_recur_1979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1980_: u8 = 0;
    v___x_1980_ = lean_nat_dec_eq(v_it_1976_, v___x_1974_);
    if v___x_1980_ == 0 {
        let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1981_ = lean_string_utf8_next_fast(v_opt_1975_, v_it_1976_);
        v___x_1982_ = leanh::lean_unsigned_to_nat(1);
        v___x_1983_ = lean_nat_add(v_acc_1977_, v___x_1982_);
        v___x_1984_ = leanh::lean_apply_4(
            v_recur_1979_,
            v___x_1981_,
            v___x_1983_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1984_;
    } else {
        leanh::lean_dec_ref(v_recur_1979_);
        leanh::lean_inc(v_acc_1977_);
        return v_acc_1977_;
    }
}
pub unsafe fn l_Lake_shortOption___redArg___lam__0___boxed(
    mut v___x_1985_: *mut leanh::LeanObject,
    mut v_opt_1986_: *mut leanh::LeanObject,
    mut v_it_1987_: *mut leanh::LeanObject,
    mut v_acc_1988_: *mut leanh::LeanObject,
    mut v_hP_1989_: *mut leanh::LeanObject,
    mut v_recur_1990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1991_ = l_Lake_shortOption___redArg___lam__0(
        v___x_1985_,
        v_opt_1986_,
        v_it_1987_,
        v_acc_1988_,
        v_hP_1989_,
        v_recur_1990_,
    );
    leanh::lean_dec(v_acc_1988_);
    leanh::lean_dec(v_it_1987_);
    leanh::lean_dec_ref(v_opt_1986_);
    leanh::lean_dec(v___x_1985_);
    return v_res_1991_;
}
pub unsafe fn l_Lake_shortOption___redArg___lam__1(
    mut v_opt_1992_: *mut leanh::LeanObject,
    mut v_shortHandle_1993_: *mut leanh::LeanObject,
    mut v_____r_1994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: u32 = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1995_ = leanh::lean_unsigned_to_nat(1);
    v___x_1996_ = lean_string_utf8_get(v_opt_1992_, v___x_1995_);
    v___x_1997_ = leanh::lean_box_uint32(v___x_1996_);
    v___x_1998_ = leanh::lean_apply_1(v_shortHandle_1993_, v___x_1997_);
    return v___x_1998_;
}
pub unsafe fn l_Lake_shortOption___redArg___lam__1___boxed(
    mut v_opt_1999_: *mut leanh::LeanObject,
    mut v_shortHandle_2000_: *mut leanh::LeanObject,
    mut v_____r_2001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2002_ =
        l_Lake_shortOption___redArg___lam__1(v_opt_1999_, v_shortHandle_2000_, v_____r_2001_);
    leanh::lean_dec_ref(v_opt_1999_);
    return v_res_2002_;
}
pub unsafe fn l_Lake_shortOption___redArg(
    mut v_inst_2003_: *mut leanh::LeanObject,
    mut v_inst_2004_: *mut leanh::LeanObject,
    mut v_shortHandle_2005_: *mut leanh::LeanObject,
    mut v_longHandle_2006_: *mut leanh::LeanObject,
    mut v_opt_2007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: u8 = 0;
    let mut v___x_2016_: u32 = 0;
    let mut v___x_2017_: u32 = 0;
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: u32 = 0;
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_unused_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: u32 = 0;
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2008_ = leanh::lean_unsigned_to_nat(0);
                v___x_2009_ = lean_string_utf8_byte_size(v_opt_2007_);
                leanh::lean_inc_ref_n(v_opt_2007_, 2);
                v___f_2010_ = leanh::lean_alloc_closure(
                    l_Lake_shortOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    2,
                );
                leanh::lean_closure_set(v___f_2010_, 0, v___x_2009_);
                leanh::lean_closure_set(v___f_2010_, 1, v_opt_2007_);
                v___x_2011_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2011_, 0, v_opt_2007_);
                leanh::lean_ctor_set(v___x_2011_, 1, v___x_2008_);
                leanh::lean_ctor_set(v___x_2011_, 2, v___x_2009_);
                v___x_2012_ = l_String_Slice_positions(v___x_2011_);
                v___x_2013_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2010_,
                    v___x_2012_,
                    v___x_2008_,
                    leanh::lean_box(0),
                );
                v___x_2014_ = leanh::lean_unsigned_to_nat(2);
                v___x_2015_ = lean_nat_dec_eq(v___x_2013_, v___x_2014_);
                leanh::lean_dec(v___x_2013_);
                if v___x_2015_ == 0 {
                    v___x_2016_ = lean_string_utf8_get(v_opt_2007_, v___x_2014_);
                    v___x_2017_ = 61;
                    v___x_2018_ = lean_uint32_dec_eq(v___x_2016_, v___x_2017_);
                    if v___x_2018_ == 0 {
                        v___x_2019_ = 32;
                        v___x_2020_ = lean_uint32_dec_eq(v___x_2016_, v___x_2019_);
                        if v___x_2020_ == 0 {
                            leanh::lean_dec_ref_known(v___x_2011_, 3);
                            leanh::lean_dec(v_shortHandle_2005_);
                            leanh::lean_dec_ref(v_inst_2004_);
                            leanh::lean_dec_ref(v_inst_2003_);
                            v___x_2021_ =
                                leanh::lean_apply_1(v_longHandle_2006_, v_opt_2007_);
                            return v___x_2021_;
                        } else {
                            leanh::lean_dec(v_longHandle_2006_);
                            v_toBind_2022_ = leanh::lean_ctor_get(v_inst_2003_, 1);
                            leanh::lean_inc(v_toBind_2022_);
                            leanh::lean_dec_ref(v_inst_2003_);
                            v___x_2023_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1_once
                                ),
                                _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                            );
                            v_modifyGet_2024_ = leanh::lean_ctor_get(v_inst_2004_, 2);
                            v_isSharedCheck_2039_ =
                                (!leanh::lean_is_exclusive(v_inst_2004_)) as u8;
                            if v_isSharedCheck_2039_ == 0 {
                                v_unused_2040_ = leanh::lean_ctor_get(v_inst_2004_, 1);
                                leanh::lean_dec(v_unused_2040_);
                                v_unused_2041_ = leanh::lean_ctor_get(v_inst_2004_, 0);
                                leanh::lean_dec(v_unused_2041_);
                                v___x_2026_ = v_inst_2004_;
                                v_isShared_2027_ = v_isSharedCheck_2039_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_modifyGet_2024_);
                                leanh::lean_dec(v_inst_2004_);
                                v___x_2026_ = leanh::lean_box(0);
                                v_isShared_2027_ = v_isSharedCheck_2039_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_longHandle_2006_);
                        v_toBind_2042_ = leanh::lean_ctor_get(v_inst_2003_, 1);
                        leanh::lean_inc(v_toBind_2042_);
                        leanh::lean_dec_ref(v_inst_2003_);
                        v_modifyGet_2043_ = leanh::lean_ctor_get(v_inst_2004_, 2);
                        leanh::lean_inc(v_modifyGet_2043_);
                        leanh::lean_dec_ref(v_inst_2004_);
                        leanh::lean_inc_ref(v_opt_2007_);
                        v___f_2044_ = leanh::lean_alloc_closure(
                            l_Lake_shortOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_2044_, 0, v_opt_2007_);
                        leanh::lean_closure_set(v___f_2044_, 1, v_shortHandle_2005_);
                        v___x_2045_ = leanh::lean_unsigned_to_nat(3);
                        v___x_2046_ =
                            l_String_Slice_Pos_nextn(v___x_2011_, v___x_2008_, v___x_2045_);
                        leanh::lean_dec_ref_known(v___x_2011_, 3);
                        v___x_2047_ =
                            lean_string_utf8_extract(v_opt_2007_, v___x_2046_, v___x_2009_);
                        leanh::lean_dec(v___x_2046_);
                        leanh::lean_dec_ref(v_opt_2007_);
                        v___f_2048_ = leanh::lean_alloc_closure(
                            l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_2048_, 0, v___x_2047_);
                        v___x_2049_ = leanh::lean_apply_2(
                            v_modifyGet_2043_,
                            leanh::lean_box(0),
                            v___f_2048_,
                        );
                        v___x_2050_ = leanh::lean_apply_4(
                            v_toBind_2042_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2049_,
                            v___f_2044_,
                        );
                        return v___x_2050_;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2011_, 3);
                    leanh::lean_dec(v_longHandle_2006_);
                    leanh::lean_dec_ref(v_inst_2004_);
                    leanh::lean_dec_ref(v_inst_2003_);
                    v___x_2051_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2052_ = lean_string_utf8_get(v_opt_2007_, v___x_2051_);
                    leanh::lean_dec_ref(v_opt_2007_);
                    v___x_2053_ = leanh::lean_box_uint32(v___x_2052_);
                    v___x_2054_ = leanh::lean_apply_1(v_shortHandle_2005_, v___x_2053_);
                    return v___x_2054_;
                }
            }
            1 => {
                v___x_2028_ = l_String_Slice_Pos_nextn(v___x_2011_, v___x_2008_, v___x_2014_);
                leanh::lean_dec_ref_known(v___x_2011_, 3);
                leanh::lean_inc_ref_n(v_opt_2007_, 2);
                v___f_2029_ = leanh::lean_alloc_closure(
                    l_Lake_shortOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_2029_, 0, v_opt_2007_);
                leanh::lean_closure_set(v___f_2029_, 1, v_shortHandle_2005_);
                leanh::lean_inc(v___x_2028_);
                if v_isShared_2027_ == 0 {
                    leanh::lean_ctor_set(v___x_2026_, 2, v___x_2009_);
                    leanh::lean_ctor_set(v___x_2026_, 1, v___x_2028_);
                    leanh::lean_ctor_set(v___x_2026_, 0, v_opt_2007_);
                    v___x_2031_ = v___x_2026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_opt_2007_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2038_, 2, v___x_2009_);
                    v___x_2031_ = v_reuseFailAlloc_2038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2032_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_2031_, v___x_2008_, v___x_2023_);
                leanh::lean_dec_ref(v___x_2031_);
                v___x_2033_ = lean_nat_add(v___x_2028_, v___x_2032_);
                leanh::lean_dec(v___x_2032_);
                leanh::lean_dec(v___x_2028_);
                v___x_2034_ = lean_string_utf8_extract(v_opt_2007_, v___x_2033_, v___x_2009_);
                leanh::lean_dec(v___x_2033_);
                leanh::lean_dec_ref(v_opt_2007_);
                v___f_2035_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2035_, 0, v___x_2034_);
                v___x_2036_ = leanh::lean_apply_2(
                    v_modifyGet_2024_,
                    leanh::lean_box(0),
                    v___f_2035_,
                );
                v___x_2037_ = leanh::lean_apply_4(
                    v_toBind_2022_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2036_,
                    v___f_2029_,
                );
                return v___x_2037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_shortOption(
    mut v_m_2055_: *mut leanh::LeanObject,
    mut v_inst_2056_: *mut leanh::LeanObject,
    mut v_inst_2057_: *mut leanh::LeanObject,
    mut v_00_u03b1_2058_: *mut leanh::LeanObject,
    mut v_shortHandle_2059_: *mut leanh::LeanObject,
    mut v_longHandle_2060_: *mut leanh::LeanObject,
    mut v_opt_2061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: u8 = 0;
    let mut v___x_2070_: u32 = 0;
    let mut v___x_2071_: u32 = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: u32 = 0;
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2093_: u8 = 0;
    let mut v_unused_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: u32 = 0;
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2062_ = leanh::lean_unsigned_to_nat(0);
                v___x_2063_ = lean_string_utf8_byte_size(v_opt_2061_);
                leanh::lean_inc_ref_n(v_opt_2061_, 2);
                v___f_2064_ = leanh::lean_alloc_closure(
                    l_Lake_shortOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    2,
                );
                leanh::lean_closure_set(v___f_2064_, 0, v___x_2063_);
                leanh::lean_closure_set(v___f_2064_, 1, v_opt_2061_);
                v___x_2065_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2065_, 0, v_opt_2061_);
                leanh::lean_ctor_set(v___x_2065_, 1, v___x_2062_);
                leanh::lean_ctor_set(v___x_2065_, 2, v___x_2063_);
                v___x_2066_ = l_String_Slice_positions(v___x_2065_);
                v___x_2067_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2064_,
                    v___x_2066_,
                    v___x_2062_,
                    leanh::lean_box(0),
                );
                v___x_2068_ = leanh::lean_unsigned_to_nat(2);
                v___x_2069_ = lean_nat_dec_eq(v___x_2067_, v___x_2068_);
                leanh::lean_dec(v___x_2067_);
                if v___x_2069_ == 0 {
                    v___x_2070_ = lean_string_utf8_get(v_opt_2061_, v___x_2068_);
                    v___x_2071_ = 61;
                    v___x_2072_ = lean_uint32_dec_eq(v___x_2070_, v___x_2071_);
                    if v___x_2072_ == 0 {
                        v___x_2073_ = 32;
                        v___x_2074_ = lean_uint32_dec_eq(v___x_2070_, v___x_2073_);
                        if v___x_2074_ == 0 {
                            leanh::lean_dec_ref_known(v___x_2065_, 3);
                            leanh::lean_dec(v_shortHandle_2059_);
                            leanh::lean_dec_ref(v_inst_2057_);
                            leanh::lean_dec_ref(v_inst_2056_);
                            v___x_2075_ =
                                leanh::lean_apply_1(v_longHandle_2060_, v_opt_2061_);
                            return v___x_2075_;
                        } else {
                            leanh::lean_dec(v_longHandle_2060_);
                            v_toBind_2076_ = leanh::lean_ctor_get(v_inst_2056_, 1);
                            leanh::lean_inc(v_toBind_2076_);
                            leanh::lean_dec_ref(v_inst_2056_);
                            v___x_2077_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1_once
                                ),
                                _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                            );
                            v_modifyGet_2078_ = leanh::lean_ctor_get(v_inst_2057_, 2);
                            v_isSharedCheck_2093_ =
                                (!leanh::lean_is_exclusive(v_inst_2057_)) as u8;
                            if v_isSharedCheck_2093_ == 0 {
                                v_unused_2094_ = leanh::lean_ctor_get(v_inst_2057_, 1);
                                leanh::lean_dec(v_unused_2094_);
                                v_unused_2095_ = leanh::lean_ctor_get(v_inst_2057_, 0);
                                leanh::lean_dec(v_unused_2095_);
                                v___x_2080_ = v_inst_2057_;
                                v_isShared_2081_ = v_isSharedCheck_2093_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_modifyGet_2078_);
                                leanh::lean_dec(v_inst_2057_);
                                v___x_2080_ = leanh::lean_box(0);
                                v_isShared_2081_ = v_isSharedCheck_2093_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_longHandle_2060_);
                        v_toBind_2096_ = leanh::lean_ctor_get(v_inst_2056_, 1);
                        leanh::lean_inc(v_toBind_2096_);
                        leanh::lean_dec_ref(v_inst_2056_);
                        v_modifyGet_2097_ = leanh::lean_ctor_get(v_inst_2057_, 2);
                        leanh::lean_inc(v_modifyGet_2097_);
                        leanh::lean_dec_ref(v_inst_2057_);
                        leanh::lean_inc_ref(v_opt_2061_);
                        v___f_2098_ = leanh::lean_alloc_closure(
                            l_Lake_shortOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_2098_, 0, v_opt_2061_);
                        leanh::lean_closure_set(v___f_2098_, 1, v_shortHandle_2059_);
                        v___x_2099_ = leanh::lean_unsigned_to_nat(3);
                        v___x_2100_ =
                            l_String_Slice_Pos_nextn(v___x_2065_, v___x_2062_, v___x_2099_);
                        leanh::lean_dec_ref_known(v___x_2065_, 3);
                        v___x_2101_ =
                            lean_string_utf8_extract(v_opt_2061_, v___x_2100_, v___x_2063_);
                        leanh::lean_dec(v___x_2100_);
                        leanh::lean_dec_ref(v_opt_2061_);
                        v___f_2102_ = leanh::lean_alloc_closure(
                            l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_2102_, 0, v___x_2101_);
                        v___x_2103_ = leanh::lean_apply_2(
                            v_modifyGet_2097_,
                            leanh::lean_box(0),
                            v___f_2102_,
                        );
                        v___x_2104_ = leanh::lean_apply_4(
                            v_toBind_2096_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2103_,
                            v___f_2098_,
                        );
                        return v___x_2104_;
                    }
                } else {
                    leanh::lean_dec_ref_known(v___x_2065_, 3);
                    leanh::lean_dec(v_longHandle_2060_);
                    leanh::lean_dec_ref(v_inst_2057_);
                    leanh::lean_dec_ref(v_inst_2056_);
                    v___x_2105_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2106_ = lean_string_utf8_get(v_opt_2061_, v___x_2105_);
                    leanh::lean_dec_ref(v_opt_2061_);
                    v___x_2107_ = leanh::lean_box_uint32(v___x_2106_);
                    v___x_2108_ = leanh::lean_apply_1(v_shortHandle_2059_, v___x_2107_);
                    return v___x_2108_;
                }
            }
            1 => {
                v___x_2082_ = l_String_Slice_Pos_nextn(v___x_2065_, v___x_2062_, v___x_2068_);
                leanh::lean_dec_ref_known(v___x_2065_, 3);
                leanh::lean_inc_ref_n(v_opt_2061_, 2);
                v___f_2083_ = leanh::lean_alloc_closure(
                    l_Lake_shortOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_2083_, 0, v_opt_2061_);
                leanh::lean_closure_set(v___f_2083_, 1, v_shortHandle_2059_);
                leanh::lean_inc(v___x_2082_);
                if v_isShared_2081_ == 0 {
                    leanh::lean_ctor_set(v___x_2080_, 2, v___x_2063_);
                    leanh::lean_ctor_set(v___x_2080_, 1, v___x_2082_);
                    leanh::lean_ctor_set(v___x_2080_, 0, v_opt_2061_);
                    v___x_2085_ = v___x_2080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_opt_2061_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 2, v___x_2063_);
                    v___x_2085_ = v_reuseFailAlloc_2092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2086_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_2085_, v___x_2062_, v___x_2077_);
                leanh::lean_dec_ref(v___x_2085_);
                v___x_2087_ = lean_nat_add(v___x_2082_, v___x_2086_);
                leanh::lean_dec(v___x_2086_);
                leanh::lean_dec(v___x_2082_);
                v___x_2088_ = lean_string_utf8_extract(v_opt_2061_, v___x_2087_, v___x_2063_);
                leanh::lean_dec(v___x_2087_);
                leanh::lean_dec_ref(v_opt_2061_);
                v___f_2089_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2089_, 0, v___x_2088_);
                v___x_2090_ = leanh::lean_apply_2(
                    v_modifyGet_2078_,
                    leanh::lean_box(0),
                    v___f_2089_,
                );
                v___x_2091_ = leanh::lean_apply_4(
                    v_toBind_2076_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2090_,
                    v___f_2083_,
                );
                return v___x_2091_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_option___redArg___lam__0(
    mut v___x_2109_: *mut leanh::LeanObject,
    mut v_opt_2110_: *mut leanh::LeanObject,
    mut v___x_2111_: *mut leanh::LeanObject,
    mut v_it_2112_: *mut leanh::LeanObject,
    mut v_acc_2113_: *mut leanh::LeanObject,
    mut v_hP_2114_: *mut leanh::LeanObject,
    mut v_recur_2115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2116_: u8 = 0;
    v___x_2116_ = lean_nat_dec_eq(v_it_2112_, v___x_2109_);
    if v___x_2116_ == 0 {
        let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2117_ = lean_string_utf8_next_fast(v_opt_2110_, v_it_2112_);
        v___x_2118_ = lean_nat_add(v_acc_2113_, v___x_2111_);
        v___x_2119_ = leanh::lean_apply_4(
            v_recur_2115_,
            v___x_2117_,
            v___x_2118_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_2119_;
    } else {
        leanh::lean_dec_ref(v_recur_2115_);
        leanh::lean_inc(v_acc_2113_);
        return v_acc_2113_;
    }
}
pub unsafe fn l_Lake_option___redArg___lam__0___boxed(
    mut v___x_2120_: *mut leanh::LeanObject,
    mut v_opt_2121_: *mut leanh::LeanObject,
    mut v___x_2122_: *mut leanh::LeanObject,
    mut v_it_2123_: *mut leanh::LeanObject,
    mut v_acc_2124_: *mut leanh::LeanObject,
    mut v_hP_2125_: *mut leanh::LeanObject,
    mut v_recur_2126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2127_ = l_Lake_option___redArg___lam__0(
        v___x_2120_,
        v_opt_2121_,
        v___x_2122_,
        v_it_2123_,
        v_acc_2124_,
        v_hP_2125_,
        v_recur_2126_,
    );
    leanh::lean_dec(v_acc_2124_);
    leanh::lean_dec(v_it_2123_);
    leanh::lean_dec(v___x_2122_);
    leanh::lean_dec_ref(v_opt_2121_);
    leanh::lean_dec(v___x_2120_);
    return v_res_2127_;
}
pub unsafe fn l_Lake_option___redArg___lam__1(
    mut v_short_2128_: *mut leanh::LeanObject,
    mut v___x_2129_: u32,
    mut v_____r_2130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2131_ = leanh::lean_box_uint32(v___x_2129_);
    v___x_2132_ = leanh::lean_apply_1(v_short_2128_, v___x_2131_);
    return v___x_2132_;
}
pub unsafe fn l_Lake_option___redArg___lam__1___boxed(
    mut v_short_2133_: *mut leanh::LeanObject,
    mut v___x_2134_: *mut leanh::LeanObject,
    mut v_____r_2135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1512__boxed_2136_: u32 = 0;
    let mut v_res_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1512__boxed_2136_ = leanh::lean_unbox_uint32(v___x_2134_);
    leanh::lean_dec(v___x_2134_);
    v_res_2137_ =
        l_Lake_option___redArg___lam__1(v_short_2133_, v___x_1512__boxed_2136_, v_____r_2135_);
    return v_res_2137_;
}
pub unsafe fn l_Lake_option___redArg___lam__5(
    mut v_opt_2138_: *mut leanh::LeanObject,
    mut v___y_2139_: *mut leanh::LeanObject,
    mut v_long_2140_: *mut leanh::LeanObject,
    mut v_____r_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2142_ = leanh::lean_unsigned_to_nat(0);
    v___x_2143_ = lean_string_utf8_extract(v_opt_2138_, v___x_2142_, v___y_2139_);
    v___x_2144_ = leanh::lean_apply_1(v_long_2140_, v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn l_Lake_option___redArg___lam__5___boxed(
    mut v_opt_2145_: *mut leanh::LeanObject,
    mut v___y_2146_: *mut leanh::LeanObject,
    mut v_long_2147_: *mut leanh::LeanObject,
    mut v_____r_2148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2149_ =
        l_Lake_option___redArg___lam__5(v_opt_2145_, v___y_2146_, v_long_2147_, v_____r_2148_);
    leanh::lean_dec(v___y_2146_);
    leanh::lean_dec_ref(v_opt_2145_);
    return v_res_2149_;
}
pub unsafe fn l_Lake_option___redArg___lam__3(
    mut v___x_2150_: *mut leanh::LeanObject,
    mut v_searcher_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
    mut v_long_2153_: *mut leanh::LeanObject,
    mut v_____r_2154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2155_ = lean_string_utf8_extract(v___x_2150_, v_searcher_2151_, v___y_2152_);
    v___x_2156_ = leanh::lean_apply_1(v_long_2153_, v___x_2155_);
    return v___x_2156_;
}
pub unsafe fn l_Lake_option___redArg___lam__3___boxed(
    mut v___x_2157_: *mut leanh::LeanObject,
    mut v_searcher_2158_: *mut leanh::LeanObject,
    mut v___y_2159_: *mut leanh::LeanObject,
    mut v_long_2160_: *mut leanh::LeanObject,
    mut v_____r_2161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2162_ = l_Lake_option___redArg___lam__3(
        v___x_2157_,
        v_searcher_2158_,
        v___y_2159_,
        v_long_2160_,
        v_____r_2161_,
    );
    leanh::lean_dec(v___y_2159_);
    leanh::lean_dec(v_searcher_2158_);
    leanh::lean_dec_ref(v___x_2157_);
    return v_res_2162_;
}
pub unsafe fn l_Lake_option___redArg___lam__6(
    mut v_opt_2163_: *mut leanh::LeanObject,
    mut v___y_2164_: *mut leanh::LeanObject,
    mut v_long_2165_: *mut leanh::LeanObject,
    mut v_modifyGet_2166_: *mut leanh::LeanObject,
    mut v_toBind_2167_: *mut leanh::LeanObject,
    mut v_____r_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_searcher_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: u8 = 0;
    let mut v___f_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_2169_ = leanh::lean_unsigned_to_nat(0);
                v___x_2170_ = lean_string_utf8_extract(v_opt_2163_, v_searcher_2169_, v___y_2164_);
                v___x_2182_ = lean_string_utf8_byte_size(v___x_2170_);
                v___x_2183_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___x_2170_);
                v___f_2184_ = leanh::lean_alloc_closure(
                    l_Lake_longOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_2184_, 0, v___x_2182_);
                leanh::lean_closure_set(v___f_2184_, 1, v___x_2170_);
                leanh::lean_closure_set(v___f_2184_, 2, v___x_2183_);
                v___x_2185_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2184_,
                    v_searcher_2169_,
                    v___x_2183_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_2185_) == 0 {
                    v___y_2172_ = v___x_2182_;
                    state = 1;
                    continue;
                } else {
                    v_val_2186_ = leanh::lean_ctor_get(v___x_2185_, 0);
                    leanh::lean_inc(v_val_2186_);
                    leanh::lean_dec_ref_known(v___x_2185_, 1);
                    v___y_2172_ = v_val_2186_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2173_ = lean_string_utf8_byte_size(v___x_2170_);
                v___x_2174_ = lean_nat_dec_eq(v___y_2172_, v___x_2173_);
                if v___x_2174_ == 0 {
                    leanh::lean_inc(v___y_2172_);
                    leanh::lean_inc_ref(v___x_2170_);
                    v___f_2175_ = leanh::lean_alloc_closure(
                        l_Lake_option___redArg___lam__3___boxed as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    leanh::lean_closure_set(v___f_2175_, 0, v___x_2170_);
                    leanh::lean_closure_set(v___f_2175_, 1, v_searcher_2169_);
                    leanh::lean_closure_set(v___f_2175_, 2, v___y_2172_);
                    leanh::lean_closure_set(v___f_2175_, 3, v_long_2165_);
                    v___x_2176_ = lean_string_utf8_next_fast(v___x_2170_, v___y_2172_);
                    leanh::lean_dec(v___y_2172_);
                    v___x_2177_ = lean_string_utf8_extract(v___x_2170_, v___x_2176_, v___x_2173_);
                    leanh::lean_dec_ref(v___x_2170_);
                    v___f_2178_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2178_, 0, v___x_2177_);
                    v___x_2179_ = leanh::lean_apply_2(
                        v_modifyGet_2166_,
                        leanh::lean_box(0),
                        v___f_2178_,
                    );
                    v___x_2180_ = leanh::lean_apply_4(
                        v_toBind_2167_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2179_,
                        v___f_2175_,
                    );
                    return v___x_2180_;
                } else {
                    leanh::lean_dec(v___y_2172_);
                    leanh::lean_dec(v_toBind_2167_);
                    leanh::lean_dec(v_modifyGet_2166_);
                    v___x_2181_ = leanh::lean_apply_1(v_long_2165_, v___x_2170_);
                    return v___x_2181_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_option___redArg___lam__6___boxed(
    mut v_opt_2187_: *mut leanh::LeanObject,
    mut v___y_2188_: *mut leanh::LeanObject,
    mut v_long_2189_: *mut leanh::LeanObject,
    mut v_modifyGet_2190_: *mut leanh::LeanObject,
    mut v_toBind_2191_: *mut leanh::LeanObject,
    mut v_____r_2192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2193_ = l_Lake_option___redArg___lam__6(
        v_opt_2187_,
        v___y_2188_,
        v_long_2189_,
        v_modifyGet_2190_,
        v_toBind_2191_,
        v_____r_2192_,
    );
    leanh::lean_dec(v___y_2188_);
    leanh::lean_dec_ref(v_opt_2187_);
    return v_res_2193_;
}
pub unsafe fn l_Lake_option___redArg(
    mut v_inst_2194_: *mut leanh::LeanObject,
    mut v_inst_2195_: *mut leanh::LeanObject,
    mut v_handlers_2196_: *mut leanh::LeanObject,
    mut v_opt_2197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u32 = 0;
    let mut v___x_2200_: u32 = 0;
    let mut v___x_2201_: u8 = 0;
    let mut v_short_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_longShort_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut v___x_2216_: u32 = 0;
    let mut v___x_2217_: u32 = 0;
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: u32 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2227_: u8 = 0;
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_unused_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut v_unused_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_long_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v_toBind_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v_toBind_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2198_ = leanh::lean_unsigned_to_nat(1);
                v___x_2199_ = lean_string_utf8_get(v_opt_2197_, v___x_2198_);
                v___x_2200_ = 45;
                v___x_2201_ = lean_uint32_dec_eq(v___x_2199_, v___x_2200_);
                if v___x_2201_ == 0 {
                    v_short_2202_ = leanh::lean_ctor_get(v_handlers_2196_, 1);
                    v_longShort_2203_ = leanh::lean_ctor_get(v_handlers_2196_, 2);
                    v_isSharedCheck_2256_ =
                        (!leanh::lean_is_exclusive(v_handlers_2196_)) as u8;
                    if v_isSharedCheck_2256_ == 0 {
                        v_unused_2257_ = leanh::lean_ctor_get(v_handlers_2196_, 0);
                        leanh::lean_dec(v_unused_2257_);
                        v___x_2205_ = v_handlers_2196_;
                        v_isShared_2206_ = v_isSharedCheck_2256_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_longShort_2203_);
                        leanh::lean_inc(v_short_2202_);
                        leanh::lean_dec(v_handlers_2196_);
                        v___x_2205_ = leanh::lean_box(0);
                        v_isShared_2206_ = v_isSharedCheck_2256_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_long_2258_ = leanh::lean_ctor_get(v_handlers_2196_, 0);
                    leanh::lean_inc(v_long_2258_);
                    leanh::lean_dec_ref(v_handlers_2196_);
                    v_searcher_2289_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2290_ = lean_string_utf8_byte_size(v_opt_2197_);
                    v___x_2291_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_opt_2197_);
                    v___f_2292_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2292_, 0, v___x_2290_);
                    leanh::lean_closure_set(v___f_2292_, 1, v_opt_2197_);
                    leanh::lean_closure_set(v___f_2292_, 2, v___x_2291_);
                    v___x_2293_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2292_,
                        v_searcher_2289_,
                        v___x_2291_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2293_) == 0 {
                        v___y_2273_ = v___x_2290_;
                        state = 6;
                        continue;
                    } else {
                        v_val_2294_ = leanh::lean_ctor_get(v___x_2293_, 0);
                        leanh::lean_inc(v_val_2294_);
                        leanh::lean_dec_ref_known(v___x_2293_, 1);
                        v___y_2273_ = v_val_2294_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2207_ = leanh::lean_unsigned_to_nat(0);
                v___x_2208_ = lean_string_utf8_byte_size(v_opt_2197_);
                leanh::lean_inc_ref_n(v_opt_2197_, 2);
                v___f_2209_ = leanh::lean_alloc_closure(
                    l_Lake_option___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_2209_, 0, v___x_2208_);
                leanh::lean_closure_set(v___f_2209_, 1, v_opt_2197_);
                leanh::lean_closure_set(v___f_2209_, 2, v___x_2198_);
                if v_isShared_2206_ == 0 {
                    leanh::lean_ctor_set(v___x_2205_, 2, v___x_2208_);
                    leanh::lean_ctor_set(v___x_2205_, 1, v___x_2207_);
                    leanh::lean_ctor_set(v___x_2205_, 0, v_opt_2197_);
                    v___x_2211_ = v___x_2205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2255_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_opt_2197_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2255_, 2, v___x_2208_);
                    v___x_2211_ = v_reuseFailAlloc_2255_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2212_ = l_String_Slice_positions(v___x_2211_);
                v___x_2213_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2209_,
                    v___x_2212_,
                    v___x_2207_,
                    leanh::lean_box(0),
                );
                v___x_2214_ = leanh::lean_unsigned_to_nat(2);
                v___x_2215_ = lean_nat_dec_eq(v___x_2213_, v___x_2214_);
                leanh::lean_dec(v___x_2213_);
                if v___x_2215_ == 0 {
                    v___x_2216_ = lean_string_utf8_get(v_opt_2197_, v___x_2214_);
                    v___x_2217_ = 61;
                    v___x_2218_ = lean_uint32_dec_eq(v___x_2216_, v___x_2217_);
                    if v___x_2218_ == 0 {
                        v___x_2219_ = 32;
                        v___x_2220_ = lean_uint32_dec_eq(v___x_2216_, v___x_2219_);
                        if v___x_2220_ == 0 {
                            leanh::lean_dec_ref(v___x_2211_);
                            leanh::lean_dec(v_short_2202_);
                            leanh::lean_dec_ref(v_inst_2195_);
                            leanh::lean_dec_ref(v_inst_2194_);
                            v___x_2221_ =
                                leanh::lean_apply_1(v_longShort_2203_, v_opt_2197_);
                            return v___x_2221_;
                        } else {
                            leanh::lean_dec(v_longShort_2203_);
                            v_toBind_2222_ = leanh::lean_ctor_get(v_inst_2194_, 1);
                            leanh::lean_inc(v_toBind_2222_);
                            leanh::lean_dec_ref(v_inst_2194_);
                            v___x_2223_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1_once
                                ),
                                _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                            );
                            v_modifyGet_2224_ = leanh::lean_ctor_get(v_inst_2195_, 2);
                            v_isSharedCheck_2240_ =
                                (!leanh::lean_is_exclusive(v_inst_2195_)) as u8;
                            if v_isSharedCheck_2240_ == 0 {
                                v_unused_2241_ = leanh::lean_ctor_get(v_inst_2195_, 1);
                                leanh::lean_dec(v_unused_2241_);
                                v_unused_2242_ = leanh::lean_ctor_get(v_inst_2195_, 0);
                                leanh::lean_dec(v_unused_2242_);
                                v___x_2226_ = v_inst_2195_;
                                v_isShared_2227_ = v_isSharedCheck_2240_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_modifyGet_2224_);
                                leanh::lean_dec(v_inst_2195_);
                                v___x_2226_ = leanh::lean_box(0);
                                v_isShared_2227_ = v_isSharedCheck_2240_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_longShort_2203_);
                        v_toBind_2243_ = leanh::lean_ctor_get(v_inst_2194_, 1);
                        leanh::lean_inc(v_toBind_2243_);
                        leanh::lean_dec_ref(v_inst_2194_);
                        v_modifyGet_2244_ = leanh::lean_ctor_get(v_inst_2195_, 2);
                        leanh::lean_inc(v_modifyGet_2244_);
                        leanh::lean_dec_ref(v_inst_2195_);
                        v___x_2245_ = leanh::lean_box_uint32(v___x_2199_);
                        v___f_2246_ = leanh::lean_alloc_closure(
                            l_Lake_option___redArg___lam__1___boxed as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_2246_, 0, v_short_2202_);
                        leanh::lean_closure_set(v___f_2246_, 1, v___x_2245_);
                        v___x_2247_ = leanh::lean_unsigned_to_nat(3);
                        v___x_2248_ =
                            l_String_Slice_Pos_nextn(v___x_2211_, v___x_2207_, v___x_2247_);
                        leanh::lean_dec_ref(v___x_2211_);
                        v___x_2249_ =
                            lean_string_utf8_extract(v_opt_2197_, v___x_2248_, v___x_2208_);
                        leanh::lean_dec(v___x_2248_);
                        leanh::lean_dec_ref(v_opt_2197_);
                        v___f_2250_ = leanh::lean_alloc_closure(
                            l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_2250_, 0, v___x_2249_);
                        v___x_2251_ = leanh::lean_apply_2(
                            v_modifyGet_2244_,
                            leanh::lean_box(0),
                            v___f_2250_,
                        );
                        v___x_2252_ = leanh::lean_apply_4(
                            v_toBind_2243_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2251_,
                            v___f_2246_,
                        );
                        return v___x_2252_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2211_);
                    leanh::lean_dec(v_longShort_2203_);
                    leanh::lean_dec_ref(v_opt_2197_);
                    leanh::lean_dec_ref(v_inst_2195_);
                    leanh::lean_dec_ref(v_inst_2194_);
                    v___x_2253_ = leanh::lean_box_uint32(v___x_2199_);
                    v___x_2254_ = leanh::lean_apply_1(v_short_2202_, v___x_2253_);
                    return v___x_2254_;
                }
            }
            3 => {
                v___x_2228_ = l_String_Slice_Pos_nextn(v___x_2211_, v___x_2207_, v___x_2214_);
                leanh::lean_dec_ref(v___x_2211_);
                v___x_2229_ = leanh::lean_box_uint32(v___x_2199_);
                v___f_2230_ = leanh::lean_alloc_closure(
                    l_Lake_option___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_2230_, 0, v_short_2202_);
                leanh::lean_closure_set(v___f_2230_, 1, v___x_2229_);
                leanh::lean_inc(v___x_2228_);
                leanh::lean_inc_ref(v_opt_2197_);
                if v_isShared_2227_ == 0 {
                    leanh::lean_ctor_set(v___x_2226_, 2, v___x_2208_);
                    leanh::lean_ctor_set(v___x_2226_, 1, v___x_2228_);
                    leanh::lean_ctor_set(v___x_2226_, 0, v_opt_2197_);
                    v___x_2232_ = v___x_2226_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_opt_2197_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2239_, 2, v___x_2208_);
                    v___x_2232_ = v_reuseFailAlloc_2239_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2233_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_2232_, v___x_2207_, v___x_2223_);
                leanh::lean_dec_ref(v___x_2232_);
                v___x_2234_ = lean_nat_add(v___x_2228_, v___x_2233_);
                leanh::lean_dec(v___x_2233_);
                leanh::lean_dec(v___x_2228_);
                v___x_2235_ = lean_string_utf8_extract(v_opt_2197_, v___x_2234_, v___x_2208_);
                leanh::lean_dec(v___x_2234_);
                leanh::lean_dec_ref(v_opt_2197_);
                v___f_2236_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2236_, 0, v___x_2235_);
                v___x_2237_ = leanh::lean_apply_2(
                    v_modifyGet_2224_,
                    leanh::lean_box(0),
                    v___f_2236_,
                );
                v___x_2238_ = leanh::lean_apply_4(
                    v_toBind_2222_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2237_,
                    v___f_2230_,
                );
                return v___x_2238_;
            }
            5 => {
                v___x_2261_ = lean_string_utf8_byte_size(v_opt_2197_);
                v___x_2262_ = lean_nat_dec_eq(v___y_2260_, v___x_2261_);
                if v___x_2262_ == 0 {
                    v_toBind_2263_ = leanh::lean_ctor_get(v_inst_2194_, 1);
                    leanh::lean_inc(v_toBind_2263_);
                    leanh::lean_dec_ref(v_inst_2194_);
                    v_modifyGet_2264_ = leanh::lean_ctor_get(v_inst_2195_, 2);
                    leanh::lean_inc(v_modifyGet_2264_);
                    leanh::lean_dec_ref(v_inst_2195_);
                    leanh::lean_inc(v___y_2260_);
                    leanh::lean_inc_ref(v_opt_2197_);
                    v___f_2265_ = leanh::lean_alloc_closure(
                        l_Lake_option___redArg___lam__5___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2265_, 0, v_opt_2197_);
                    leanh::lean_closure_set(v___f_2265_, 1, v___y_2260_);
                    leanh::lean_closure_set(v___f_2265_, 2, v_long_2258_);
                    v___x_2266_ = lean_string_utf8_next_fast(v_opt_2197_, v___y_2260_);
                    leanh::lean_dec(v___y_2260_);
                    v___x_2267_ = lean_string_utf8_extract(v_opt_2197_, v___x_2266_, v___x_2261_);
                    leanh::lean_dec_ref(v_opt_2197_);
                    v___f_2268_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2268_, 0, v___x_2267_);
                    v___x_2269_ = leanh::lean_apply_2(
                        v_modifyGet_2264_,
                        leanh::lean_box(0),
                        v___f_2268_,
                    );
                    v___x_2270_ = leanh::lean_apply_4(
                        v_toBind_2263_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2269_,
                        v___f_2265_,
                    );
                    return v___x_2270_;
                } else {
                    leanh::lean_dec(v___y_2260_);
                    leanh::lean_dec_ref(v_inst_2195_);
                    leanh::lean_dec_ref(v_inst_2194_);
                    v___x_2271_ = leanh::lean_apply_1(v_long_2258_, v_opt_2197_);
                    return v___x_2271_;
                }
            }
            6 => {
                v___x_2274_ = lean_string_utf8_byte_size(v_opt_2197_);
                v___x_2275_ = lean_nat_dec_eq(v___y_2273_, v___x_2274_);
                if v___x_2275_ == 0 {
                    v_toBind_2276_ = leanh::lean_ctor_get(v_inst_2194_, 1);
                    leanh::lean_inc_n(v_toBind_2276_, 2);
                    leanh::lean_dec_ref(v_inst_2194_);
                    v_modifyGet_2277_ = leanh::lean_ctor_get(v_inst_2195_, 2);
                    leanh::lean_inc_n(v_modifyGet_2277_, 2);
                    leanh::lean_dec_ref(v_inst_2195_);
                    leanh::lean_inc(v___y_2273_);
                    leanh::lean_inc_ref(v_opt_2197_);
                    v___f_2278_ = leanh::lean_alloc_closure(
                        l_Lake_option___redArg___lam__6___boxed as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    leanh::lean_closure_set(v___f_2278_, 0, v_opt_2197_);
                    leanh::lean_closure_set(v___f_2278_, 1, v___y_2273_);
                    leanh::lean_closure_set(v___f_2278_, 2, v_long_2258_);
                    leanh::lean_closure_set(v___f_2278_, 3, v_modifyGet_2277_);
                    leanh::lean_closure_set(v___f_2278_, 4, v_toBind_2276_);
                    v___x_2279_ = lean_string_utf8_next_fast(v_opt_2197_, v___y_2273_);
                    leanh::lean_dec(v___y_2273_);
                    v___x_2280_ = lean_string_utf8_extract(v_opt_2197_, v___x_2279_, v___x_2274_);
                    leanh::lean_dec_ref(v_opt_2197_);
                    v___f_2281_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2281_, 0, v___x_2280_);
                    v___x_2282_ = leanh::lean_apply_2(
                        v_modifyGet_2277_,
                        leanh::lean_box(0),
                        v___f_2281_,
                    );
                    v___x_2283_ = leanh::lean_apply_4(
                        v_toBind_2276_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2282_,
                        v___f_2278_,
                    );
                    return v___x_2283_;
                } else {
                    leanh::lean_dec(v___y_2273_);
                    v_searcher_2284_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2285_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_opt_2197_);
                    v___f_2286_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2286_, 0, v___x_2274_);
                    leanh::lean_closure_set(v___f_2286_, 1, v_opt_2197_);
                    leanh::lean_closure_set(v___f_2286_, 2, v___x_2285_);
                    v___x_2287_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2286_,
                        v_searcher_2284_,
                        v___x_2285_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2287_) == 0 {
                        v___y_2260_ = v___x_2274_;
                        state = 5;
                        continue;
                    } else {
                        v_val_2288_ = leanh::lean_ctor_get(v___x_2287_, 0);
                        leanh::lean_inc(v_val_2288_);
                        leanh::lean_dec_ref_known(v___x_2287_, 1);
                        v___y_2260_ = v_val_2288_;
                        state = 5;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_option(
    mut v_m_2295_: *mut leanh::LeanObject,
    mut v_inst_2296_: *mut leanh::LeanObject,
    mut v_inst_2297_: *mut leanh::LeanObject,
    mut v_00_u03b1_2298_: *mut leanh::LeanObject,
    mut v_handlers_2299_: *mut leanh::LeanObject,
    mut v_opt_2300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u32 = 0;
    let mut v___x_2303_: u32 = 0;
    let mut v___x_2304_: u8 = 0;
    let mut v_short_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_longShort_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: u32 = 0;
    let mut v___x_2320_: u32 = 0;
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: u32 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2330_: u8 = 0;
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v_unused_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut v_unused_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_long_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    let mut v_toBind_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: u8 = 0;
    let mut v_toBind_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_searcher_2392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2301_ = leanh::lean_unsigned_to_nat(1);
                v___x_2302_ = lean_string_utf8_get(v_opt_2300_, v___x_2301_);
                v___x_2303_ = 45;
                v___x_2304_ = lean_uint32_dec_eq(v___x_2302_, v___x_2303_);
                if v___x_2304_ == 0 {
                    v_short_2305_ = leanh::lean_ctor_get(v_handlers_2299_, 1);
                    v_longShort_2306_ = leanh::lean_ctor_get(v_handlers_2299_, 2);
                    v_isSharedCheck_2359_ =
                        (!leanh::lean_is_exclusive(v_handlers_2299_)) as u8;
                    if v_isSharedCheck_2359_ == 0 {
                        v_unused_2360_ = leanh::lean_ctor_get(v_handlers_2299_, 0);
                        leanh::lean_dec(v_unused_2360_);
                        v___x_2308_ = v_handlers_2299_;
                        v_isShared_2309_ = v_isSharedCheck_2359_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_longShort_2306_);
                        leanh::lean_inc(v_short_2305_);
                        leanh::lean_dec(v_handlers_2299_);
                        v___x_2308_ = leanh::lean_box(0);
                        v_isShared_2309_ = v_isSharedCheck_2359_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_long_2361_ = leanh::lean_ctor_get(v_handlers_2299_, 0);
                    leanh::lean_inc(v_long_2361_);
                    leanh::lean_dec_ref(v_handlers_2299_);
                    v_searcher_2392_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2393_ = lean_string_utf8_byte_size(v_opt_2300_);
                    v___x_2394_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_opt_2300_);
                    v___f_2395_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2395_, 0, v___x_2393_);
                    leanh::lean_closure_set(v___f_2395_, 1, v_opt_2300_);
                    leanh::lean_closure_set(v___f_2395_, 2, v___x_2394_);
                    v___x_2396_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2395_,
                        v_searcher_2392_,
                        v___x_2394_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2396_) == 0 {
                        v___y_2376_ = v___x_2393_;
                        state = 6;
                        continue;
                    } else {
                        v_val_2397_ = leanh::lean_ctor_get(v___x_2396_, 0);
                        leanh::lean_inc(v_val_2397_);
                        leanh::lean_dec_ref_known(v___x_2396_, 1);
                        v___y_2376_ = v_val_2397_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2310_ = leanh::lean_unsigned_to_nat(0);
                v___x_2311_ = lean_string_utf8_byte_size(v_opt_2300_);
                leanh::lean_inc_ref_n(v_opt_2300_, 2);
                v___f_2312_ = leanh::lean_alloc_closure(
                    l_Lake_option___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                leanh::lean_closure_set(v___f_2312_, 0, v___x_2311_);
                leanh::lean_closure_set(v___f_2312_, 1, v_opt_2300_);
                leanh::lean_closure_set(v___f_2312_, 2, v___x_2301_);
                if v_isShared_2309_ == 0 {
                    leanh::lean_ctor_set(v___x_2308_, 2, v___x_2311_);
                    leanh::lean_ctor_set(v___x_2308_, 1, v___x_2310_);
                    leanh::lean_ctor_set(v___x_2308_, 0, v_opt_2300_);
                    v___x_2314_ = v___x_2308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_opt_2300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 2, v___x_2311_);
                    v___x_2314_ = v_reuseFailAlloc_2358_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2315_ = l_String_Slice_positions(v___x_2314_);
                v___x_2316_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2312_,
                    v___x_2315_,
                    v___x_2310_,
                    leanh::lean_box(0),
                );
                v___x_2317_ = leanh::lean_unsigned_to_nat(2);
                v___x_2318_ = lean_nat_dec_eq(v___x_2316_, v___x_2317_);
                leanh::lean_dec(v___x_2316_);
                if v___x_2318_ == 0 {
                    v___x_2319_ = lean_string_utf8_get(v_opt_2300_, v___x_2317_);
                    v___x_2320_ = 61;
                    v___x_2321_ = lean_uint32_dec_eq(v___x_2319_, v___x_2320_);
                    if v___x_2321_ == 0 {
                        v___x_2322_ = 32;
                        v___x_2323_ = lean_uint32_dec_eq(v___x_2319_, v___x_2322_);
                        if v___x_2323_ == 0 {
                            leanh::lean_dec_ref(v___x_2314_);
                            leanh::lean_dec(v_short_2305_);
                            leanh::lean_dec_ref(v_inst_2297_);
                            leanh::lean_dec_ref(v_inst_2296_);
                            v___x_2324_ =
                                leanh::lean_apply_1(v_longShort_2306_, v_opt_2300_);
                            return v___x_2324_;
                        } else {
                            leanh::lean_dec(v_longShort_2306_);
                            v_toBind_2325_ = leanh::lean_ctor_get(v_inst_2296_, 1);
                            leanh::lean_inc(v_toBind_2325_);
                            leanh::lean_dec_ref(v_inst_2296_);
                            v___x_2326_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1_once
                                ),
                                _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                            );
                            v_modifyGet_2327_ = leanh::lean_ctor_get(v_inst_2297_, 2);
                            v_isSharedCheck_2343_ =
                                (!leanh::lean_is_exclusive(v_inst_2297_)) as u8;
                            if v_isSharedCheck_2343_ == 0 {
                                v_unused_2344_ = leanh::lean_ctor_get(v_inst_2297_, 1);
                                leanh::lean_dec(v_unused_2344_);
                                v_unused_2345_ = leanh::lean_ctor_get(v_inst_2297_, 0);
                                leanh::lean_dec(v_unused_2345_);
                                v___x_2329_ = v_inst_2297_;
                                v_isShared_2330_ = v_isSharedCheck_2343_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_modifyGet_2327_);
                                leanh::lean_dec(v_inst_2297_);
                                v___x_2329_ = leanh::lean_box(0);
                                v_isShared_2330_ = v_isSharedCheck_2343_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_longShort_2306_);
                        v_toBind_2346_ = leanh::lean_ctor_get(v_inst_2296_, 1);
                        leanh::lean_inc(v_toBind_2346_);
                        leanh::lean_dec_ref(v_inst_2296_);
                        v_modifyGet_2347_ = leanh::lean_ctor_get(v_inst_2297_, 2);
                        leanh::lean_inc(v_modifyGet_2347_);
                        leanh::lean_dec_ref(v_inst_2297_);
                        v___x_2348_ = leanh::lean_box_uint32(v___x_2302_);
                        v___f_2349_ = leanh::lean_alloc_closure(
                            l_Lake_option___redArg___lam__1___boxed as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        leanh::lean_closure_set(v___f_2349_, 0, v_short_2305_);
                        leanh::lean_closure_set(v___f_2349_, 1, v___x_2348_);
                        v___x_2350_ = leanh::lean_unsigned_to_nat(3);
                        v___x_2351_ =
                            l_String_Slice_Pos_nextn(v___x_2314_, v___x_2310_, v___x_2350_);
                        leanh::lean_dec_ref(v___x_2314_);
                        v___x_2352_ =
                            lean_string_utf8_extract(v_opt_2300_, v___x_2351_, v___x_2311_);
                        leanh::lean_dec(v___x_2351_);
                        leanh::lean_dec_ref(v_opt_2300_);
                        v___f_2353_ = leanh::lean_alloc_closure(
                            l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        leanh::lean_closure_set(v___f_2353_, 0, v___x_2352_);
                        v___x_2354_ = leanh::lean_apply_2(
                            v_modifyGet_2347_,
                            leanh::lean_box(0),
                            v___f_2353_,
                        );
                        v___x_2355_ = leanh::lean_apply_4(
                            v_toBind_2346_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2354_,
                            v___f_2349_,
                        );
                        return v___x_2355_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2314_);
                    leanh::lean_dec(v_longShort_2306_);
                    leanh::lean_dec_ref(v_opt_2300_);
                    leanh::lean_dec_ref(v_inst_2297_);
                    leanh::lean_dec_ref(v_inst_2296_);
                    v___x_2356_ = leanh::lean_box_uint32(v___x_2302_);
                    v___x_2357_ = leanh::lean_apply_1(v_short_2305_, v___x_2356_);
                    return v___x_2357_;
                }
            }
            3 => {
                v___x_2331_ = l_String_Slice_Pos_nextn(v___x_2314_, v___x_2310_, v___x_2317_);
                leanh::lean_dec_ref(v___x_2314_);
                v___x_2332_ = leanh::lean_box_uint32(v___x_2302_);
                v___f_2333_ = leanh::lean_alloc_closure(
                    l_Lake_option___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_2333_, 0, v_short_2305_);
                leanh::lean_closure_set(v___f_2333_, 1, v___x_2332_);
                leanh::lean_inc(v___x_2331_);
                leanh::lean_inc_ref(v_opt_2300_);
                if v_isShared_2330_ == 0 {
                    leanh::lean_ctor_set(v___x_2329_, 2, v___x_2311_);
                    leanh::lean_ctor_set(v___x_2329_, 1, v___x_2331_);
                    leanh::lean_ctor_set(v___x_2329_, 0, v_opt_2300_);
                    v___x_2335_ = v___x_2329_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_opt_2300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2331_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2342_, 2, v___x_2311_);
                    v___x_2335_ = v_reuseFailAlloc_2342_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2336_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_2335_, v___x_2310_, v___x_2326_);
                leanh::lean_dec_ref(v___x_2335_);
                v___x_2337_ = lean_nat_add(v___x_2331_, v___x_2336_);
                leanh::lean_dec(v___x_2336_);
                leanh::lean_dec(v___x_2331_);
                v___x_2338_ = lean_string_utf8_extract(v_opt_2300_, v___x_2337_, v___x_2311_);
                leanh::lean_dec(v___x_2337_);
                leanh::lean_dec_ref(v_opt_2300_);
                v___f_2339_ = leanh::lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_2339_, 0, v___x_2338_);
                v___x_2340_ = leanh::lean_apply_2(
                    v_modifyGet_2327_,
                    leanh::lean_box(0),
                    v___f_2339_,
                );
                v___x_2341_ = leanh::lean_apply_4(
                    v_toBind_2325_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2340_,
                    v___f_2333_,
                );
                return v___x_2341_;
            }
            5 => {
                v___x_2364_ = lean_string_utf8_byte_size(v_opt_2300_);
                v___x_2365_ = lean_nat_dec_eq(v___y_2363_, v___x_2364_);
                if v___x_2365_ == 0 {
                    v_toBind_2366_ = leanh::lean_ctor_get(v_inst_2296_, 1);
                    leanh::lean_inc(v_toBind_2366_);
                    leanh::lean_dec_ref(v_inst_2296_);
                    v_modifyGet_2367_ = leanh::lean_ctor_get(v_inst_2297_, 2);
                    leanh::lean_inc(v_modifyGet_2367_);
                    leanh::lean_dec_ref(v_inst_2297_);
                    leanh::lean_inc(v___y_2363_);
                    leanh::lean_inc_ref(v_opt_2300_);
                    v___f_2368_ = leanh::lean_alloc_closure(
                        l_Lake_option___redArg___lam__5___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2368_, 0, v_opt_2300_);
                    leanh::lean_closure_set(v___f_2368_, 1, v___y_2363_);
                    leanh::lean_closure_set(v___f_2368_, 2, v_long_2361_);
                    v___x_2369_ = lean_string_utf8_next_fast(v_opt_2300_, v___y_2363_);
                    leanh::lean_dec(v___y_2363_);
                    v___x_2370_ = lean_string_utf8_extract(v_opt_2300_, v___x_2369_, v___x_2364_);
                    leanh::lean_dec_ref(v_opt_2300_);
                    v___f_2371_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2371_, 0, v___x_2370_);
                    v___x_2372_ = leanh::lean_apply_2(
                        v_modifyGet_2367_,
                        leanh::lean_box(0),
                        v___f_2371_,
                    );
                    v___x_2373_ = leanh::lean_apply_4(
                        v_toBind_2366_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2372_,
                        v___f_2368_,
                    );
                    return v___x_2373_;
                } else {
                    leanh::lean_dec(v___y_2363_);
                    leanh::lean_dec_ref(v_inst_2297_);
                    leanh::lean_dec_ref(v_inst_2296_);
                    v___x_2374_ = leanh::lean_apply_1(v_long_2361_, v_opt_2300_);
                    return v___x_2374_;
                }
            }
            6 => {
                v___x_2377_ = lean_string_utf8_byte_size(v_opt_2300_);
                v___x_2378_ = lean_nat_dec_eq(v___y_2376_, v___x_2377_);
                if v___x_2378_ == 0 {
                    v_toBind_2379_ = leanh::lean_ctor_get(v_inst_2296_, 1);
                    leanh::lean_inc_n(v_toBind_2379_, 2);
                    leanh::lean_dec_ref(v_inst_2296_);
                    v_modifyGet_2380_ = leanh::lean_ctor_get(v_inst_2297_, 2);
                    leanh::lean_inc_n(v_modifyGet_2380_, 2);
                    leanh::lean_dec_ref(v_inst_2297_);
                    leanh::lean_inc(v___y_2376_);
                    leanh::lean_inc_ref(v_opt_2300_);
                    v___f_2381_ = leanh::lean_alloc_closure(
                        l_Lake_option___redArg___lam__6___boxed as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    leanh::lean_closure_set(v___f_2381_, 0, v_opt_2300_);
                    leanh::lean_closure_set(v___f_2381_, 1, v___y_2376_);
                    leanh::lean_closure_set(v___f_2381_, 2, v_long_2361_);
                    leanh::lean_closure_set(v___f_2381_, 3, v_modifyGet_2380_);
                    leanh::lean_closure_set(v___f_2381_, 4, v_toBind_2379_);
                    v___x_2382_ = lean_string_utf8_next_fast(v_opt_2300_, v___y_2376_);
                    leanh::lean_dec(v___y_2376_);
                    v___x_2383_ = lean_string_utf8_extract(v_opt_2300_, v___x_2382_, v___x_2377_);
                    leanh::lean_dec_ref(v_opt_2300_);
                    v___f_2384_ = leanh::lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2384_, 0, v___x_2383_);
                    v___x_2385_ = leanh::lean_apply_2(
                        v_modifyGet_2380_,
                        leanh::lean_box(0),
                        v___f_2384_,
                    );
                    v___x_2386_ = leanh::lean_apply_4(
                        v_toBind_2379_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2385_,
                        v___f_2381_,
                    );
                    return v___x_2386_;
                } else {
                    leanh::lean_dec(v___y_2376_);
                    v_searcher_2387_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2388_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_opt_2300_);
                    v___f_2389_ = leanh::lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2389_, 0, v___x_2377_);
                    leanh::lean_closure_set(v___f_2389_, 1, v_opt_2300_);
                    leanh::lean_closure_set(v___f_2389_, 2, v___x_2388_);
                    v___x_2390_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2389_,
                        v_searcher_2387_,
                        v___x_2388_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_2390_) == 0 {
                        v___y_2363_ = v___x_2377_;
                        state = 5;
                        continue;
                    } else {
                        v_val_2391_ = leanh::lean_ctor_get(v___x_2390_, 0);
                        leanh::lean_inc(v_val_2391_);
                        leanh::lean_dec_ref_known(v___x_2390_, 1);
                        v___y_2363_ = v_val_2391_;
                        state = 5;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_processLeadingOption___redArg___lam__0(
    mut v_handle_2398_: *mut leanh::LeanObject,
    mut v_head_2399_: *mut leanh::LeanObject,
    mut v_____r_2400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2401_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2401_ = leanh::lean_apply_1(v_handle_2398_, v_head_2399_);
    return v___x_2401_;
}
pub unsafe fn l_Lake_processLeadingOption___redArg___lam__1(
    mut v___x_2402_: *mut leanh::LeanObject,
    mut v_head_2403_: *mut leanh::LeanObject,
    mut v___x_2404_: *mut leanh::LeanObject,
    mut v_it_2405_: *mut leanh::LeanObject,
    mut v_acc_2406_: *mut leanh::LeanObject,
    mut v_hP_2407_: *mut leanh::LeanObject,
    mut v_recur_2408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2409_: u8 = 0;
    v___x_2409_ = lean_nat_dec_eq(v_it_2405_, v___x_2402_);
    if v___x_2409_ == 0 {
        let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2410_ = lean_string_utf8_next_fast(v_head_2403_, v_it_2405_);
        v___x_2411_ = lean_nat_add(v_acc_2406_, v___x_2404_);
        v___x_2412_ = leanh::lean_apply_4(
            v_recur_2408_,
            v___x_2410_,
            v___x_2411_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_2412_;
    } else {
        leanh::lean_dec_ref(v_recur_2408_);
        leanh::lean_inc(v_acc_2406_);
        return v_acc_2406_;
    }
}
pub unsafe fn l_Lake_processLeadingOption___redArg___lam__1___boxed(
    mut v___x_2413_: *mut leanh::LeanObject,
    mut v_head_2414_: *mut leanh::LeanObject,
    mut v___x_2415_: *mut leanh::LeanObject,
    mut v_it_2416_: *mut leanh::LeanObject,
    mut v_acc_2417_: *mut leanh::LeanObject,
    mut v_hP_2418_: *mut leanh::LeanObject,
    mut v_recur_2419_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2420_ = l_Lake_processLeadingOption___redArg___lam__1(
        v___x_2413_,
        v_head_2414_,
        v___x_2415_,
        v_it_2416_,
        v_acc_2417_,
        v_hP_2418_,
        v_recur_2419_,
    );
    leanh::lean_dec(v_acc_2417_);
    leanh::lean_dec(v_it_2416_);
    leanh::lean_dec(v___x_2415_);
    leanh::lean_dec_ref(v_head_2414_);
    leanh::lean_dec(v___x_2413_);
    return v_res_2420_;
}
pub unsafe fn l_Lake_processLeadingOption___redArg___lam__2(
    mut v_toPure_2421_: *mut leanh::LeanObject,
    mut v_handle_2422_: *mut leanh::LeanObject,
    mut v_set_2423_: *mut leanh::LeanObject,
    mut v_toBind_2424_: *mut leanh::LeanObject,
    mut v_____do__lift_2425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2432_: u8 = 0;
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: u32 = 0;
    let mut v___x_2446_: u32 = 0;
    let mut v___x_2447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2425_) == 0 {
                    leanh::lean_dec(v_toBind_2424_);
                    leanh::lean_dec(v_set_2423_);
                    leanh::lean_dec(v_handle_2422_);
                    v___x_2426_ = leanh::lean_box(0);
                    v___x_2427_ = leanh::lean_apply_2(
                        v_toPure_2421_,
                        leanh::lean_box(0),
                        v___x_2426_,
                    );
                    return v___x_2427_;
                } else {
                    v_head_2428_ = leanh::lean_ctor_get(v_____do__lift_2425_, 0);
                    leanh::lean_inc_n(v_head_2428_, 4);
                    v_tail_2429_ = leanh::lean_ctor_get(v_____do__lift_2425_, 1);
                    leanh::lean_inc(v_tail_2429_);
                    leanh::lean_dec_ref_known(v_____do__lift_2425_, 2);
                    v___f_2430_ = leanh::lean_alloc_closure(
                        l_Lake_processLeadingOption___redArg___lam__0 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2430_, 0, v_handle_2422_);
                    leanh::lean_closure_set(v___f_2430_, 1, v_head_2428_);
                    v___x_2437_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2438_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2439_ = lean_string_utf8_byte_size(v_head_2428_);
                    v___f_2440_ = leanh::lean_alloc_closure(
                        l_Lake_processLeadingOption___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    leanh::lean_closure_set(v___f_2440_, 0, v___x_2439_);
                    leanh::lean_closure_set(v___f_2440_, 1, v_head_2428_);
                    leanh::lean_closure_set(v___f_2440_, 2, v___x_2437_);
                    v___x_2441_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2441_, 0, v_head_2428_);
                    leanh::lean_ctor_set(v___x_2441_, 1, v___x_2438_);
                    leanh::lean_ctor_set(v___x_2441_, 2, v___x_2439_);
                    v___x_2442_ = l_String_Slice_positions(v___x_2441_);
                    leanh::lean_dec_ref_known(v___x_2441_, 3);
                    v___x_2443_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2440_,
                        v___x_2442_,
                        v___x_2438_,
                        leanh::lean_box(0),
                    );
                    v___x_2444_ = lean_nat_dec_lt(v___x_2437_, v___x_2443_);
                    leanh::lean_dec(v___x_2443_);
                    if v___x_2444_ == 0 {
                        leanh::lean_dec(v_head_2428_);
                        v___y_2432_ = v___x_2444_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2445_ = lean_string_utf8_get(v_head_2428_, v___x_2438_);
                        leanh::lean_dec(v_head_2428_);
                        v___x_2446_ = 45;
                        v___x_2447_ = lean_uint32_dec_eq(v___x_2445_, v___x_2446_);
                        v___y_2432_ = v___x_2447_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2432_ == 0 {
                    leanh::lean_dec_ref(v___f_2430_);
                    leanh::lean_dec(v_tail_2429_);
                    leanh::lean_dec(v_toBind_2424_);
                    leanh::lean_dec(v_set_2423_);
                    v___x_2433_ = leanh::lean_box(0);
                    v___x_2434_ = leanh::lean_apply_2(
                        v_toPure_2421_,
                        leanh::lean_box(0),
                        v___x_2433_,
                    );
                    return v___x_2434_;
                } else {
                    leanh::lean_dec(v_toPure_2421_);
                    v___x_2435_ = leanh::lean_apply_1(v_set_2423_, v_tail_2429_);
                    v___x_2436_ = leanh::lean_apply_4(
                        v_toBind_2424_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2435_,
                        v___f_2430_,
                    );
                    return v___x_2436_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_processLeadingOption___redArg(
    mut v_inst_2448_: *mut leanh::LeanObject,
    mut v_inst_2449_: *mut leanh::LeanObject,
    mut v_handle_2450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2451_ = leanh::lean_ctor_get(v_inst_2448_, 0);
    leanh::lean_inc_ref(v_toApplicative_2451_);
    v_toBind_2452_ = leanh::lean_ctor_get(v_inst_2448_, 1);
    leanh::lean_inc_n(v_toBind_2452_, 2);
    leanh::lean_dec_ref(v_inst_2448_);
    v_get_2453_ = leanh::lean_ctor_get(v_inst_2449_, 0);
    leanh::lean_inc(v_get_2453_);
    v_set_2454_ = leanh::lean_ctor_get(v_inst_2449_, 1);
    leanh::lean_inc(v_set_2454_);
    leanh::lean_dec_ref(v_inst_2449_);
    v_toPure_2455_ = leanh::lean_ctor_get(v_toApplicative_2451_, 1);
    leanh::lean_inc(v_toPure_2455_);
    leanh::lean_dec_ref(v_toApplicative_2451_);
    v___f_2456_ = leanh::lean_alloc_closure(
        l_Lake_processLeadingOption___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2456_, 0, v_toPure_2455_);
    leanh::lean_closure_set(v___f_2456_, 1, v_handle_2450_);
    leanh::lean_closure_set(v___f_2456_, 2, v_set_2454_);
    leanh::lean_closure_set(v___f_2456_, 3, v_toBind_2452_);
    v___x_2457_ = leanh::lean_apply_4(
        v_toBind_2452_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_get_2453_,
        v___f_2456_,
    );
    return v___x_2457_;
}
pub unsafe fn l_Lake_processLeadingOption(
    mut v_m_2458_: *mut leanh::LeanObject,
    mut v_inst_2459_: *mut leanh::LeanObject,
    mut v_inst_2460_: *mut leanh::LeanObject,
    mut v_handle_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2462_ = l_Lake_processLeadingOption___redArg(v_inst_2459_, v_inst_2460_, v_handle_2461_);
    return v___x_2462_;
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__1(
    mut v___x_2463_: *mut leanh::LeanObject,
    mut v_head_2464_: *mut leanh::LeanObject,
    mut v_it_2465_: *mut leanh::LeanObject,
    mut v_acc_2466_: *mut leanh::LeanObject,
    mut v_hP_2467_: *mut leanh::LeanObject,
    mut v_recur_2468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2469_: u8 = 0;
    v___x_2469_ = lean_nat_dec_eq(v_it_2465_, v___x_2463_);
    if v___x_2469_ == 0 {
        let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2470_ = lean_string_utf8_next_fast(v_head_2464_, v_it_2465_);
        v___x_2471_ = leanh::lean_unsigned_to_nat(1);
        v___x_2472_ = lean_nat_add(v_acc_2466_, v___x_2471_);
        v___x_2473_ = leanh::lean_apply_4(
            v_recur_2468_,
            v___x_2470_,
            v___x_2472_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_2473_;
    } else {
        leanh::lean_dec_ref(v_recur_2468_);
        leanh::lean_inc(v_acc_2466_);
        return v_acc_2466_;
    }
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__1___boxed(
    mut v___x_2474_: *mut leanh::LeanObject,
    mut v_head_2475_: *mut leanh::LeanObject,
    mut v_it_2476_: *mut leanh::LeanObject,
    mut v_acc_2477_: *mut leanh::LeanObject,
    mut v_hP_2478_: *mut leanh::LeanObject,
    mut v_recur_2479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2480_ = l_Lake_processLeadingOptions___redArg___lam__1(
        v___x_2474_,
        v_head_2475_,
        v_it_2476_,
        v_acc_2477_,
        v_hP_2478_,
        v_recur_2479_,
    );
    leanh::lean_dec(v_acc_2477_);
    leanh::lean_dec(v_it_2476_);
    leanh::lean_dec_ref(v_head_2475_);
    leanh::lean_dec(v___x_2474_);
    return v_res_2480_;
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__2(
    mut v_handle_2481_: *mut leanh::LeanObject,
    mut v_head_2482_: *mut leanh::LeanObject,
    mut v_toBind_2483_: *mut leanh::LeanObject,
    mut v___f_2484_: *mut leanh::LeanObject,
    mut v_____r_2485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2486_ = leanh::lean_apply_1(v_handle_2481_, v_head_2482_);
    v___x_2487_ = leanh::lean_apply_4(
        v_toBind_2483_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2486_,
        v___f_2484_,
    );
    return v___x_2487_;
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__3(
    mut v_handle_2488_: *mut leanh::LeanObject,
    mut v_toBind_2489_: *mut leanh::LeanObject,
    mut v___f_2490_: *mut leanh::LeanObject,
    mut v_toPure_2491_: *mut leanh::LeanObject,
    mut v_set_2492_: *mut leanh::LeanObject,
    mut v___f_2493_: *mut leanh::LeanObject,
    mut v_____do__lift_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_len_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut v___x_2507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: u32 = 0;
    let mut v___x_2516_: u32 = 0;
    let mut v___x_2517_: u8 = 0;
    let mut v___x_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2494_) == 1 {
                    v_head_2495_ = leanh::lean_ctor_get(v_____do__lift_2494_, 0);
                    leanh::lean_inc_n(v_head_2495_, 4);
                    v_tail_2496_ = leanh::lean_ctor_get(v_____do__lift_2494_, 1);
                    leanh::lean_inc(v_tail_2496_);
                    leanh::lean_dec_ref_known(v_____do__lift_2494_, 2);
                    leanh::lean_inc(v_toBind_2489_);
                    v___f_2497_ = leanh::lean_alloc_closure(
                        l_Lake_processLeadingOptions___redArg___lam__2 as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    leanh::lean_closure_set(v___f_2497_, 0, v_handle_2488_);
                    leanh::lean_closure_set(v___f_2497_, 1, v_head_2495_);
                    leanh::lean_closure_set(v___f_2497_, 2, v_toBind_2489_);
                    leanh::lean_closure_set(v___f_2497_, 3, v___f_2490_);
                    v___x_2498_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2499_ = lean_string_utf8_byte_size(v_head_2495_);
                    v___f_2500_ = leanh::lean_alloc_closure(
                        l_Lake_processLeadingOptions___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        6,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2500_, 0, v___x_2499_);
                    leanh::lean_closure_set(v___f_2500_, 1, v_head_2495_);
                    v___x_2501_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2501_, 0, v_head_2495_);
                    leanh::lean_ctor_set(v___x_2501_, 1, v___x_2498_);
                    leanh::lean_ctor_set(v___x_2501_, 2, v___x_2499_);
                    v___x_2502_ = l_String_Slice_positions(v___x_2501_);
                    leanh::lean_dec_ref_known(v___x_2501_, 3);
                    v_len_2503_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2500_,
                        v___x_2502_,
                        v___x_2498_,
                        leanh::lean_box(0),
                    );
                    v___x_2513_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2514_ = lean_nat_dec_lt(v___x_2513_, v_len_2503_);
                    if v___x_2514_ == 0 {
                        leanh::lean_dec(v_head_2495_);
                        v___y_2505_ = v___x_2514_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2515_ = lean_string_utf8_get(v_head_2495_, v___x_2498_);
                        leanh::lean_dec(v_head_2495_);
                        v___x_2516_ = 45;
                        v___x_2517_ = lean_uint32_dec_eq(v___x_2515_, v___x_2516_);
                        v___y_2505_ = v___x_2517_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_____do__lift_2494_);
                    leanh::lean_dec(v___f_2493_);
                    leanh::lean_dec(v_set_2492_);
                    leanh::lean_dec(v___f_2490_);
                    leanh::lean_dec(v_toBind_2489_);
                    leanh::lean_dec(v_handle_2488_);
                    v___x_2518_ = leanh::lean_box(0);
                    v___x_2519_ = leanh::lean_apply_2(
                        v_toPure_2491_,
                        leanh::lean_box(0),
                        v___x_2518_,
                    );
                    return v___x_2519_;
                }
            }
            1 => {
                if v___y_2505_ == 0 {
                    leanh::lean_dec_ref(v___f_2497_);
                    v___x_2506_ = lean_nat_dec_eq(v_len_2503_, v___x_2498_);
                    leanh::lean_dec(v_len_2503_);
                    if v___x_2506_ == 0 {
                        leanh::lean_dec(v_tail_2496_);
                        leanh::lean_dec(v___f_2493_);
                        leanh::lean_dec(v_set_2492_);
                        leanh::lean_dec(v_toBind_2489_);
                        v___x_2507_ = leanh::lean_box(0);
                        v___x_2508_ = leanh::lean_apply_2(
                            v_toPure_2491_,
                            leanh::lean_box(0),
                            v___x_2507_,
                        );
                        return v___x_2508_;
                    } else {
                        leanh::lean_dec(v_toPure_2491_);
                        v___x_2509_ = leanh::lean_apply_1(v_set_2492_, v_tail_2496_);
                        v___x_2510_ = leanh::lean_apply_4(
                            v_toBind_2489_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2509_,
                            v___f_2493_,
                        );
                        return v___x_2510_;
                    }
                } else {
                    leanh::lean_dec(v_len_2503_);
                    leanh::lean_dec(v___f_2493_);
                    leanh::lean_dec(v_toPure_2491_);
                    v___x_2511_ = leanh::lean_apply_1(v_set_2492_, v_tail_2496_);
                    v___x_2512_ = leanh::lean_apply_4(
                        v_toBind_2489_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2511_,
                        v___f_2497_,
                    );
                    return v___x_2512_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_processLeadingOptions___redArg(
    mut v_inst_2520_: *mut leanh::LeanObject,
    mut v_inst_2521_: *mut leanh::LeanObject,
    mut v_handle_2522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_set_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2523_ = leanh::lean_ctor_get(v_inst_2520_, 0);
    v_toBind_2524_ = leanh::lean_ctor_get(v_inst_2520_, 1);
    leanh::lean_inc_n(v_toBind_2524_, 2);
    v_get_2525_ = leanh::lean_ctor_get(v_inst_2521_, 0);
    leanh::lean_inc(v_get_2525_);
    v_set_2526_ = leanh::lean_ctor_get(v_inst_2521_, 1);
    leanh::lean_inc(v_set_2526_);
    v_toPure_2527_ = leanh::lean_ctor_get(v_toApplicative_2523_, 1);
    leanh::lean_inc(v_toPure_2527_);
    leanh::lean_inc(v_handle_2522_);
    v___f_2528_ = leanh::lean_alloc_closure(
        l_Lake_processLeadingOptions___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2528_, 0, v_inst_2520_);
    leanh::lean_closure_set(v___f_2528_, 1, v_inst_2521_);
    leanh::lean_closure_set(v___f_2528_, 2, v_handle_2522_);
    leanh::lean_inc_ref(v___f_2528_);
    v___f_2529_ = leanh::lean_alloc_closure(
        l_Lake_processLeadingOptions___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    leanh::lean_closure_set(v___f_2529_, 0, v_handle_2522_);
    leanh::lean_closure_set(v___f_2529_, 1, v_toBind_2524_);
    leanh::lean_closure_set(v___f_2529_, 2, v___f_2528_);
    leanh::lean_closure_set(v___f_2529_, 3, v_toPure_2527_);
    leanh::lean_closure_set(v___f_2529_, 4, v_set_2526_);
    leanh::lean_closure_set(v___f_2529_, 5, v___f_2528_);
    v___x_2530_ = leanh::lean_apply_4(
        v_toBind_2524_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_get_2525_,
        v___f_2529_,
    );
    return v___x_2530_;
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__0(
    mut v_inst_2531_: *mut leanh::LeanObject,
    mut v_inst_2532_: *mut leanh::LeanObject,
    mut v_handle_2533_: *mut leanh::LeanObject,
    mut v_____r_2534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2535_ = l_Lake_processLeadingOptions___redArg(v_inst_2531_, v_inst_2532_, v_handle_2533_);
    return v___x_2535_;
}
pub unsafe fn l_Lake_processLeadingOptions(
    mut v_m_2536_: *mut leanh::LeanObject,
    mut v_inst_2537_: *mut leanh::LeanObject,
    mut v_inst_2538_: *mut leanh::LeanObject,
    mut v_handle_2539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2540_ = l_Lake_processLeadingOptions___redArg(v_inst_2537_, v_inst_2538_, v_handle_2539_);
    return v___x_2540_;
}
pub unsafe fn l_Lake_collectArgs___redArg___lam__0(
    mut v_x_2541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2548_: u8 = 0;
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2553_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2541_) == 0 {
                    v___x_2542_ = leanh::lean_box(0);
                    v___x_2543_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2543_, 0, v___x_2542_);
                    leanh::lean_ctor_set(v___x_2543_, 1, v_x_2541_);
                    return v___x_2543_;
                } else {
                    v_head_2544_ = leanh::lean_ctor_get(v_x_2541_, 0);
                    v_tail_2545_ = leanh::lean_ctor_get(v_x_2541_, 1);
                    v_isSharedCheck_2553_ = (!leanh::lean_is_exclusive(v_x_2541_)) as u8;
                    if v_isSharedCheck_2553_ == 0 {
                        v___x_2547_ = v_x_2541_;
                        v_isShared_2548_ = v_isSharedCheck_2553_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2545_);
                        leanh::lean_inc(v_head_2544_);
                        leanh::lean_dec(v_x_2541_);
                        v___x_2547_ = leanh::lean_box(0);
                        v_isShared_2548_ = v_isSharedCheck_2553_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2549_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2549_, 0, v_head_2544_);
                if v_isShared_2548_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2547_, 0);
                    leanh::lean_ctor_set(v___x_2547_, 0, v___x_2549_);
                    v___x_2551_ = v___x_2547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2552_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_tail_2545_);
                    v___x_2551_ = v_reuseFailAlloc_2552_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2551_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_collectArgs___redArg___lam__2(
    mut v___x_2554_: *mut leanh::LeanObject,
    mut v_val_2555_: *mut leanh::LeanObject,
    mut v_it_2556_: *mut leanh::LeanObject,
    mut v_acc_2557_: *mut leanh::LeanObject,
    mut v_hP_2558_: *mut leanh::LeanObject,
    mut v_recur_2559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2560_: u8 = 0;
    v___x_2560_ = lean_nat_dec_eq(v_it_2556_, v___x_2554_);
    if v___x_2560_ == 0 {
        let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2561_ = lean_string_utf8_next_fast(v_val_2555_, v_it_2556_);
        v___x_2562_ = leanh::lean_unsigned_to_nat(1);
        v___x_2563_ = lean_nat_add(v_acc_2557_, v___x_2562_);
        v___x_2564_ = leanh::lean_apply_4(
            v_recur_2559_,
            v___x_2561_,
            v___x_2563_,
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_2564_;
    } else {
        leanh::lean_dec_ref(v_recur_2559_);
        leanh::lean_inc(v_acc_2557_);
        return v_acc_2557_;
    }
}
pub unsafe fn l_Lake_collectArgs___redArg___lam__2___boxed(
    mut v___x_2565_: *mut leanh::LeanObject,
    mut v_val_2566_: *mut leanh::LeanObject,
    mut v_it_2567_: *mut leanh::LeanObject,
    mut v_acc_2568_: *mut leanh::LeanObject,
    mut v_hP_2569_: *mut leanh::LeanObject,
    mut v_recur_2570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2571_ = l_Lake_collectArgs___redArg___lam__2(
        v___x_2565_,
        v_val_2566_,
        v_it_2567_,
        v_acc_2568_,
        v_hP_2569_,
        v_recur_2570_,
    );
    leanh::lean_dec(v_acc_2568_);
    leanh::lean_dec(v_it_2567_);
    leanh::lean_dec_ref(v_val_2566_);
    leanh::lean_dec(v___x_2565_);
    return v_res_2571_;
}
pub unsafe fn l_Lake_collectArgs___redArg___lam__3(
    mut v_args_2573_: *mut leanh::LeanObject,
    mut v_inst_2574_: *mut leanh::LeanObject,
    mut v_inst_2575_: *mut leanh::LeanObject,
    mut v_option_2576_: *mut leanh::LeanObject,
    mut v_toBind_2577_: *mut leanh::LeanObject,
    mut v___f_2578_: *mut leanh::LeanObject,
    mut v_toPure_2579_: *mut leanh::LeanObject,
    mut v_____do__lift_2580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_len_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: u8 = 0;
    let mut v___x_2590_: u8 = 0;
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: u32 = 0;
    let mut v___x_2599_: u32 = 0;
    let mut v___x_2600_: u8 = 0;
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2580_) == 1 {
                    leanh::lean_dec(v_toPure_2579_);
                    v_val_2581_ = leanh::lean_ctor_get(v_____do__lift_2580_, 0);
                    leanh::lean_inc_n(v_val_2581_, 3);
                    leanh::lean_dec_ref_known(v_____do__lift_2580_, 1);
                    v___x_2582_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2583_ = lean_string_utf8_byte_size(v_val_2581_);
                    v___f_2584_ = leanh::lean_alloc_closure(
                        l_Lake_collectArgs___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        6,
                        2,
                    );
                    leanh::lean_closure_set(v___f_2584_, 0, v___x_2583_);
                    leanh::lean_closure_set(v___f_2584_, 1, v_val_2581_);
                    v___x_2585_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_2585_, 0, v_val_2581_);
                    leanh::lean_ctor_set(v___x_2585_, 1, v___x_2582_);
                    leanh::lean_ctor_set(v___x_2585_, 2, v___x_2583_);
                    v___x_2586_ = l_String_Slice_positions(v___x_2585_);
                    leanh::lean_dec_ref_known(v___x_2585_, 3);
                    v_len_2587_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2584_,
                        v___x_2586_,
                        v___x_2582_,
                        leanh::lean_box(0),
                    );
                    v___x_2596_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2597_ = lean_nat_dec_lt(v___x_2596_, v_len_2587_);
                    if v___x_2597_ == 0 {
                        v___y_2589_ = v___x_2597_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2598_ = lean_string_utf8_get(v_val_2581_, v___x_2582_);
                        v___x_2599_ = 45;
                        v___x_2600_ = lean_uint32_dec_eq(v___x_2598_, v___x_2599_);
                        v___y_2589_ = v___x_2600_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_____do__lift_2580_);
                    leanh::lean_dec(v___f_2578_);
                    leanh::lean_dec(v_toBind_2577_);
                    leanh::lean_dec(v_option_2576_);
                    leanh::lean_dec_ref(v_inst_2575_);
                    leanh::lean_dec_ref(v_inst_2574_);
                    v___x_2601_ = leanh::lean_apply_2(
                        v_toPure_2579_,
                        leanh::lean_box(0),
                        v_args_2573_,
                    );
                    return v___x_2601_;
                }
            }
            1 => {
                if v___y_2589_ == 0 {
                    leanh::lean_dec(v___f_2578_);
                    leanh::lean_dec(v_toBind_2577_);
                    v___x_2590_ = lean_nat_dec_eq(v_len_2587_, v___x_2582_);
                    leanh::lean_dec(v_len_2587_);
                    if v___x_2590_ == 0 {
                        v___x_2591_ = lean_array_push(v_args_2573_, v_val_2581_);
                        v___x_2592_ = l_Lake_collectArgs___redArg(
                            v_inst_2574_,
                            v_inst_2575_,
                            v_option_2576_,
                            v___x_2591_,
                        );
                        return v___x_2592_;
                    } else {
                        leanh::lean_dec(v_val_2581_);
                        v___x_2593_ = l_Lake_collectArgs___redArg(
                            v_inst_2574_,
                            v_inst_2575_,
                            v_option_2576_,
                            v_args_2573_,
                        );
                        return v___x_2593_;
                    }
                } else {
                    leanh::lean_dec(v_len_2587_);
                    leanh::lean_dec_ref(v_inst_2575_);
                    leanh::lean_dec_ref(v_inst_2574_);
                    leanh::lean_dec_ref(v_args_2573_);
                    v___x_2594_ = leanh::lean_apply_1(v_option_2576_, v_val_2581_);
                    v___x_2595_ = leanh::lean_apply_4(
                        v_toBind_2577_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2594_,
                        v___f_2578_,
                    );
                    return v___x_2595_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_collectArgs___redArg(
    mut v_inst_2602_: *mut leanh::LeanObject,
    mut v_inst_2603_: *mut leanh::LeanObject,
    mut v_option_2604_: *mut leanh::LeanObject,
    mut v_args_2605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2606_ = leanh::lean_ctor_get(v_inst_2602_, 0);
    v_toBind_2607_ = leanh::lean_ctor_get(v_inst_2602_, 1);
    leanh::lean_inc_n(v_toBind_2607_, 2);
    v_modifyGet_2608_ = leanh::lean_ctor_get(v_inst_2603_, 2);
    v_toPure_2609_ = leanh::lean_ctor_get(v_toApplicative_2606_, 1);
    leanh::lean_inc(v_toPure_2609_);
    v___f_2610_ = l_Lake_collectArgs___redArg___closed__0;
    leanh::lean_inc_ref(v_args_2605_);
    leanh::lean_inc(v_option_2604_);
    leanh::lean_inc_ref(v_inst_2603_);
    leanh::lean_inc_ref(v_inst_2602_);
    v___f_2611_ = leanh::lean_alloc_closure(
        l_Lake_collectArgs___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    leanh::lean_closure_set(v___f_2611_, 0, v_inst_2602_);
    leanh::lean_closure_set(v___f_2611_, 1, v_inst_2603_);
    leanh::lean_closure_set(v___f_2611_, 2, v_option_2604_);
    leanh::lean_closure_set(v___f_2611_, 3, v_args_2605_);
    leanh::lean_inc(v_modifyGet_2608_);
    v___x_2612_ =
        leanh::lean_apply_2(v_modifyGet_2608_, leanh::lean_box(0), v___f_2610_);
    v___f_2613_ = leanh::lean_alloc_closure(
        l_Lake_collectArgs___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_2613_, 0, v_args_2605_);
    leanh::lean_closure_set(v___f_2613_, 1, v_inst_2602_);
    leanh::lean_closure_set(v___f_2613_, 2, v_inst_2603_);
    leanh::lean_closure_set(v___f_2613_, 3, v_option_2604_);
    leanh::lean_closure_set(v___f_2613_, 4, v_toBind_2607_);
    leanh::lean_closure_set(v___f_2613_, 5, v___f_2611_);
    leanh::lean_closure_set(v___f_2613_, 6, v_toPure_2609_);
    v___x_2614_ = leanh::lean_apply_4(
        v_toBind_2607_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2612_,
        v___f_2613_,
    );
    return v___x_2614_;
}
pub unsafe fn l_Lake_collectArgs___redArg___lam__1(
    mut v_inst_2615_: *mut leanh::LeanObject,
    mut v_inst_2616_: *mut leanh::LeanObject,
    mut v_option_2617_: *mut leanh::LeanObject,
    mut v_args_2618_: *mut leanh::LeanObject,
    mut v_____r_2619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2620_ =
        l_Lake_collectArgs___redArg(v_inst_2615_, v_inst_2616_, v_option_2617_, v_args_2618_);
    return v___x_2620_;
}
pub unsafe fn l_Lake_collectArgs(
    mut v_m_2621_: *mut leanh::LeanObject,
    mut v_inst_2622_: *mut leanh::LeanObject,
    mut v_inst_2623_: *mut leanh::LeanObject,
    mut v_option_2624_: *mut leanh::LeanObject,
    mut v_args_2625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2626_ =
        l_Lake_collectArgs___redArg(v_inst_2622_, v_inst_2623_, v_option_2624_, v_args_2625_);
    return v___x_2626_;
}
pub unsafe fn l_Lake_processOptions___redArg___lam__0(
    mut v_inst_2627_: *mut leanh::LeanObject,
    mut v_____do__lift_2628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_set_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_set_2629_ = leanh::lean_ctor_get(v_inst_2627_, 1);
    leanh::lean_inc(v_set_2629_);
    leanh::lean_dec_ref(v_inst_2627_);
    v___x_2630_ = lean_array_to_list(v_____do__lift_2628_);
    v___x_2631_ = leanh::lean_apply_1(v_set_2629_, v___x_2630_);
    return v___x_2631_;
}
pub unsafe fn l_Lake_processOptions___redArg(
    mut v_inst_2634_: *mut leanh::LeanObject,
    mut v_inst_2635_: *mut leanh::LeanObject,
    mut v_handle_2636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2637_ = leanh::lean_ctor_get(v_inst_2634_, 1);
    leanh::lean_inc(v_toBind_2637_);
    leanh::lean_inc_ref(v_inst_2635_);
    v___f_2638_ = leanh::lean_alloc_closure(
        l_Lake_processOptions___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2638_, 0, v_inst_2635_);
    v___x_2639_ = l_Lake_processOptions___redArg___closed__0;
    v___x_2640_ =
        l_Lake_collectArgs___redArg(v_inst_2634_, v_inst_2635_, v_handle_2636_, v___x_2639_);
    v___x_2641_ = leanh::lean_apply_4(
        v_toBind_2637_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2640_,
        v___f_2638_,
    );
    return v___x_2641_;
}
pub unsafe fn l_Lake_processOptions(
    mut v_m_2642_: *mut leanh::LeanObject,
    mut v_inst_2643_: *mut leanh::LeanObject,
    mut v_inst_2644_: *mut leanh::LeanObject,
    mut v_handle_2645_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toBind_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2646_ = leanh::lean_ctor_get(v_inst_2643_, 1);
    leanh::lean_inc(v_toBind_2646_);
    leanh::lean_inc_ref(v_inst_2644_);
    v___f_2647_ = leanh::lean_alloc_closure(
        l_Lake_processOptions___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2647_, 0, v_inst_2644_);
    v___x_2648_ = l_Lake_processOptions___redArg___closed__0;
    v___x_2649_ =
        l_Lake_collectArgs___redArg(v_inst_2643_, v_inst_2644_, v_handle_2645_, v___x_2648_);
    v___x_2650_ = leanh::lean_apply_4(
        v_toBind_2646_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2649_,
        v___f_2647_,
    );
    return v___x_2650_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Cli(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Cli(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Cli(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Cli(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Cli(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Cli(builtin);
}