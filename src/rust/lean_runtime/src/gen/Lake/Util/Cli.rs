// Lean compiler output
// Module: Lake.Util.Cli
// Imports: Init.Data.String.TakeDrop Init.Data.String.Search Init.Data.String.Length
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
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_at_end, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_string_utf8_byte_size, lean_uint32_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_box_uint32, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox_uint32, lean_unsigned_to_nat,
};
pub static l_Lake_ArgsT_run_x27___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_ArgsT_run_x27___redArg___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ArgsT_run_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ArgsT_run_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_takeArg_x3f___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_takeArg_x3f___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_takeArg_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_takeArg_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_takeArgs___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_takeArgs___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_takeArgs___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_takeArgs___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_shortOptionWithSpace___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Char_isWhitespace___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_shortOptionWithSpace___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_shortOptionWithSpace___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lake_shortOptionWithSpace___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lake_shortOptionWithSpace___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lake_collectArgs___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_collectArgs___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_collectArgs___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_collectArgs___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_processOptions___redArg___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lake_processOptions___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_processOptions___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_ArgList_mk(mut v_args_1326_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_args_1326_);
    return v_args_1326_;
}
pub unsafe fn l_Lake_ArgList_mk___boxed(mut v_args_1327_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1328_: *mut LeanObject = core::ptr::null_mut();
    v_res_1328_ = l_Lake_ArgList_mk(v_args_1327_);
    lean_dec(v_args_1327_);
    return v_res_1328_;
}
pub unsafe fn l_Lake_ArgsT_run___redArg(
    mut v_args_1329_: *mut LeanObject,
    mut v_self_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    v___x_1331_ = lean_apply_1(v_self_1330_, v_args_1329_);
    return v___x_1331_;
}
pub unsafe fn l_Lake_ArgsT_run(
    mut v_m_1332_: *mut LeanObject,
    mut v_00_u03b1_1333_: *mut LeanObject,
    mut v_args_1334_: *mut LeanObject,
    mut v_self_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    v___x_1336_ = lean_apply_1(v_self_1335_, v_args_1334_);
    return v___x_1336_;
}
pub unsafe fn l_Lake_ArgsT_run_x27___redArg___lam__0(
    mut v_x_1337_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1338_: *mut LeanObject = core::ptr::null_mut();
    v_fst_1338_ = lean_ctor_get(v_x_1337_, 0);
    lean_inc(v_fst_1338_);
    return v_fst_1338_;
}
pub unsafe fn l_Lake_ArgsT_run_x27___redArg___lam__0___boxed(
    mut v_x_1339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1340_: *mut LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lake_ArgsT_run_x27___redArg___lam__0(v_x_1339_);
    lean_dec_ref(v_x_1339_);
    return v_res_1340_;
}
pub unsafe fn l_Lake_ArgsT_run_x27___redArg(
    mut v_inst_1342_: *mut LeanObject,
    mut v_args_1343_: *mut LeanObject,
    mut v_self_1344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    v_map_1345_ = lean_ctor_get(v_inst_1342_, 0);
    lean_inc(v_map_1345_);
    lean_dec_ref(v_inst_1342_);
    v___f_1346_ = l_Lake_ArgsT_run_x27___redArg___closed__0;
    v___x_1347_ = lean_apply_1(v_self_1344_, v_args_1343_);
    v___x_1348_ = lean_apply_4(
        v_map_1345_,
        lean_box(0),
        lean_box(0),
        v___f_1346_,
        v___x_1347_,
    );
    return v___x_1348_;
}
pub unsafe fn l_Lake_ArgsT_run_x27(
    mut v_m_1349_: *mut LeanObject,
    mut v_00_u03b1_1350_: *mut LeanObject,
    mut v_inst_1351_: *mut LeanObject,
    mut v_args_1352_: *mut LeanObject,
    mut v_self_1353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    v_map_1354_ = lean_ctor_get(v_inst_1351_, 0);
    lean_inc(v_map_1354_);
    lean_dec_ref(v_inst_1351_);
    v___f_1355_ = l_Lake_ArgsT_run_x27___redArg___closed__0;
    v___x_1356_ = lean_apply_1(v_self_1353_, v_args_1352_);
    v___x_1357_ = lean_apply_4(
        v_map_1354_,
        lean_box(0),
        lean_box(0),
        v___f_1355_,
        v___x_1356_,
    );
    return v___x_1357_;
}
pub unsafe fn l_Lake_getArgs___redArg(mut v_inst_1358_: *mut LeanObject) -> *mut LeanObject {
    let mut v_get_1359_: *mut LeanObject = core::ptr::null_mut();
    v_get_1359_ = lean_ctor_get(v_inst_1358_, 0);
    lean_inc(v_get_1359_);
    return v_get_1359_;
}
pub unsafe fn l_Lake_getArgs___redArg___boxed(
    mut v_inst_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1361_: *mut LeanObject = core::ptr::null_mut();
    v_res_1361_ = l_Lake_getArgs___redArg(v_inst_1360_);
    lean_dec_ref(v_inst_1360_);
    return v_res_1361_;
}
pub unsafe fn l_Lake_getArgs(
    mut v_m_1362_: *mut LeanObject,
    mut v_inst_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_get_1364_: *mut LeanObject = core::ptr::null_mut();
    v_get_1364_ = lean_ctor_get(v_inst_1363_, 0);
    lean_inc(v_get_1364_);
    return v_get_1364_;
}
pub unsafe fn l_Lake_getArgs___boxed(
    mut v_m_1365_: *mut LeanObject,
    mut v_inst_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1367_: *mut LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Lake_getArgs(v_m_1365_, v_inst_1366_);
    lean_dec_ref(v_inst_1366_);
    return v_res_1367_;
}
pub unsafe fn l_Lake_setArgs___redArg(
    mut v_inst_1368_: *mut LeanObject,
    mut v_args_1369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_set_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    v_set_1370_ = lean_ctor_get(v_inst_1368_, 1);
    lean_inc(v_set_1370_);
    lean_dec_ref(v_inst_1368_);
    v___x_1371_ = lean_apply_1(v_set_1370_, v_args_1369_);
    return v___x_1371_;
}
pub unsafe fn l_Lake_setArgs(
    mut v_m_1372_: *mut LeanObject,
    mut v_inst_1373_: *mut LeanObject,
    mut v_args_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_set_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v_set_1375_ = lean_ctor_get(v_inst_1373_, 1);
    lean_inc(v_set_1375_);
    lean_dec_ref(v_inst_1373_);
    v___x_1376_ = lean_apply_1(v_set_1375_, v_args_1374_);
    return v___x_1376_;
}
pub unsafe fn l_Lake_takeArg_x3f___redArg___lam__0(
    mut v_x_1377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1384_: u8 = 0;
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1389_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1377_) == 0 {
                    v___x_1378_ = lean_box(0);
                    v___x_1379_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1379_, 0, v___x_1378_);
                    lean_ctor_set(v___x_1379_, 1, v_x_1377_);
                    return v___x_1379_;
                } else {
                    v_head_1380_ = lean_ctor_get(v_x_1377_, 0);
                    v_tail_1381_ = lean_ctor_get(v_x_1377_, 1);
                    v_isSharedCheck_1389_ = (!lean_is_exclusive(v_x_1377_)) as u8;
                    if v_isSharedCheck_1389_ == 0 {
                        v___x_1383_ = v_x_1377_;
                        v_isShared_1384_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1381_);
                        lean_inc(v_head_1380_);
                        lean_dec(v_x_1377_);
                        v___x_1383_ = lean_box(0);
                        v_isShared_1384_ = v_isSharedCheck_1389_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1385_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1385_, 0, v_head_1380_);
                if v_isShared_1384_ == 0 {
                    lean_ctor_set_tag(v___x_1383_, 0);
                    lean_ctor_set(v___x_1383_, 0, v___x_1385_);
                    v___x_1387_ = v___x_1383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1388_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1388_, 0, v___x_1385_);
                    lean_ctor_set(v_reuseFailAlloc_1388_, 1, v_tail_1381_);
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
pub unsafe fn l_Lake_takeArg_x3f___redArg(mut v_inst_1391_: *mut LeanObject) -> *mut LeanObject {
    let mut v_modifyGet_1392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_1392_ = lean_ctor_get(v_inst_1391_, 2);
    lean_inc(v_modifyGet_1392_);
    lean_dec_ref(v_inst_1391_);
    v___f_1393_ = l_Lake_takeArg_x3f___redArg___closed__0;
    v___x_1394_ = lean_apply_2(v_modifyGet_1392_, lean_box(0), v___f_1393_);
    return v___x_1394_;
}
pub unsafe fn l_Lake_takeArg_x3f(
    mut v_m_1395_: *mut LeanObject,
    mut v_inst_1396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_1397_ = lean_ctor_get(v_inst_1396_, 2);
    lean_inc(v_modifyGet_1397_);
    lean_dec_ref(v_inst_1396_);
    v___f_1398_ = l_Lake_takeArg_x3f___redArg___closed__0;
    v___x_1399_ = lean_apply_2(v_modifyGet_1397_, lean_box(0), v___f_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lake_takeArgD___redArg___lam__0(
    mut v_default_1400_: *mut LeanObject,
    mut v_x_1401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1407_: u8 = 0;
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1411_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1401_) == 0 {
                    v___x_1402_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1402_, 0, v_default_1400_);
                    lean_ctor_set(v___x_1402_, 1, v_x_1401_);
                    return v___x_1402_;
                } else {
                    lean_dec_ref(v_default_1400_);
                    v_head_1403_ = lean_ctor_get(v_x_1401_, 0);
                    v_tail_1404_ = lean_ctor_get(v_x_1401_, 1);
                    v_isSharedCheck_1411_ = (!lean_is_exclusive(v_x_1401_)) as u8;
                    if v_isSharedCheck_1411_ == 0 {
                        v___x_1406_ = v_x_1401_;
                        v_isShared_1407_ = v_isSharedCheck_1411_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1404_);
                        lean_inc(v_head_1403_);
                        lean_dec(v_x_1401_);
                        v___x_1406_ = lean_box(0);
                        v_isShared_1407_ = v_isSharedCheck_1411_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1407_ == 0 {
                    lean_ctor_set_tag(v___x_1406_, 0);
                    v___x_1409_ = v___x_1406_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_head_1403_);
                    lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_tail_1404_);
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
    mut v_inst_1412_: *mut LeanObject,
    mut v_default_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_1414_ = lean_ctor_get(v_inst_1412_, 2);
    lean_inc(v_modifyGet_1414_);
    lean_dec_ref(v_inst_1412_);
    v___f_1415_ = lean_alloc_closure(
        l_Lake_takeArgD___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1415_, 0, v_default_1413_);
    v___x_1416_ = lean_apply_2(v_modifyGet_1414_, lean_box(0), v___f_1415_);
    return v___x_1416_;
}
pub unsafe fn l_Lake_takeArgD(
    mut v_m_1417_: *mut LeanObject,
    mut v_inst_1418_: *mut LeanObject,
    mut v_default_1419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_1420_ = lean_ctor_get(v_inst_1418_, 2);
    lean_inc(v_modifyGet_1420_);
    lean_dec_ref(v_inst_1418_);
    v___f_1421_ = lean_alloc_closure(
        l_Lake_takeArgD___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1421_, 0, v_default_1419_);
    v___x_1422_ = lean_apply_2(v_modifyGet_1420_, lean_box(0), v___f_1421_);
    return v___x_1422_;
}
pub unsafe fn l_Lake_takeArgs___redArg___lam__0(
    mut v_args_1423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    v___x_1424_ = lean_box(0);
    v___x_1425_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1425_, 0, v_args_1423_);
    lean_ctor_set(v___x_1425_, 1, v___x_1424_);
    return v___x_1425_;
}
pub unsafe fn l_Lake_takeArgs___redArg(mut v_inst_1427_: *mut LeanObject) -> *mut LeanObject {
    let mut v_modifyGet_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_1428_ = lean_ctor_get(v_inst_1427_, 2);
    lean_inc(v_modifyGet_1428_);
    lean_dec_ref(v_inst_1427_);
    v___f_1429_ = l_Lake_takeArgs___redArg___closed__0;
    v___x_1430_ = lean_apply_2(v_modifyGet_1428_, lean_box(0), v___f_1429_);
    return v___x_1430_;
}
pub unsafe fn l_Lake_takeArgs(
    mut v_m_1431_: *mut LeanObject,
    mut v_inst_1432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_1433_ = lean_ctor_get(v_inst_1432_, 2);
    lean_inc(v_modifyGet_1433_);
    lean_dec_ref(v_inst_1432_);
    v___f_1434_ = l_Lake_takeArgs___redArg___closed__0;
    v___x_1435_ = lean_apply_2(v_modifyGet_1433_, lean_box(0), v___f_1434_);
    return v___x_1435_;
}
pub unsafe fn l_Lake_consArg___redArg___lam__0(
    mut v_arg_1436_: *mut LeanObject,
    mut v_s_1437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    v___x_1438_ = lean_box(0);
    v___x_1439_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1439_, 0, v_arg_1436_);
    lean_ctor_set(v___x_1439_, 1, v_s_1437_);
    v___x_1440_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1440_, 0, v___x_1438_);
    lean_ctor_set(v___x_1440_, 1, v___x_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Lake_consArg___redArg(
    mut v_inst_1441_: *mut LeanObject,
    mut v_arg_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_1443_ = lean_ctor_get(v_inst_1441_, 2);
    lean_inc(v_modifyGet_1443_);
    lean_dec_ref(v_inst_1441_);
    v___f_1444_ = lean_alloc_closure(
        l_Lake_consArg___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1444_, 0, v_arg_1442_);
    v___x_1445_ = lean_apply_2(v_modifyGet_1443_, lean_box(0), v___f_1444_);
    return v___x_1445_;
}
pub unsafe fn l_Lake_consArg(
    mut v_m_1446_: *mut LeanObject,
    mut v_inst_1447_: *mut LeanObject,
    mut v_arg_1448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modifyGet_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
    v_modifyGet_1449_ = lean_ctor_get(v_inst_1447_, 2);
    lean_inc(v_modifyGet_1449_);
    lean_dec_ref(v_inst_1447_);
    v___f_1450_ = lean_alloc_closure(
        l_Lake_consArg___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1450_, 0, v_arg_1448_);
    v___x_1451_ = lean_apply_2(v_modifyGet_1449_, lean_box(0), v___f_1450_);
    return v___x_1451_;
}
pub unsafe fn l_Lake_shortOptionWithEq___redArg___lam__0(
    mut v_opt_1452_: *mut LeanObject,
    mut v_handle_1453_: *mut LeanObject,
    mut v_____r_1454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: u32 = 0;
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    v___x_1455_ = lean_unsigned_to_nat(1);
    v___x_1456_ = lean_string_utf8_get(v_opt_1452_, v___x_1455_);
    v___x_1457_ = lean_box_uint32(v___x_1456_);
    v___x_1458_ = lean_apply_1(v_handle_1453_, v___x_1457_);
    return v___x_1458_;
}
pub unsafe fn l_Lake_shortOptionWithEq___redArg___lam__0___boxed(
    mut v_opt_1459_: *mut LeanObject,
    mut v_handle_1460_: *mut LeanObject,
    mut v_____r_1461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1462_: *mut LeanObject = core::ptr::null_mut();
    v_res_1462_ =
        l_Lake_shortOptionWithEq___redArg___lam__0(v_opt_1459_, v_handle_1460_, v_____r_1461_);
    lean_dec_ref(v_opt_1459_);
    return v_res_1462_;
}
pub unsafe fn l_Lake_shortOptionWithEq___redArg___lam__1(
    mut v___x_1463_: *mut LeanObject,
    mut v_s_1464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    v___x_1465_ = lean_box(0);
    v___x_1466_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1466_, 0, v___x_1463_);
    lean_ctor_set(v___x_1466_, 1, v_s_1464_);
    v___x_1467_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1467_, 0, v___x_1465_);
    lean_ctor_set(v___x_1467_, 1, v___x_1466_);
    return v___x_1467_;
}
pub unsafe fn l_Lake_shortOptionWithEq___redArg(
    mut v_inst_1468_: *mut LeanObject,
    mut v_inst_1469_: *mut LeanObject,
    mut v_handle_1470_: *mut LeanObject,
    mut v_opt_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1477_: u8 = 0;
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1489_: u8 = 0;
    let mut v_unused_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1472_ = lean_ctor_get(v_inst_1468_, 1);
                lean_inc(v_toBind_1472_);
                lean_dec_ref(v_inst_1468_);
                v___x_1473_ = lean_string_utf8_byte_size(v_opt_1471_);
                v_modifyGet_1474_ = lean_ctor_get(v_inst_1469_, 2);
                v_isSharedCheck_1489_ = (!lean_is_exclusive(v_inst_1469_)) as u8;
                if v_isSharedCheck_1489_ == 0 {
                    v_unused_1490_ = lean_ctor_get(v_inst_1469_, 1);
                    lean_dec(v_unused_1490_);
                    v_unused_1491_ = lean_ctor_get(v_inst_1469_, 0);
                    lean_dec(v_unused_1491_);
                    v___x_1476_ = v_inst_1469_;
                    v_isShared_1477_ = v_isSharedCheck_1489_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyGet_1474_);
                    lean_dec(v_inst_1469_);
                    v___x_1476_ = lean_box(0);
                    v_isShared_1477_ = v_isSharedCheck_1489_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1478_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_opt_1471_);
                if v_isShared_1477_ == 0 {
                    lean_ctor_set(v___x_1476_, 2, v___x_1473_);
                    lean_ctor_set(v___x_1476_, 1, v___x_1478_);
                    lean_ctor_set(v___x_1476_, 0, v_opt_1471_);
                    v___x_1480_ = v___x_1476_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_opt_1471_);
                    lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1478_);
                    lean_ctor_set(v_reuseFailAlloc_1488_, 2, v___x_1473_);
                    v___x_1480_ = v_reuseFailAlloc_1488_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_opt_1471_);
                v___f_1481_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1481_, 0, v_opt_1471_);
                lean_closure_set(v___f_1481_, 1, v_handle_1470_);
                v___x_1482_ = lean_unsigned_to_nat(3);
                v___x_1483_ = l_String_Slice_Pos_nextn(v___x_1480_, v___x_1478_, v___x_1482_);
                lean_dec_ref(v___x_1480_);
                v___x_1484_ = lean_string_utf8_extract(v_opt_1471_, v___x_1483_, v___x_1473_);
                lean_dec(v___x_1483_);
                lean_dec_ref(v_opt_1471_);
                v___f_1485_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1485_, 0, v___x_1484_);
                v___x_1486_ = lean_apply_2(v_modifyGet_1474_, lean_box(0), v___f_1485_);
                v___x_1487_ = lean_apply_4(
                    v_toBind_1472_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_1492_: *mut LeanObject,
    mut v_inst_1493_: *mut LeanObject,
    mut v_inst_1494_: *mut LeanObject,
    mut v_00_u03b1_1495_: *mut LeanObject,
    mut v_handle_1496_: *mut LeanObject,
    mut v_opt_1497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1503_: u8 = 0;
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1515_: u8 = 0;
    let mut v_unused_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1498_ = lean_ctor_get(v_inst_1493_, 1);
                lean_inc(v_toBind_1498_);
                lean_dec_ref(v_inst_1493_);
                v___x_1499_ = lean_string_utf8_byte_size(v_opt_1497_);
                v_modifyGet_1500_ = lean_ctor_get(v_inst_1494_, 2);
                v_isSharedCheck_1515_ = (!lean_is_exclusive(v_inst_1494_)) as u8;
                if v_isSharedCheck_1515_ == 0 {
                    v_unused_1516_ = lean_ctor_get(v_inst_1494_, 1);
                    lean_dec(v_unused_1516_);
                    v_unused_1517_ = lean_ctor_get(v_inst_1494_, 0);
                    lean_dec(v_unused_1517_);
                    v___x_1502_ = v_inst_1494_;
                    v_isShared_1503_ = v_isSharedCheck_1515_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyGet_1500_);
                    lean_dec(v_inst_1494_);
                    v___x_1502_ = lean_box(0);
                    v_isShared_1503_ = v_isSharedCheck_1515_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1504_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_opt_1497_);
                if v_isShared_1503_ == 0 {
                    lean_ctor_set(v___x_1502_, 2, v___x_1499_);
                    lean_ctor_set(v___x_1502_, 1, v___x_1504_);
                    lean_ctor_set(v___x_1502_, 0, v_opt_1497_);
                    v___x_1506_ = v___x_1502_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1514_, 0, v_opt_1497_);
                    lean_ctor_set(v_reuseFailAlloc_1514_, 1, v___x_1504_);
                    lean_ctor_set(v_reuseFailAlloc_1514_, 2, v___x_1499_);
                    v___x_1506_ = v_reuseFailAlloc_1514_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_opt_1497_);
                v___f_1507_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1507_, 0, v_opt_1497_);
                lean_closure_set(v___f_1507_, 1, v_handle_1496_);
                v___x_1508_ = lean_unsigned_to_nat(3);
                v___x_1509_ = l_String_Slice_Pos_nextn(v___x_1506_, v___x_1504_, v___x_1508_);
                lean_dec_ref(v___x_1506_);
                v___x_1510_ = lean_string_utf8_extract(v_opt_1497_, v___x_1509_, v___x_1499_);
                lean_dec(v___x_1509_);
                lean_dec_ref(v_opt_1497_);
                v___f_1511_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1511_, 0, v___x_1510_);
                v___x_1512_ = lean_apply_2(v_modifyGet_1500_, lean_box(0), v___f_1511_);
                v___x_1513_ = lean_apply_4(
                    v_toBind_1498_,
                    lean_box(0),
                    lean_box(0),
                    v___x_1512_,
                    v___f_1507_,
                );
                return v___x_1513_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_shortOptionWithSpace___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    v___x_1519_ = l_Lake_shortOptionWithSpace___redArg___closed__0;
    v___x_1520_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1519_);
    return v___x_1520_;
}
pub unsafe fn l_Lake_shortOptionWithSpace___redArg(
    mut v_inst_1521_: *mut LeanObject,
    mut v_inst_1522_: *mut LeanObject,
    mut v_handle_1523_: *mut LeanObject,
    mut v_opt_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1533_: u8 = 0;
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_unused_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1525_ = lean_ctor_get(v_inst_1521_, 1);
                lean_inc(v_toBind_1525_);
                lean_dec_ref(v_inst_1521_);
                v___x_1526_ = lean_unsigned_to_nat(0);
                v___x_1527_ = lean_string_utf8_byte_size(v_opt_1524_);
                lean_inc_ref(v_opt_1524_);
                v___x_1528_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1528_, 0, v_opt_1524_);
                lean_ctor_set(v___x_1528_, 1, v___x_1526_);
                lean_ctor_set(v___x_1528_, 2, v___x_1527_);
                v___x_1529_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_shortOptionWithSpace___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_shortOptionWithSpace___redArg___closed__1_once),
                    _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                );
                v_modifyGet_1530_ = lean_ctor_get(v_inst_1522_, 2);
                v_isSharedCheck_1546_ = (!lean_is_exclusive(v_inst_1522_)) as u8;
                if v_isSharedCheck_1546_ == 0 {
                    v_unused_1547_ = lean_ctor_get(v_inst_1522_, 1);
                    lean_dec(v_unused_1547_);
                    v_unused_1548_ = lean_ctor_get(v_inst_1522_, 0);
                    lean_dec(v_unused_1548_);
                    v___x_1532_ = v_inst_1522_;
                    v_isShared_1533_ = v_isSharedCheck_1546_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyGet_1530_);
                    lean_dec(v_inst_1522_);
                    v___x_1532_ = lean_box(0);
                    v_isShared_1533_ = v_isSharedCheck_1546_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1534_ = lean_unsigned_to_nat(2);
                v___x_1535_ = l_String_Slice_Pos_nextn(v___x_1528_, v___x_1526_, v___x_1534_);
                lean_dec_ref_known(v___x_1528_, 3);
                lean_inc_ref_n(v_opt_1524_, 2);
                v___f_1536_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1536_, 0, v_opt_1524_);
                lean_closure_set(v___f_1536_, 1, v_handle_1523_);
                lean_inc(v___x_1535_);
                if v_isShared_1533_ == 0 {
                    lean_ctor_set(v___x_1532_, 2, v___x_1527_);
                    lean_ctor_set(v___x_1532_, 1, v___x_1535_);
                    lean_ctor_set(v___x_1532_, 0, v_opt_1524_);
                    v___x_1538_ = v___x_1532_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1545_, 0, v_opt_1524_);
                    lean_ctor_set(v_reuseFailAlloc_1545_, 1, v___x_1535_);
                    lean_ctor_set(v_reuseFailAlloc_1545_, 2, v___x_1527_);
                    v___x_1538_ = v_reuseFailAlloc_1545_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1539_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_1538_, v___x_1526_, v___x_1529_);
                lean_dec_ref(v___x_1538_);
                v___x_1540_ = lean_nat_add(v___x_1535_, v___x_1539_);
                lean_dec(v___x_1539_);
                lean_dec(v___x_1535_);
                v___x_1541_ = lean_string_utf8_extract(v_opt_1524_, v___x_1540_, v___x_1527_);
                lean_dec(v___x_1540_);
                lean_dec_ref(v_opt_1524_);
                v___f_1542_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1542_, 0, v___x_1541_);
                v___x_1543_ = lean_apply_2(v_modifyGet_1530_, lean_box(0), v___f_1542_);
                v___x_1544_ = lean_apply_4(
                    v_toBind_1525_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_1549_: *mut LeanObject,
    mut v_inst_1550_: *mut LeanObject,
    mut v_inst_1551_: *mut LeanObject,
    mut v_00_u03b1_1552_: *mut LeanObject,
    mut v_handle_1553_: *mut LeanObject,
    mut v_opt_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1563_: u8 = 0;
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1576_: u8 = 0;
    let mut v_unused_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1555_ = lean_ctor_get(v_inst_1550_, 1);
                lean_inc(v_toBind_1555_);
                lean_dec_ref(v_inst_1550_);
                v___x_1556_ = lean_unsigned_to_nat(0);
                v___x_1557_ = lean_string_utf8_byte_size(v_opt_1554_);
                lean_inc_ref(v_opt_1554_);
                v___x_1558_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1558_, 0, v_opt_1554_);
                lean_ctor_set(v___x_1558_, 1, v___x_1556_);
                lean_ctor_set(v___x_1558_, 2, v___x_1557_);
                v___x_1559_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lake_shortOptionWithSpace___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Lake_shortOptionWithSpace___redArg___closed__1_once),
                    _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                );
                v_modifyGet_1560_ = lean_ctor_get(v_inst_1551_, 2);
                v_isSharedCheck_1576_ = (!lean_is_exclusive(v_inst_1551_)) as u8;
                if v_isSharedCheck_1576_ == 0 {
                    v_unused_1577_ = lean_ctor_get(v_inst_1551_, 1);
                    lean_dec(v_unused_1577_);
                    v_unused_1578_ = lean_ctor_get(v_inst_1551_, 0);
                    lean_dec(v_unused_1578_);
                    v___x_1562_ = v_inst_1551_;
                    v_isShared_1563_ = v_isSharedCheck_1576_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyGet_1560_);
                    lean_dec(v_inst_1551_);
                    v___x_1562_ = lean_box(0);
                    v_isShared_1563_ = v_isSharedCheck_1576_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1564_ = lean_unsigned_to_nat(2);
                v___x_1565_ = l_String_Slice_Pos_nextn(v___x_1558_, v___x_1556_, v___x_1564_);
                lean_dec_ref_known(v___x_1558_, 3);
                lean_inc_ref_n(v_opt_1554_, 2);
                v___f_1566_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1566_, 0, v_opt_1554_);
                lean_closure_set(v___f_1566_, 1, v_handle_1553_);
                lean_inc(v___x_1565_);
                if v_isShared_1563_ == 0 {
                    lean_ctor_set(v___x_1562_, 2, v___x_1557_);
                    lean_ctor_set(v___x_1562_, 1, v___x_1565_);
                    lean_ctor_set(v___x_1562_, 0, v_opt_1554_);
                    v___x_1568_ = v___x_1562_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_opt_1554_);
                    lean_ctor_set(v_reuseFailAlloc_1575_, 1, v___x_1565_);
                    lean_ctor_set(v_reuseFailAlloc_1575_, 2, v___x_1557_);
                    v___x_1568_ = v_reuseFailAlloc_1575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1569_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_1568_, v___x_1556_, v___x_1559_);
                lean_dec_ref(v___x_1568_);
                v___x_1570_ = lean_nat_add(v___x_1565_, v___x_1569_);
                lean_dec(v___x_1569_);
                lean_dec(v___x_1565_);
                v___x_1571_ = lean_string_utf8_extract(v_opt_1554_, v___x_1570_, v___x_1557_);
                lean_dec(v___x_1570_);
                lean_dec_ref(v_opt_1554_);
                v___f_1572_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1572_, 0, v___x_1571_);
                v___x_1573_ = lean_apply_2(v_modifyGet_1560_, lean_box(0), v___f_1572_);
                v___x_1574_ = lean_apply_4(
                    v_toBind_1555_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_1579_: *mut LeanObject,
    mut v_inst_1580_: *mut LeanObject,
    mut v_handle_1581_: *mut LeanObject,
    mut v_opt_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1600_: u8 = 0;
    let mut v_unused_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1583_ = lean_ctor_get(v_inst_1579_, 1);
                lean_inc(v_toBind_1583_);
                lean_dec_ref(v_inst_1579_);
                v___x_1584_ = lean_string_utf8_byte_size(v_opt_1582_);
                v_modifyGet_1585_ = lean_ctor_get(v_inst_1580_, 2);
                v_isSharedCheck_1600_ = (!lean_is_exclusive(v_inst_1580_)) as u8;
                if v_isSharedCheck_1600_ == 0 {
                    v_unused_1601_ = lean_ctor_get(v_inst_1580_, 1);
                    lean_dec(v_unused_1601_);
                    v_unused_1602_ = lean_ctor_get(v_inst_1580_, 0);
                    lean_dec(v_unused_1602_);
                    v___x_1587_ = v_inst_1580_;
                    v_isShared_1588_ = v_isSharedCheck_1600_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyGet_1585_);
                    lean_dec(v_inst_1580_);
                    v___x_1587_ = lean_box(0);
                    v_isShared_1588_ = v_isSharedCheck_1600_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1589_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_opt_1582_);
                if v_isShared_1588_ == 0 {
                    lean_ctor_set(v___x_1587_, 2, v___x_1584_);
                    lean_ctor_set(v___x_1587_, 1, v___x_1589_);
                    lean_ctor_set(v___x_1587_, 0, v_opt_1582_);
                    v___x_1591_ = v___x_1587_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1599_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_opt_1582_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 1, v___x_1589_);
                    lean_ctor_set(v_reuseFailAlloc_1599_, 2, v___x_1584_);
                    v___x_1591_ = v_reuseFailAlloc_1599_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_opt_1582_);
                v___f_1592_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1592_, 0, v_opt_1582_);
                lean_closure_set(v___f_1592_, 1, v_handle_1581_);
                v___x_1593_ = lean_unsigned_to_nat(2);
                v___x_1594_ = l_String_Slice_Pos_nextn(v___x_1591_, v___x_1589_, v___x_1593_);
                lean_dec_ref(v___x_1591_);
                v___x_1595_ = lean_string_utf8_extract(v_opt_1582_, v___x_1594_, v___x_1584_);
                lean_dec(v___x_1594_);
                lean_dec_ref(v_opt_1582_);
                v___f_1596_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1596_, 0, v___x_1595_);
                v___x_1597_ = lean_apply_2(v_modifyGet_1585_, lean_box(0), v___f_1596_);
                v___x_1598_ = lean_apply_4(
                    v_toBind_1583_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_1603_: *mut LeanObject,
    mut v_inst_1604_: *mut LeanObject,
    mut v_inst_1605_: *mut LeanObject,
    mut v_00_u03b1_1606_: *mut LeanObject,
    mut v_handle_1607_: *mut LeanObject,
    mut v_opt_1608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1614_: u8 = 0;
    let mut v___x_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1626_: u8 = 0;
    let mut v_unused_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toBind_1609_ = lean_ctor_get(v_inst_1604_, 1);
                lean_inc(v_toBind_1609_);
                lean_dec_ref(v_inst_1604_);
                v___x_1610_ = lean_string_utf8_byte_size(v_opt_1608_);
                v_modifyGet_1611_ = lean_ctor_get(v_inst_1605_, 2);
                v_isSharedCheck_1626_ = (!lean_is_exclusive(v_inst_1605_)) as u8;
                if v_isSharedCheck_1626_ == 0 {
                    v_unused_1627_ = lean_ctor_get(v_inst_1605_, 1);
                    lean_dec(v_unused_1627_);
                    v_unused_1628_ = lean_ctor_get(v_inst_1605_, 0);
                    lean_dec(v_unused_1628_);
                    v___x_1613_ = v_inst_1605_;
                    v_isShared_1614_ = v_isSharedCheck_1626_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_modifyGet_1611_);
                    lean_dec(v_inst_1605_);
                    v___x_1613_ = lean_box(0);
                    v_isShared_1614_ = v_isSharedCheck_1626_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1615_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_opt_1608_);
                if v_isShared_1614_ == 0 {
                    lean_ctor_set(v___x_1613_, 2, v___x_1610_);
                    lean_ctor_set(v___x_1613_, 1, v___x_1615_);
                    lean_ctor_set(v___x_1613_, 0, v_opt_1608_);
                    v___x_1617_ = v___x_1613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_opt_1608_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 1, v___x_1615_);
                    lean_ctor_set(v_reuseFailAlloc_1625_, 2, v___x_1610_);
                    v___x_1617_ = v_reuseFailAlloc_1625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_opt_1608_);
                v___f_1618_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_1618_, 0, v_opt_1608_);
                lean_closure_set(v___f_1618_, 1, v_handle_1607_);
                v___x_1619_ = lean_unsigned_to_nat(2);
                v___x_1620_ = l_String_Slice_Pos_nextn(v___x_1617_, v___x_1615_, v___x_1619_);
                lean_dec_ref(v___x_1617_);
                v___x_1621_ = lean_string_utf8_extract(v_opt_1608_, v___x_1620_, v___x_1610_);
                lean_dec(v___x_1620_);
                lean_dec_ref(v_opt_1608_);
                v___f_1622_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_1622_, 0, v___x_1621_);
                v___x_1623_ = lean_apply_2(v_modifyGet_1611_, lean_box(0), v___f_1622_);
                v___x_1624_ = lean_apply_4(
                    v_toBind_1609_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_opt_1629_: *mut LeanObject,
    mut v_p_1630_: *mut LeanObject,
    mut v_inst_1631_: *mut LeanObject,
    mut v_handle_1632_: *mut LeanObject,
    mut v_____r_1633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1634_: *mut LeanObject = core::ptr::null_mut();
    v_res_1634_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(
        v_opt_1629_,
        v_p_1630_,
        v_inst_1631_,
        v_handle_1632_,
        v_____r_1633_,
    );
    lean_dec(v_p_1630_);
    return v_res_1634_;
}
pub unsafe fn l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(
    mut v_inst_1635_: *mut LeanObject,
    mut v_handle_1636_: *mut LeanObject,
    mut v_opt_1637_: *mut LeanObject,
    mut v_p_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1639_: u8 = 0;
    v___x_1639_ = lean_string_utf8_at_end(v_opt_1637_, v_p_1638_);
    if v___x_1639_ == 0 {
        let mut v_toBind_1640_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1641_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1642_: u32 = 0;
        let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_1640_ = lean_ctor_get(v_inst_1635_, 1);
        lean_inc(v_toBind_1640_);
        lean_inc(v_handle_1636_);
        lean_inc(v_p_1638_);
        lean_inc_ref(v_opt_1637_);
        v___f_1641_ = lean_alloc_closure(
            l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_1641_, 0, v_opt_1637_);
        lean_closure_set(v___f_1641_, 1, v_p_1638_);
        lean_closure_set(v___f_1641_, 2, v_inst_1635_);
        lean_closure_set(v___f_1641_, 3, v_handle_1636_);
        v___x_1642_ = lean_string_utf8_get_fast(v_opt_1637_, v_p_1638_);
        lean_dec(v_p_1638_);
        lean_dec_ref(v_opt_1637_);
        v___x_1643_ = lean_box_uint32(v___x_1642_);
        v___x_1644_ = lean_apply_1(v_handle_1636_, v___x_1643_);
        v___x_1645_ = lean_apply_4(
            v_toBind_1640_,
            lean_box(0),
            lean_box(0),
            v___x_1644_,
            v___f_1641_,
        );
        return v___x_1645_;
    } else {
        let mut v_toApplicative_1646_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_1647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_p_1638_);
        lean_dec_ref(v_opt_1637_);
        lean_dec(v_handle_1636_);
        v_toApplicative_1646_ = lean_ctor_get(v_inst_1635_, 0);
        lean_inc_ref(v_toApplicative_1646_);
        lean_dec_ref(v_inst_1635_);
        v_toPure_1647_ = lean_ctor_get(v_toApplicative_1646_, 1);
        lean_inc(v_toPure_1647_);
        lean_dec_ref(v_toApplicative_1646_);
        v___x_1648_ = lean_box(0);
        v___x_1649_ = lean_apply_2(v_toPure_1647_, lean_box(0), v___x_1648_);
        return v___x_1649_;
    }
}
pub unsafe fn l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg___lam__0(
    mut v_opt_1650_: *mut LeanObject,
    mut v_p_1651_: *mut LeanObject,
    mut v_inst_1652_: *mut LeanObject,
    mut v_handle_1653_: *mut LeanObject,
    mut v_____r_1654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_m_1657_: *mut LeanObject,
    mut v_inst_1658_: *mut LeanObject,
    mut v_handle_1659_: *mut LeanObject,
    mut v_opt_1660_: *mut LeanObject,
    mut v_p_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
    v___x_1662_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(
        v_inst_1658_,
        v_handle_1659_,
        v_opt_1660_,
        v_p_1661_,
    );
    return v___x_1662_;
}
pub unsafe fn l_Lake_multiShortOption___redArg(
    mut v_inst_1663_: *mut LeanObject,
    mut v_handle_1664_: *mut LeanObject,
    mut v_opt_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    v___x_1666_ = lean_unsigned_to_nat(1);
    v___x_1667_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(
        v_inst_1663_,
        v_handle_1664_,
        v_opt_1665_,
        v___x_1666_,
    );
    return v___x_1667_;
}
pub unsafe fn l_Lake_multiShortOption(
    mut v_m_1668_: *mut LeanObject,
    mut v_inst_1669_: *mut LeanObject,
    mut v_handle_1670_: *mut LeanObject,
    mut v_opt_1671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
    v___x_1672_ = lean_unsigned_to_nat(1);
    v___x_1673_ = l___private_Lake_Util_Cli_0__Lake_multiShortOption_loop___redArg(
        v_inst_1669_,
        v_handle_1670_,
        v_opt_1671_,
        v___x_1672_,
    );
    return v___x_1673_;
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg___lam__0(
    mut v_opt_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v_handle_1676_: *mut LeanObject,
    mut v_____r_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    v___x_1678_ = lean_unsigned_to_nat(0);
    v___x_1679_ = lean_string_utf8_extract(v_opt_1674_, v___x_1678_, v___y_1675_);
    v___x_1680_ = lean_apply_1(v_handle_1676_, v___x_1679_);
    return v___x_1680_;
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg___lam__0___boxed(
    mut v_opt_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
    mut v_handle_1683_: *mut LeanObject,
    mut v_____r_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1685_: *mut LeanObject = core::ptr::null_mut();
    v_res_1685_ = l_Lake_longOptionOrSpace___redArg___lam__0(
        v_opt_1681_,
        v___y_1682_,
        v_handle_1683_,
        v_____r_1684_,
    );
    lean_dec(v___y_1682_);
    lean_dec_ref(v_opt_1681_);
    return v_res_1685_;
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg___lam__2(
    mut v___x_1686_: *mut LeanObject,
    mut v_opt_1687_: *mut LeanObject,
    mut v___x_1688_: *mut LeanObject,
    mut v_it_1689_: *mut LeanObject,
    mut v_acc_1690_: *mut LeanObject,
    mut v_hP_1691_: *mut LeanObject,
    mut v_recur_1692_: *mut LeanObject,
) -> *mut LeanObject {
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
            let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
            v___x_1697_ = lean_string_utf8_next_fast(v_opt_1687_, v_it_1689_);
            lean_dec(v_it_1689_);
            v___x_1698_ = lean_apply_4(
                v_recur_1692_,
                v___x_1697_,
                v___x_1688_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1698_;
        } else {
            let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_recur_1692_);
            lean_dec(v___x_1688_);
            v___x_1699_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1699_, 0, v_it_1689_);
            return v___x_1699_;
        }
    } else {
        lean_dec_ref(v_recur_1692_);
        lean_dec(v_it_1689_);
        lean_dec(v___x_1688_);
        lean_inc(v_acc_1690_);
        return v_acc_1690_;
    }
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg___lam__2___boxed(
    mut v___x_1700_: *mut LeanObject,
    mut v_opt_1701_: *mut LeanObject,
    mut v___x_1702_: *mut LeanObject,
    mut v_it_1703_: *mut LeanObject,
    mut v_acc_1704_: *mut LeanObject,
    mut v_hP_1705_: *mut LeanObject,
    mut v_recur_1706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1707_: *mut LeanObject = core::ptr::null_mut();
    v_res_1707_ = l_Lake_longOptionOrSpace___redArg___lam__2(
        v___x_1700_,
        v_opt_1701_,
        v___x_1702_,
        v_it_1703_,
        v_acc_1704_,
        v_hP_1705_,
        v_recur_1706_,
    );
    lean_dec(v_acc_1704_);
    lean_dec_ref(v_opt_1701_);
    lean_dec(v___x_1700_);
    return v_res_1707_;
}
pub unsafe fn l_Lake_longOptionOrSpace___redArg(
    mut v_inst_1708_: *mut LeanObject,
    mut v_inst_1709_: *mut LeanObject,
    mut v_handle_1710_: *mut LeanObject,
    mut v_opt_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: u8 = 0;
    let mut v_toBind_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1725_ = lean_unsigned_to_nat(0);
                v___x_1726_ = lean_string_utf8_byte_size(v_opt_1711_);
                v___x_1727_ = lean_box(0);
                lean_inc_ref(v_opt_1711_);
                v___f_1728_ = lean_alloc_closure(
                    l_Lake_longOptionOrSpace___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_1728_, 0, v___x_1726_);
                lean_closure_set(v___f_1728_, 1, v_opt_1711_);
                lean_closure_set(v___f_1728_, 2, v___x_1727_);
                v___x_1729_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1728_,
                    v_searcher_1725_,
                    v___x_1727_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1729_) == 0 {
                    v___y_1713_ = v___x_1726_;
                    state = 1;
                    continue;
                } else {
                    v_val_1730_ = lean_ctor_get(v___x_1729_, 0);
                    lean_inc(v_val_1730_);
                    lean_dec_ref_known(v___x_1729_, 1);
                    v___y_1713_ = v_val_1730_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1714_ = lean_string_utf8_byte_size(v_opt_1711_);
                v___x_1715_ = lean_nat_dec_eq(v___y_1713_, v___x_1714_);
                if v___x_1715_ == 0 {
                    v_toBind_1716_ = lean_ctor_get(v_inst_1708_, 1);
                    lean_inc(v_toBind_1716_);
                    lean_dec_ref(v_inst_1708_);
                    v_modifyGet_1717_ = lean_ctor_get(v_inst_1709_, 2);
                    lean_inc(v_modifyGet_1717_);
                    lean_dec_ref(v_inst_1709_);
                    lean_inc(v___y_1713_);
                    lean_inc_ref(v_opt_1711_);
                    v___f_1718_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_1718_, 0, v_opt_1711_);
                    lean_closure_set(v___f_1718_, 1, v___y_1713_);
                    lean_closure_set(v___f_1718_, 2, v_handle_1710_);
                    v___x_1719_ = lean_string_utf8_next_fast(v_opt_1711_, v___y_1713_);
                    lean_dec(v___y_1713_);
                    v___x_1720_ = lean_string_utf8_extract(v_opt_1711_, v___x_1719_, v___x_1714_);
                    lean_dec_ref(v_opt_1711_);
                    v___f_1721_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1721_, 0, v___x_1720_);
                    v___x_1722_ = lean_apply_2(v_modifyGet_1717_, lean_box(0), v___f_1721_);
                    v___x_1723_ = lean_apply_4(
                        v_toBind_1716_,
                        lean_box(0),
                        lean_box(0),
                        v___x_1722_,
                        v___f_1718_,
                    );
                    return v___x_1723_;
                } else {
                    lean_dec(v___y_1713_);
                    lean_dec_ref(v_inst_1709_);
                    lean_dec_ref(v_inst_1708_);
                    v___x_1724_ = lean_apply_1(v_handle_1710_, v_opt_1711_);
                    return v___x_1724_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOptionOrSpace(
    mut v_m_1731_: *mut LeanObject,
    mut v_inst_1732_: *mut LeanObject,
    mut v_inst_1733_: *mut LeanObject,
    mut v_00_u03b1_1734_: *mut LeanObject,
    mut v_handle_1735_: *mut LeanObject,
    mut v_opt_1736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v_toBind_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1750_ = lean_unsigned_to_nat(0);
                v___x_1751_ = lean_string_utf8_byte_size(v_opt_1736_);
                v___x_1752_ = lean_box(0);
                lean_inc_ref(v_opt_1736_);
                v___f_1753_ = lean_alloc_closure(
                    l_Lake_longOptionOrSpace___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_1753_, 0, v___x_1751_);
                lean_closure_set(v___f_1753_, 1, v_opt_1736_);
                lean_closure_set(v___f_1753_, 2, v___x_1752_);
                v___x_1754_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1753_,
                    v_searcher_1750_,
                    v___x_1752_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1754_) == 0 {
                    v___y_1738_ = v___x_1751_;
                    state = 1;
                    continue;
                } else {
                    v_val_1755_ = lean_ctor_get(v___x_1754_, 0);
                    lean_inc(v_val_1755_);
                    lean_dec_ref_known(v___x_1754_, 1);
                    v___y_1738_ = v_val_1755_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1739_ = lean_string_utf8_byte_size(v_opt_1736_);
                v___x_1740_ = lean_nat_dec_eq(v___y_1738_, v___x_1739_);
                if v___x_1740_ == 0 {
                    v_toBind_1741_ = lean_ctor_get(v_inst_1732_, 1);
                    lean_inc(v_toBind_1741_);
                    lean_dec_ref(v_inst_1732_);
                    v_modifyGet_1742_ = lean_ctor_get(v_inst_1733_, 2);
                    lean_inc(v_modifyGet_1742_);
                    lean_dec_ref(v_inst_1733_);
                    lean_inc(v___y_1738_);
                    lean_inc_ref(v_opt_1736_);
                    v___f_1743_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_1743_, 0, v_opt_1736_);
                    lean_closure_set(v___f_1743_, 1, v___y_1738_);
                    lean_closure_set(v___f_1743_, 2, v_handle_1735_);
                    v___x_1744_ = lean_string_utf8_next_fast(v_opt_1736_, v___y_1738_);
                    lean_dec(v___y_1738_);
                    v___x_1745_ = lean_string_utf8_extract(v_opt_1736_, v___x_1744_, v___x_1739_);
                    lean_dec_ref(v_opt_1736_);
                    v___f_1746_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1746_, 0, v___x_1745_);
                    v___x_1747_ = lean_apply_2(v_modifyGet_1742_, lean_box(0), v___f_1746_);
                    v___x_1748_ = lean_apply_4(
                        v_toBind_1741_,
                        lean_box(0),
                        lean_box(0),
                        v___x_1747_,
                        v___f_1743_,
                    );
                    return v___x_1748_;
                } else {
                    lean_dec(v___y_1738_);
                    lean_dec_ref(v_inst_1733_);
                    lean_dec_ref(v_inst_1732_);
                    v___x_1749_ = lean_apply_1(v_handle_1735_, v_opt_1736_);
                    return v___x_1749_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOptionOrEq___redArg___lam__2(
    mut v___x_1756_: *mut LeanObject,
    mut v_opt_1757_: *mut LeanObject,
    mut v___x_1758_: *mut LeanObject,
    mut v_it_1759_: *mut LeanObject,
    mut v_acc_1760_: *mut LeanObject,
    mut v_hP_1761_: *mut LeanObject,
    mut v_recur_1762_: *mut LeanObject,
) -> *mut LeanObject {
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
            let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
            v___x_1767_ = lean_string_utf8_next_fast(v_opt_1757_, v_it_1759_);
            lean_dec(v_it_1759_);
            v___x_1768_ = lean_apply_4(
                v_recur_1762_,
                v___x_1767_,
                v___x_1758_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1768_;
        } else {
            let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_recur_1762_);
            lean_dec(v___x_1758_);
            v___x_1769_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1769_, 0, v_it_1759_);
            return v___x_1769_;
        }
    } else {
        lean_dec_ref(v_recur_1762_);
        lean_dec(v_it_1759_);
        lean_dec(v___x_1758_);
        lean_inc(v_acc_1760_);
        return v_acc_1760_;
    }
}
pub unsafe fn l_Lake_longOptionOrEq___redArg___lam__2___boxed(
    mut v___x_1770_: *mut LeanObject,
    mut v_opt_1771_: *mut LeanObject,
    mut v___x_1772_: *mut LeanObject,
    mut v_it_1773_: *mut LeanObject,
    mut v_acc_1774_: *mut LeanObject,
    mut v_hP_1775_: *mut LeanObject,
    mut v_recur_1776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1777_: *mut LeanObject = core::ptr::null_mut();
    v_res_1777_ = l_Lake_longOptionOrEq___redArg___lam__2(
        v___x_1770_,
        v_opt_1771_,
        v___x_1772_,
        v_it_1773_,
        v_acc_1774_,
        v_hP_1775_,
        v_recur_1776_,
    );
    lean_dec(v_acc_1774_);
    lean_dec_ref(v_opt_1771_);
    lean_dec(v___x_1770_);
    return v_res_1777_;
}
pub unsafe fn l_Lake_longOptionOrEq___redArg(
    mut v_inst_1778_: *mut LeanObject,
    mut v_inst_1779_: *mut LeanObject,
    mut v_handle_1780_: *mut LeanObject,
    mut v_opt_1781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: u8 = 0;
    let mut v_toBind_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1795_ = lean_unsigned_to_nat(0);
                v___x_1796_ = lean_string_utf8_byte_size(v_opt_1781_);
                v___x_1797_ = lean_box(0);
                lean_inc_ref(v_opt_1781_);
                v___f_1798_ = lean_alloc_closure(
                    l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_1798_, 0, v___x_1796_);
                lean_closure_set(v___f_1798_, 1, v_opt_1781_);
                lean_closure_set(v___f_1798_, 2, v___x_1797_);
                v___x_1799_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1798_,
                    v_searcher_1795_,
                    v___x_1797_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1799_) == 0 {
                    v___y_1783_ = v___x_1796_;
                    state = 1;
                    continue;
                } else {
                    v_val_1800_ = lean_ctor_get(v___x_1799_, 0);
                    lean_inc(v_val_1800_);
                    lean_dec_ref_known(v___x_1799_, 1);
                    v___y_1783_ = v_val_1800_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1784_ = lean_string_utf8_byte_size(v_opt_1781_);
                v___x_1785_ = lean_nat_dec_eq(v___y_1783_, v___x_1784_);
                if v___x_1785_ == 0 {
                    v_toBind_1786_ = lean_ctor_get(v_inst_1778_, 1);
                    lean_inc(v_toBind_1786_);
                    lean_dec_ref(v_inst_1778_);
                    v_modifyGet_1787_ = lean_ctor_get(v_inst_1779_, 2);
                    lean_inc(v_modifyGet_1787_);
                    lean_dec_ref(v_inst_1779_);
                    lean_inc(v___y_1783_);
                    lean_inc_ref(v_opt_1781_);
                    v___f_1788_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_1788_, 0, v_opt_1781_);
                    lean_closure_set(v___f_1788_, 1, v___y_1783_);
                    lean_closure_set(v___f_1788_, 2, v_handle_1780_);
                    v___x_1789_ = lean_string_utf8_next_fast(v_opt_1781_, v___y_1783_);
                    lean_dec(v___y_1783_);
                    v___x_1790_ = lean_string_utf8_extract(v_opt_1781_, v___x_1789_, v___x_1784_);
                    lean_dec_ref(v_opt_1781_);
                    v___f_1791_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1791_, 0, v___x_1790_);
                    v___x_1792_ = lean_apply_2(v_modifyGet_1787_, lean_box(0), v___f_1791_);
                    v___x_1793_ = lean_apply_4(
                        v_toBind_1786_,
                        lean_box(0),
                        lean_box(0),
                        v___x_1792_,
                        v___f_1788_,
                    );
                    return v___x_1793_;
                } else {
                    lean_dec(v___y_1783_);
                    lean_dec_ref(v_inst_1779_);
                    lean_dec_ref(v_inst_1778_);
                    v___x_1794_ = lean_apply_1(v_handle_1780_, v_opt_1781_);
                    return v___x_1794_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOptionOrEq(
    mut v_m_1801_: *mut LeanObject,
    mut v_inst_1802_: *mut LeanObject,
    mut v_inst_1803_: *mut LeanObject,
    mut v_00_u03b1_1804_: *mut LeanObject,
    mut v_handle_1805_: *mut LeanObject,
    mut v_opt_1806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: u8 = 0;
    let mut v_toBind_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1820_ = lean_unsigned_to_nat(0);
                v___x_1821_ = lean_string_utf8_byte_size(v_opt_1806_);
                v___x_1822_ = lean_box(0);
                lean_inc_ref(v_opt_1806_);
                v___f_1823_ = lean_alloc_closure(
                    l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_1823_, 0, v___x_1821_);
                lean_closure_set(v___f_1823_, 1, v_opt_1806_);
                lean_closure_set(v___f_1823_, 2, v___x_1822_);
                v___x_1824_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1823_,
                    v_searcher_1820_,
                    v___x_1822_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1824_) == 0 {
                    v___y_1808_ = v___x_1821_;
                    state = 1;
                    continue;
                } else {
                    v_val_1825_ = lean_ctor_get(v___x_1824_, 0);
                    lean_inc(v_val_1825_);
                    lean_dec_ref_known(v___x_1824_, 1);
                    v___y_1808_ = v_val_1825_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1809_ = lean_string_utf8_byte_size(v_opt_1806_);
                v___x_1810_ = lean_nat_dec_eq(v___y_1808_, v___x_1809_);
                if v___x_1810_ == 0 {
                    v_toBind_1811_ = lean_ctor_get(v_inst_1802_, 1);
                    lean_inc(v_toBind_1811_);
                    lean_dec_ref(v_inst_1802_);
                    v_modifyGet_1812_ = lean_ctor_get(v_inst_1803_, 2);
                    lean_inc(v_modifyGet_1812_);
                    lean_dec_ref(v_inst_1803_);
                    lean_inc(v___y_1808_);
                    lean_inc_ref(v_opt_1806_);
                    v___f_1813_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_1813_, 0, v_opt_1806_);
                    lean_closure_set(v___f_1813_, 1, v___y_1808_);
                    lean_closure_set(v___f_1813_, 2, v_handle_1805_);
                    v___x_1814_ = lean_string_utf8_next_fast(v_opt_1806_, v___y_1808_);
                    lean_dec(v___y_1808_);
                    v___x_1815_ = lean_string_utf8_extract(v_opt_1806_, v___x_1814_, v___x_1809_);
                    lean_dec_ref(v_opt_1806_);
                    v___f_1816_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1816_, 0, v___x_1815_);
                    v___x_1817_ = lean_apply_2(v_modifyGet_1812_, lean_box(0), v___f_1816_);
                    v___x_1818_ = lean_apply_4(
                        v_toBind_1811_,
                        lean_box(0),
                        lean_box(0),
                        v___x_1817_,
                        v___f_1813_,
                    );
                    return v___x_1818_;
                } else {
                    lean_dec(v___y_1808_);
                    lean_dec_ref(v_inst_1803_);
                    lean_dec_ref(v_inst_1802_);
                    v___x_1819_ = lean_apply_1(v_handle_1805_, v_opt_1806_);
                    return v___x_1819_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOption___redArg___lam__2(
    mut v___x_1826_: *mut LeanObject,
    mut v_searcher_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v_handle_1829_: *mut LeanObject,
    mut v_____r_1830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    v___x_1831_ = lean_string_utf8_extract(v___x_1826_, v_searcher_1827_, v___y_1828_);
    v___x_1832_ = lean_apply_1(v_handle_1829_, v___x_1831_);
    return v___x_1832_;
}
pub unsafe fn l_Lake_longOption___redArg___lam__2___boxed(
    mut v___x_1833_: *mut LeanObject,
    mut v_searcher_1834_: *mut LeanObject,
    mut v___y_1835_: *mut LeanObject,
    mut v_handle_1836_: *mut LeanObject,
    mut v_____r_1837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1838_: *mut LeanObject = core::ptr::null_mut();
    v_res_1838_ = l_Lake_longOption___redArg___lam__2(
        v___x_1833_,
        v_searcher_1834_,
        v___y_1835_,
        v_handle_1836_,
        v_____r_1837_,
    );
    lean_dec(v___y_1835_);
    lean_dec(v_searcher_1834_);
    lean_dec_ref(v___x_1833_);
    return v_res_1838_;
}
pub unsafe fn l_Lake_longOption___redArg___lam__1(
    mut v___x_1839_: *mut LeanObject,
    mut v___x_1840_: *mut LeanObject,
    mut v___x_1841_: *mut LeanObject,
    mut v_it_1842_: *mut LeanObject,
    mut v_acc_1843_: *mut LeanObject,
    mut v_hP_1844_: *mut LeanObject,
    mut v_recur_1845_: *mut LeanObject,
) -> *mut LeanObject {
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
            let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
            v___x_1850_ = lean_string_utf8_next_fast(v___x_1840_, v_it_1842_);
            lean_dec(v_it_1842_);
            v___x_1851_ = lean_apply_4(
                v_recur_1845_,
                v___x_1850_,
                v___x_1841_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1851_;
        } else {
            let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_recur_1845_);
            lean_dec(v___x_1841_);
            v___x_1852_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_1852_, 0, v_it_1842_);
            return v___x_1852_;
        }
    } else {
        lean_dec_ref(v_recur_1845_);
        lean_dec(v_it_1842_);
        lean_dec(v___x_1841_);
        lean_inc(v_acc_1843_);
        return v_acc_1843_;
    }
}
pub unsafe fn l_Lake_longOption___redArg___lam__1___boxed(
    mut v___x_1853_: *mut LeanObject,
    mut v___x_1854_: *mut LeanObject,
    mut v___x_1855_: *mut LeanObject,
    mut v_it_1856_: *mut LeanObject,
    mut v_acc_1857_: *mut LeanObject,
    mut v_hP_1858_: *mut LeanObject,
    mut v_recur_1859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1860_: *mut LeanObject = core::ptr::null_mut();
    v_res_1860_ = l_Lake_longOption___redArg___lam__1(
        v___x_1853_,
        v___x_1854_,
        v___x_1855_,
        v_it_1856_,
        v_acc_1857_,
        v_hP_1858_,
        v_recur_1859_,
    );
    lean_dec(v_acc_1857_);
    lean_dec_ref(v___x_1854_);
    lean_dec(v___x_1853_);
    return v_res_1860_;
}
pub unsafe fn l_Lake_longOption___redArg___lam__0(
    mut v_opt_1861_: *mut LeanObject,
    mut v___y_1862_: *mut LeanObject,
    mut v_handle_1863_: *mut LeanObject,
    mut v_modifyGet_1864_: *mut LeanObject,
    mut v_toBind_1865_: *mut LeanObject,
    mut v_____r_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_searcher_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: u8 = 0;
    let mut v___f_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1867_ = lean_unsigned_to_nat(0);
                v___x_1868_ = lean_string_utf8_extract(v_opt_1861_, v_searcher_1867_, v___y_1862_);
                v___x_1880_ = lean_string_utf8_byte_size(v___x_1868_);
                v___x_1881_ = lean_box(0);
                lean_inc_ref(v___x_1868_);
                v___f_1882_ = lean_alloc_closure(
                    l_Lake_longOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_1882_, 0, v___x_1880_);
                lean_closure_set(v___f_1882_, 1, v___x_1868_);
                lean_closure_set(v___f_1882_, 2, v___x_1881_);
                v___x_1883_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1882_,
                    v_searcher_1867_,
                    v___x_1881_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1883_) == 0 {
                    v___y_1870_ = v___x_1880_;
                    state = 1;
                    continue;
                } else {
                    v_val_1884_ = lean_ctor_get(v___x_1883_, 0);
                    lean_inc(v_val_1884_);
                    lean_dec_ref_known(v___x_1883_, 1);
                    v___y_1870_ = v_val_1884_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1871_ = lean_string_utf8_byte_size(v___x_1868_);
                v___x_1872_ = lean_nat_dec_eq(v___y_1870_, v___x_1871_);
                if v___x_1872_ == 0 {
                    lean_inc(v___y_1870_);
                    lean_inc_ref(v___x_1868_);
                    v___f_1873_ = lean_alloc_closure(
                        l_Lake_longOption___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    lean_closure_set(v___f_1873_, 0, v___x_1868_);
                    lean_closure_set(v___f_1873_, 1, v_searcher_1867_);
                    lean_closure_set(v___f_1873_, 2, v___y_1870_);
                    lean_closure_set(v___f_1873_, 3, v_handle_1863_);
                    v___x_1874_ = lean_string_utf8_next_fast(v___x_1868_, v___y_1870_);
                    lean_dec(v___y_1870_);
                    v___x_1875_ = lean_string_utf8_extract(v___x_1868_, v___x_1874_, v___x_1871_);
                    lean_dec_ref(v___x_1868_);
                    v___f_1876_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1876_, 0, v___x_1875_);
                    v___x_1877_ = lean_apply_2(v_modifyGet_1864_, lean_box(0), v___f_1876_);
                    v___x_1878_ = lean_apply_4(
                        v_toBind_1865_,
                        lean_box(0),
                        lean_box(0),
                        v___x_1877_,
                        v___f_1873_,
                    );
                    return v___x_1878_;
                } else {
                    lean_dec(v___y_1870_);
                    lean_dec(v_toBind_1865_);
                    lean_dec(v_modifyGet_1864_);
                    v___x_1879_ = lean_apply_1(v_handle_1863_, v___x_1868_);
                    return v___x_1879_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_longOption___redArg___lam__0___boxed(
    mut v_opt_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v_handle_1887_: *mut LeanObject,
    mut v_modifyGet_1888_: *mut LeanObject,
    mut v_toBind_1889_: *mut LeanObject,
    mut v_____r_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1891_: *mut LeanObject = core::ptr::null_mut();
    v_res_1891_ = l_Lake_longOption___redArg___lam__0(
        v_opt_1885_,
        v___y_1886_,
        v_handle_1887_,
        v_modifyGet_1888_,
        v_toBind_1889_,
        v_____r_1890_,
    );
    lean_dec(v___y_1886_);
    lean_dec_ref(v_opt_1885_);
    return v_res_1891_;
}
pub unsafe fn l_Lake_longOption___redArg(
    mut v_inst_1892_: *mut LeanObject,
    mut v_inst_1893_: *mut LeanObject,
    mut v_handle_1894_: *mut LeanObject,
    mut v_opt_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: u8 = 0;
    let mut v_toBind_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: u8 = 0;
    let mut v_toBind_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1926_ = lean_unsigned_to_nat(0);
                v___x_1927_ = lean_string_utf8_byte_size(v_opt_1895_);
                v___x_1928_ = lean_box(0);
                lean_inc_ref(v_opt_1895_);
                v___f_1929_ = lean_alloc_closure(
                    l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_1929_, 0, v___x_1927_);
                lean_closure_set(v___f_1929_, 1, v_opt_1895_);
                lean_closure_set(v___f_1929_, 2, v___x_1928_);
                v___x_1930_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1929_,
                    v_searcher_1926_,
                    v___x_1928_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1930_) == 0 {
                    v___y_1910_ = v___x_1927_;
                    state = 2;
                    continue;
                } else {
                    v_val_1931_ = lean_ctor_get(v___x_1930_, 0);
                    lean_inc(v_val_1931_);
                    lean_dec_ref_known(v___x_1930_, 1);
                    v___y_1910_ = v_val_1931_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1898_ = lean_string_utf8_byte_size(v_opt_1895_);
                v___x_1899_ = lean_nat_dec_eq(v___y_1897_, v___x_1898_);
                if v___x_1899_ == 0 {
                    v_toBind_1900_ = lean_ctor_get(v_inst_1892_, 1);
                    lean_inc(v_toBind_1900_);
                    lean_dec_ref(v_inst_1892_);
                    v_modifyGet_1901_ = lean_ctor_get(v_inst_1893_, 2);
                    lean_inc(v_modifyGet_1901_);
                    lean_dec_ref(v_inst_1893_);
                    lean_inc(v___y_1897_);
                    lean_inc_ref(v_opt_1895_);
                    v___f_1902_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_1902_, 0, v_opt_1895_);
                    lean_closure_set(v___f_1902_, 1, v___y_1897_);
                    lean_closure_set(v___f_1902_, 2, v_handle_1894_);
                    v___x_1903_ = lean_string_utf8_next_fast(v_opt_1895_, v___y_1897_);
                    lean_dec(v___y_1897_);
                    v___x_1904_ = lean_string_utf8_extract(v_opt_1895_, v___x_1903_, v___x_1898_);
                    lean_dec_ref(v_opt_1895_);
                    v___f_1905_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1905_, 0, v___x_1904_);
                    v___x_1906_ = lean_apply_2(v_modifyGet_1901_, lean_box(0), v___f_1905_);
                    v___x_1907_ = lean_apply_4(
                        v_toBind_1900_,
                        lean_box(0),
                        lean_box(0),
                        v___x_1906_,
                        v___f_1902_,
                    );
                    return v___x_1907_;
                } else {
                    lean_dec(v___y_1897_);
                    lean_dec_ref(v_inst_1893_);
                    lean_dec_ref(v_inst_1892_);
                    v___x_1908_ = lean_apply_1(v_handle_1894_, v_opt_1895_);
                    return v___x_1908_;
                }
            }
            2 => {
                v___x_1911_ = lean_string_utf8_byte_size(v_opt_1895_);
                v___x_1912_ = lean_nat_dec_eq(v___y_1910_, v___x_1911_);
                if v___x_1912_ == 0 {
                    v_toBind_1913_ = lean_ctor_get(v_inst_1892_, 1);
                    lean_inc_n(v_toBind_1913_, 2);
                    lean_dec_ref(v_inst_1892_);
                    v_modifyGet_1914_ = lean_ctor_get(v_inst_1893_, 2);
                    lean_inc_n(v_modifyGet_1914_, 2);
                    lean_dec_ref(v_inst_1893_);
                    lean_inc(v___y_1910_);
                    lean_inc_ref(v_opt_1895_);
                    v___f_1915_ = lean_alloc_closure(
                        l_Lake_longOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    lean_closure_set(v___f_1915_, 0, v_opt_1895_);
                    lean_closure_set(v___f_1915_, 1, v___y_1910_);
                    lean_closure_set(v___f_1915_, 2, v_handle_1894_);
                    lean_closure_set(v___f_1915_, 3, v_modifyGet_1914_);
                    lean_closure_set(v___f_1915_, 4, v_toBind_1913_);
                    v___x_1916_ = lean_string_utf8_next_fast(v_opt_1895_, v___y_1910_);
                    lean_dec(v___y_1910_);
                    v___x_1917_ = lean_string_utf8_extract(v_opt_1895_, v___x_1916_, v___x_1911_);
                    lean_dec_ref(v_opt_1895_);
                    v___f_1918_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1918_, 0, v___x_1917_);
                    v___x_1919_ = lean_apply_2(v_modifyGet_1914_, lean_box(0), v___f_1918_);
                    v___x_1920_ = lean_apply_4(
                        v_toBind_1913_,
                        lean_box(0),
                        lean_box(0),
                        v___x_1919_,
                        v___f_1915_,
                    );
                    return v___x_1920_;
                } else {
                    lean_dec(v___y_1910_);
                    v_searcher_1921_ = lean_unsigned_to_nat(0);
                    v___x_1922_ = lean_box(0);
                    lean_inc_ref(v_opt_1895_);
                    v___f_1923_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    lean_closure_set(v___f_1923_, 0, v___x_1911_);
                    lean_closure_set(v___f_1923_, 1, v_opt_1895_);
                    lean_closure_set(v___f_1923_, 2, v___x_1922_);
                    v___x_1924_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_1923_,
                        v_searcher_1921_,
                        v___x_1922_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1924_) == 0 {
                        v___y_1897_ = v___x_1911_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1925_ = lean_ctor_get(v___x_1924_, 0);
                        lean_inc(v_val_1925_);
                        lean_dec_ref_known(v___x_1924_, 1);
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
    mut v_m_1932_: *mut LeanObject,
    mut v_inst_1933_: *mut LeanObject,
    mut v_inst_1934_: *mut LeanObject,
    mut v_00_u03b1_1935_: *mut LeanObject,
    mut v_handle_1936_: *mut LeanObject,
    mut v_opt_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v_toBind_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: u8 = 0;
    let mut v_toBind_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_1968_ = lean_unsigned_to_nat(0);
                v___x_1969_ = lean_string_utf8_byte_size(v_opt_1937_);
                v___x_1970_ = lean_box(0);
                lean_inc_ref(v_opt_1937_);
                v___f_1971_ = lean_alloc_closure(
                    l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_1971_, 0, v___x_1969_);
                lean_closure_set(v___f_1971_, 1, v_opt_1937_);
                lean_closure_set(v___f_1971_, 2, v___x_1970_);
                v___x_1972_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_1971_,
                    v_searcher_1968_,
                    v___x_1970_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1972_) == 0 {
                    v___y_1952_ = v___x_1969_;
                    state = 2;
                    continue;
                } else {
                    v_val_1973_ = lean_ctor_get(v___x_1972_, 0);
                    lean_inc(v_val_1973_);
                    lean_dec_ref_known(v___x_1972_, 1);
                    v___y_1952_ = v_val_1973_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_1940_ = lean_string_utf8_byte_size(v_opt_1937_);
                v___x_1941_ = lean_nat_dec_eq(v___y_1939_, v___x_1940_);
                if v___x_1941_ == 0 {
                    v_toBind_1942_ = lean_ctor_get(v_inst_1933_, 1);
                    lean_inc(v_toBind_1942_);
                    lean_dec_ref(v_inst_1933_);
                    v_modifyGet_1943_ = lean_ctor_get(v_inst_1934_, 2);
                    lean_inc(v_modifyGet_1943_);
                    lean_dec_ref(v_inst_1934_);
                    lean_inc(v___y_1939_);
                    lean_inc_ref(v_opt_1937_);
                    v___f_1944_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_1944_, 0, v_opt_1937_);
                    lean_closure_set(v___f_1944_, 1, v___y_1939_);
                    lean_closure_set(v___f_1944_, 2, v_handle_1936_);
                    v___x_1945_ = lean_string_utf8_next_fast(v_opt_1937_, v___y_1939_);
                    lean_dec(v___y_1939_);
                    v___x_1946_ = lean_string_utf8_extract(v_opt_1937_, v___x_1945_, v___x_1940_);
                    lean_dec_ref(v_opt_1937_);
                    v___f_1947_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1947_, 0, v___x_1946_);
                    v___x_1948_ = lean_apply_2(v_modifyGet_1943_, lean_box(0), v___f_1947_);
                    v___x_1949_ = lean_apply_4(
                        v_toBind_1942_,
                        lean_box(0),
                        lean_box(0),
                        v___x_1948_,
                        v___f_1944_,
                    );
                    return v___x_1949_;
                } else {
                    lean_dec(v___y_1939_);
                    lean_dec_ref(v_inst_1934_);
                    lean_dec_ref(v_inst_1933_);
                    v___x_1950_ = lean_apply_1(v_handle_1936_, v_opt_1937_);
                    return v___x_1950_;
                }
            }
            2 => {
                v___x_1953_ = lean_string_utf8_byte_size(v_opt_1937_);
                v___x_1954_ = lean_nat_dec_eq(v___y_1952_, v___x_1953_);
                if v___x_1954_ == 0 {
                    v_toBind_1955_ = lean_ctor_get(v_inst_1933_, 1);
                    lean_inc_n(v_toBind_1955_, 2);
                    lean_dec_ref(v_inst_1933_);
                    v_modifyGet_1956_ = lean_ctor_get(v_inst_1934_, 2);
                    lean_inc_n(v_modifyGet_1956_, 2);
                    lean_dec_ref(v_inst_1934_);
                    lean_inc(v___y_1952_);
                    lean_inc_ref(v_opt_1937_);
                    v___f_1957_ = lean_alloc_closure(
                        l_Lake_longOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    lean_closure_set(v___f_1957_, 0, v_opt_1937_);
                    lean_closure_set(v___f_1957_, 1, v___y_1952_);
                    lean_closure_set(v___f_1957_, 2, v_handle_1936_);
                    lean_closure_set(v___f_1957_, 3, v_modifyGet_1956_);
                    lean_closure_set(v___f_1957_, 4, v_toBind_1955_);
                    v___x_1958_ = lean_string_utf8_next_fast(v_opt_1937_, v___y_1952_);
                    lean_dec(v___y_1952_);
                    v___x_1959_ = lean_string_utf8_extract(v_opt_1937_, v___x_1958_, v___x_1953_);
                    lean_dec_ref(v_opt_1937_);
                    v___f_1960_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_1960_, 0, v___x_1959_);
                    v___x_1961_ = lean_apply_2(v_modifyGet_1956_, lean_box(0), v___f_1960_);
                    v___x_1962_ = lean_apply_4(
                        v_toBind_1955_,
                        lean_box(0),
                        lean_box(0),
                        v___x_1961_,
                        v___f_1957_,
                    );
                    return v___x_1962_;
                } else {
                    lean_dec(v___y_1952_);
                    v_searcher_1963_ = lean_unsigned_to_nat(0);
                    v___x_1964_ = lean_box(0);
                    lean_inc_ref(v_opt_1937_);
                    v___f_1965_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    lean_closure_set(v___f_1965_, 0, v___x_1953_);
                    lean_closure_set(v___f_1965_, 1, v_opt_1937_);
                    lean_closure_set(v___f_1965_, 2, v___x_1964_);
                    v___x_1966_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_1965_,
                        v_searcher_1963_,
                        v___x_1964_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1966_) == 0 {
                        v___y_1939_ = v___x_1953_;
                        state = 1;
                        continue;
                    } else {
                        v_val_1967_ = lean_ctor_get(v___x_1966_, 0);
                        lean_inc(v_val_1967_);
                        lean_dec_ref_known(v___x_1966_, 1);
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
    mut v___x_1974_: *mut LeanObject,
    mut v_opt_1975_: *mut LeanObject,
    mut v_it_1976_: *mut LeanObject,
    mut v_acc_1977_: *mut LeanObject,
    mut v_hP_1978_: *mut LeanObject,
    mut v_recur_1979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1980_: u8 = 0;
    v___x_1980_ = lean_nat_dec_eq(v_it_1976_, v___x_1974_);
    if v___x_1980_ == 0 {
        let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
        v___x_1981_ = lean_string_utf8_next_fast(v_opt_1975_, v_it_1976_);
        v___x_1982_ = lean_unsigned_to_nat(1);
        v___x_1983_ = lean_nat_add(v_acc_1977_, v___x_1982_);
        v___x_1984_ = lean_apply_4(
            v_recur_1979_,
            v___x_1981_,
            v___x_1983_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1984_;
    } else {
        lean_dec_ref(v_recur_1979_);
        lean_inc(v_acc_1977_);
        return v_acc_1977_;
    }
}
pub unsafe fn l_Lake_shortOption___redArg___lam__0___boxed(
    mut v___x_1985_: *mut LeanObject,
    mut v_opt_1986_: *mut LeanObject,
    mut v_it_1987_: *mut LeanObject,
    mut v_acc_1988_: *mut LeanObject,
    mut v_hP_1989_: *mut LeanObject,
    mut v_recur_1990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1991_: *mut LeanObject = core::ptr::null_mut();
    v_res_1991_ = l_Lake_shortOption___redArg___lam__0(
        v___x_1985_,
        v_opt_1986_,
        v_it_1987_,
        v_acc_1988_,
        v_hP_1989_,
        v_recur_1990_,
    );
    lean_dec(v_acc_1988_);
    lean_dec(v_it_1987_);
    lean_dec_ref(v_opt_1986_);
    lean_dec(v___x_1985_);
    return v_res_1991_;
}
pub unsafe fn l_Lake_shortOption___redArg___lam__1(
    mut v_opt_1992_: *mut LeanObject,
    mut v_shortHandle_1993_: *mut LeanObject,
    mut v_____r_1994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: u32 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    v___x_1995_ = lean_unsigned_to_nat(1);
    v___x_1996_ = lean_string_utf8_get(v_opt_1992_, v___x_1995_);
    v___x_1997_ = lean_box_uint32(v___x_1996_);
    v___x_1998_ = lean_apply_1(v_shortHandle_1993_, v___x_1997_);
    return v___x_1998_;
}
pub unsafe fn l_Lake_shortOption___redArg___lam__1___boxed(
    mut v_opt_1999_: *mut LeanObject,
    mut v_shortHandle_2000_: *mut LeanObject,
    mut v_____r_2001_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2002_: *mut LeanObject = core::ptr::null_mut();
    v_res_2002_ =
        l_Lake_shortOption___redArg___lam__1(v_opt_1999_, v_shortHandle_2000_, v_____r_2001_);
    lean_dec_ref(v_opt_1999_);
    return v_res_2002_;
}
pub unsafe fn l_Lake_shortOption___redArg(
    mut v_inst_2003_: *mut LeanObject,
    mut v_inst_2004_: *mut LeanObject,
    mut v_shortHandle_2005_: *mut LeanObject,
    mut v_longHandle_2006_: *mut LeanObject,
    mut v_opt_2007_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: u8 = 0;
    let mut v___x_2016_: u32 = 0;
    let mut v___x_2017_: u32 = 0;
    let mut v___x_2018_: u8 = 0;
    let mut v___x_2019_: u32 = 0;
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2027_: u8 = 0;
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2039_: u8 = 0;
    let mut v_unused_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: u32 = 0;
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2008_ = lean_unsigned_to_nat(0);
                v___x_2009_ = lean_string_utf8_byte_size(v_opt_2007_);
                lean_inc_ref_n(v_opt_2007_, 2);
                v___f_2010_ = lean_alloc_closure(
                    l_Lake_shortOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    2,
                );
                lean_closure_set(v___f_2010_, 0, v___x_2009_);
                lean_closure_set(v___f_2010_, 1, v_opt_2007_);
                v___x_2011_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2011_, 0, v_opt_2007_);
                lean_ctor_set(v___x_2011_, 1, v___x_2008_);
                lean_ctor_set(v___x_2011_, 2, v___x_2009_);
                v___x_2012_ = l_String_Slice_positions(v___x_2011_);
                v___x_2013_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2010_,
                    v___x_2012_,
                    v___x_2008_,
                    lean_box(0),
                );
                v___x_2014_ = lean_unsigned_to_nat(2);
                v___x_2015_ = lean_nat_dec_eq(v___x_2013_, v___x_2014_);
                lean_dec(v___x_2013_);
                if v___x_2015_ == 0 {
                    v___x_2016_ = lean_string_utf8_get(v_opt_2007_, v___x_2014_);
                    v___x_2017_ = 61;
                    v___x_2018_ = lean_uint32_dec_eq(v___x_2016_, v___x_2017_);
                    if v___x_2018_ == 0 {
                        v___x_2019_ = 32;
                        v___x_2020_ = lean_uint32_dec_eq(v___x_2016_, v___x_2019_);
                        if v___x_2020_ == 0 {
                            lean_dec_ref_known(v___x_2011_, 3);
                            lean_dec(v_shortHandle_2005_);
                            lean_dec_ref(v_inst_2004_);
                            lean_dec_ref(v_inst_2003_);
                            v___x_2021_ = lean_apply_1(v_longHandle_2006_, v_opt_2007_);
                            return v___x_2021_;
                        } else {
                            lean_dec(v_longHandle_2006_);
                            v_toBind_2022_ = lean_ctor_get(v_inst_2003_, 1);
                            lean_inc(v_toBind_2022_);
                            lean_dec_ref(v_inst_2003_);
                            v___x_2023_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1_once
                                ),
                                _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                            );
                            v_modifyGet_2024_ = lean_ctor_get(v_inst_2004_, 2);
                            v_isSharedCheck_2039_ = (!lean_is_exclusive(v_inst_2004_)) as u8;
                            if v_isSharedCheck_2039_ == 0 {
                                v_unused_2040_ = lean_ctor_get(v_inst_2004_, 1);
                                lean_dec(v_unused_2040_);
                                v_unused_2041_ = lean_ctor_get(v_inst_2004_, 0);
                                lean_dec(v_unused_2041_);
                                v___x_2026_ = v_inst_2004_;
                                v_isShared_2027_ = v_isSharedCheck_2039_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_modifyGet_2024_);
                                lean_dec(v_inst_2004_);
                                v___x_2026_ = lean_box(0);
                                v_isShared_2027_ = v_isSharedCheck_2039_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_longHandle_2006_);
                        v_toBind_2042_ = lean_ctor_get(v_inst_2003_, 1);
                        lean_inc(v_toBind_2042_);
                        lean_dec_ref(v_inst_2003_);
                        v_modifyGet_2043_ = lean_ctor_get(v_inst_2004_, 2);
                        lean_inc(v_modifyGet_2043_);
                        lean_dec_ref(v_inst_2004_);
                        lean_inc_ref(v_opt_2007_);
                        v___f_2044_ = lean_alloc_closure(
                            l_Lake_shortOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_2044_, 0, v_opt_2007_);
                        lean_closure_set(v___f_2044_, 1, v_shortHandle_2005_);
                        v___x_2045_ = lean_unsigned_to_nat(3);
                        v___x_2046_ =
                            l_String_Slice_Pos_nextn(v___x_2011_, v___x_2008_, v___x_2045_);
                        lean_dec_ref_known(v___x_2011_, 3);
                        v___x_2047_ =
                            lean_string_utf8_extract(v_opt_2007_, v___x_2046_, v___x_2009_);
                        lean_dec(v___x_2046_);
                        lean_dec_ref(v_opt_2007_);
                        v___f_2048_ = lean_alloc_closure(
                            l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        lean_closure_set(v___f_2048_, 0, v___x_2047_);
                        v___x_2049_ = lean_apply_2(v_modifyGet_2043_, lean_box(0), v___f_2048_);
                        v___x_2050_ = lean_apply_4(
                            v_toBind_2042_,
                            lean_box(0),
                            lean_box(0),
                            v___x_2049_,
                            v___f_2044_,
                        );
                        return v___x_2050_;
                    }
                } else {
                    lean_dec_ref_known(v___x_2011_, 3);
                    lean_dec(v_longHandle_2006_);
                    lean_dec_ref(v_inst_2004_);
                    lean_dec_ref(v_inst_2003_);
                    v___x_2051_ = lean_unsigned_to_nat(1);
                    v___x_2052_ = lean_string_utf8_get(v_opt_2007_, v___x_2051_);
                    lean_dec_ref(v_opt_2007_);
                    v___x_2053_ = lean_box_uint32(v___x_2052_);
                    v___x_2054_ = lean_apply_1(v_shortHandle_2005_, v___x_2053_);
                    return v___x_2054_;
                }
            }
            1 => {
                v___x_2028_ = l_String_Slice_Pos_nextn(v___x_2011_, v___x_2008_, v___x_2014_);
                lean_dec_ref_known(v___x_2011_, 3);
                lean_inc_ref_n(v_opt_2007_, 2);
                v___f_2029_ = lean_alloc_closure(
                    l_Lake_shortOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2029_, 0, v_opt_2007_);
                lean_closure_set(v___f_2029_, 1, v_shortHandle_2005_);
                lean_inc(v___x_2028_);
                if v_isShared_2027_ == 0 {
                    lean_ctor_set(v___x_2026_, 2, v___x_2009_);
                    lean_ctor_set(v___x_2026_, 1, v___x_2028_);
                    lean_ctor_set(v___x_2026_, 0, v_opt_2007_);
                    v___x_2031_ = v___x_2026_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_opt_2007_);
                    lean_ctor_set(v_reuseFailAlloc_2038_, 1, v___x_2028_);
                    lean_ctor_set(v_reuseFailAlloc_2038_, 2, v___x_2009_);
                    v___x_2031_ = v_reuseFailAlloc_2038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2032_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_2031_, v___x_2008_, v___x_2023_);
                lean_dec_ref(v___x_2031_);
                v___x_2033_ = lean_nat_add(v___x_2028_, v___x_2032_);
                lean_dec(v___x_2032_);
                lean_dec(v___x_2028_);
                v___x_2034_ = lean_string_utf8_extract(v_opt_2007_, v___x_2033_, v___x_2009_);
                lean_dec(v___x_2033_);
                lean_dec_ref(v_opt_2007_);
                v___f_2035_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2035_, 0, v___x_2034_);
                v___x_2036_ = lean_apply_2(v_modifyGet_2024_, lean_box(0), v___f_2035_);
                v___x_2037_ = lean_apply_4(
                    v_toBind_2022_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_2055_: *mut LeanObject,
    mut v_inst_2056_: *mut LeanObject,
    mut v_inst_2057_: *mut LeanObject,
    mut v_00_u03b1_2058_: *mut LeanObject,
    mut v_shortHandle_2059_: *mut LeanObject,
    mut v_longHandle_2060_: *mut LeanObject,
    mut v_opt_2061_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: u8 = 0;
    let mut v___x_2070_: u32 = 0;
    let mut v___x_2071_: u32 = 0;
    let mut v___x_2072_: u8 = 0;
    let mut v___x_2073_: u32 = 0;
    let mut v___x_2074_: u8 = 0;
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2081_: u8 = 0;
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2093_: u8 = 0;
    let mut v_unused_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: u32 = 0;
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2062_ = lean_unsigned_to_nat(0);
                v___x_2063_ = lean_string_utf8_byte_size(v_opt_2061_);
                lean_inc_ref_n(v_opt_2061_, 2);
                v___f_2064_ = lean_alloc_closure(
                    l_Lake_shortOption___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    6,
                    2,
                );
                lean_closure_set(v___f_2064_, 0, v___x_2063_);
                lean_closure_set(v___f_2064_, 1, v_opt_2061_);
                v___x_2065_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2065_, 0, v_opt_2061_);
                lean_ctor_set(v___x_2065_, 1, v___x_2062_);
                lean_ctor_set(v___x_2065_, 2, v___x_2063_);
                v___x_2066_ = l_String_Slice_positions(v___x_2065_);
                v___x_2067_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2064_,
                    v___x_2066_,
                    v___x_2062_,
                    lean_box(0),
                );
                v___x_2068_ = lean_unsigned_to_nat(2);
                v___x_2069_ = lean_nat_dec_eq(v___x_2067_, v___x_2068_);
                lean_dec(v___x_2067_);
                if v___x_2069_ == 0 {
                    v___x_2070_ = lean_string_utf8_get(v_opt_2061_, v___x_2068_);
                    v___x_2071_ = 61;
                    v___x_2072_ = lean_uint32_dec_eq(v___x_2070_, v___x_2071_);
                    if v___x_2072_ == 0 {
                        v___x_2073_ = 32;
                        v___x_2074_ = lean_uint32_dec_eq(v___x_2070_, v___x_2073_);
                        if v___x_2074_ == 0 {
                            lean_dec_ref_known(v___x_2065_, 3);
                            lean_dec(v_shortHandle_2059_);
                            lean_dec_ref(v_inst_2057_);
                            lean_dec_ref(v_inst_2056_);
                            v___x_2075_ = lean_apply_1(v_longHandle_2060_, v_opt_2061_);
                            return v___x_2075_;
                        } else {
                            lean_dec(v_longHandle_2060_);
                            v_toBind_2076_ = lean_ctor_get(v_inst_2056_, 1);
                            lean_inc(v_toBind_2076_);
                            lean_dec_ref(v_inst_2056_);
                            v___x_2077_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1_once
                                ),
                                _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                            );
                            v_modifyGet_2078_ = lean_ctor_get(v_inst_2057_, 2);
                            v_isSharedCheck_2093_ = (!lean_is_exclusive(v_inst_2057_)) as u8;
                            if v_isSharedCheck_2093_ == 0 {
                                v_unused_2094_ = lean_ctor_get(v_inst_2057_, 1);
                                lean_dec(v_unused_2094_);
                                v_unused_2095_ = lean_ctor_get(v_inst_2057_, 0);
                                lean_dec(v_unused_2095_);
                                v___x_2080_ = v_inst_2057_;
                                v_isShared_2081_ = v_isSharedCheck_2093_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_modifyGet_2078_);
                                lean_dec(v_inst_2057_);
                                v___x_2080_ = lean_box(0);
                                v_isShared_2081_ = v_isSharedCheck_2093_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_longHandle_2060_);
                        v_toBind_2096_ = lean_ctor_get(v_inst_2056_, 1);
                        lean_inc(v_toBind_2096_);
                        lean_dec_ref(v_inst_2056_);
                        v_modifyGet_2097_ = lean_ctor_get(v_inst_2057_, 2);
                        lean_inc(v_modifyGet_2097_);
                        lean_dec_ref(v_inst_2057_);
                        lean_inc_ref(v_opt_2061_);
                        v___f_2098_ = lean_alloc_closure(
                            l_Lake_shortOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_2098_, 0, v_opt_2061_);
                        lean_closure_set(v___f_2098_, 1, v_shortHandle_2059_);
                        v___x_2099_ = lean_unsigned_to_nat(3);
                        v___x_2100_ =
                            l_String_Slice_Pos_nextn(v___x_2065_, v___x_2062_, v___x_2099_);
                        lean_dec_ref_known(v___x_2065_, 3);
                        v___x_2101_ =
                            lean_string_utf8_extract(v_opt_2061_, v___x_2100_, v___x_2063_);
                        lean_dec(v___x_2100_);
                        lean_dec_ref(v_opt_2061_);
                        v___f_2102_ = lean_alloc_closure(
                            l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        lean_closure_set(v___f_2102_, 0, v___x_2101_);
                        v___x_2103_ = lean_apply_2(v_modifyGet_2097_, lean_box(0), v___f_2102_);
                        v___x_2104_ = lean_apply_4(
                            v_toBind_2096_,
                            lean_box(0),
                            lean_box(0),
                            v___x_2103_,
                            v___f_2098_,
                        );
                        return v___x_2104_;
                    }
                } else {
                    lean_dec_ref_known(v___x_2065_, 3);
                    lean_dec(v_longHandle_2060_);
                    lean_dec_ref(v_inst_2057_);
                    lean_dec_ref(v_inst_2056_);
                    v___x_2105_ = lean_unsigned_to_nat(1);
                    v___x_2106_ = lean_string_utf8_get(v_opt_2061_, v___x_2105_);
                    lean_dec_ref(v_opt_2061_);
                    v___x_2107_ = lean_box_uint32(v___x_2106_);
                    v___x_2108_ = lean_apply_1(v_shortHandle_2059_, v___x_2107_);
                    return v___x_2108_;
                }
            }
            1 => {
                v___x_2082_ = l_String_Slice_Pos_nextn(v___x_2065_, v___x_2062_, v___x_2068_);
                lean_dec_ref_known(v___x_2065_, 3);
                lean_inc_ref_n(v_opt_2061_, 2);
                v___f_2083_ = lean_alloc_closure(
                    l_Lake_shortOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2083_, 0, v_opt_2061_);
                lean_closure_set(v___f_2083_, 1, v_shortHandle_2059_);
                lean_inc(v___x_2082_);
                if v_isShared_2081_ == 0 {
                    lean_ctor_set(v___x_2080_, 2, v___x_2063_);
                    lean_ctor_set(v___x_2080_, 1, v___x_2082_);
                    lean_ctor_set(v___x_2080_, 0, v_opt_2061_);
                    v___x_2085_ = v___x_2080_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_opt_2061_);
                    lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2082_);
                    lean_ctor_set(v_reuseFailAlloc_2092_, 2, v___x_2063_);
                    v___x_2085_ = v_reuseFailAlloc_2092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2086_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_2085_, v___x_2062_, v___x_2077_);
                lean_dec_ref(v___x_2085_);
                v___x_2087_ = lean_nat_add(v___x_2082_, v___x_2086_);
                lean_dec(v___x_2086_);
                lean_dec(v___x_2082_);
                v___x_2088_ = lean_string_utf8_extract(v_opt_2061_, v___x_2087_, v___x_2063_);
                lean_dec(v___x_2087_);
                lean_dec_ref(v_opt_2061_);
                v___f_2089_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2089_, 0, v___x_2088_);
                v___x_2090_ = lean_apply_2(v_modifyGet_2078_, lean_box(0), v___f_2089_);
                v___x_2091_ = lean_apply_4(
                    v_toBind_2076_,
                    lean_box(0),
                    lean_box(0),
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
    mut v___x_2109_: *mut LeanObject,
    mut v_opt_2110_: *mut LeanObject,
    mut v___x_2111_: *mut LeanObject,
    mut v_it_2112_: *mut LeanObject,
    mut v_acc_2113_: *mut LeanObject,
    mut v_hP_2114_: *mut LeanObject,
    mut v_recur_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2116_: u8 = 0;
    v___x_2116_ = lean_nat_dec_eq(v_it_2112_, v___x_2109_);
    if v___x_2116_ == 0 {
        let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
        v___x_2117_ = lean_string_utf8_next_fast(v_opt_2110_, v_it_2112_);
        v___x_2118_ = lean_nat_add(v_acc_2113_, v___x_2111_);
        v___x_2119_ = lean_apply_4(
            v_recur_2115_,
            v___x_2117_,
            v___x_2118_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_2119_;
    } else {
        lean_dec_ref(v_recur_2115_);
        lean_inc(v_acc_2113_);
        return v_acc_2113_;
    }
}
pub unsafe fn l_Lake_option___redArg___lam__0___boxed(
    mut v___x_2120_: *mut LeanObject,
    mut v_opt_2121_: *mut LeanObject,
    mut v___x_2122_: *mut LeanObject,
    mut v_it_2123_: *mut LeanObject,
    mut v_acc_2124_: *mut LeanObject,
    mut v_hP_2125_: *mut LeanObject,
    mut v_recur_2126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2127_: *mut LeanObject = core::ptr::null_mut();
    v_res_2127_ = l_Lake_option___redArg___lam__0(
        v___x_2120_,
        v_opt_2121_,
        v___x_2122_,
        v_it_2123_,
        v_acc_2124_,
        v_hP_2125_,
        v_recur_2126_,
    );
    lean_dec(v_acc_2124_);
    lean_dec(v_it_2123_);
    lean_dec(v___x_2122_);
    lean_dec_ref(v_opt_2121_);
    lean_dec(v___x_2120_);
    return v_res_2127_;
}
pub unsafe fn l_Lake_option___redArg___lam__1(
    mut v_short_2128_: *mut LeanObject,
    mut v___x_2129_: u32,
    mut v_____r_2130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    v___x_2131_ = lean_box_uint32(v___x_2129_);
    v___x_2132_ = lean_apply_1(v_short_2128_, v___x_2131_);
    return v___x_2132_;
}
pub unsafe fn l_Lake_option___redArg___lam__1___boxed(
    mut v_short_2133_: *mut LeanObject,
    mut v___x_2134_: *mut LeanObject,
    mut v_____r_2135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1512__boxed_2136_: u32 = 0;
    let mut v_res_2137_: *mut LeanObject = core::ptr::null_mut();
    v___x_1512__boxed_2136_ = lean_unbox_uint32(v___x_2134_);
    lean_dec(v___x_2134_);
    v_res_2137_ =
        l_Lake_option___redArg___lam__1(v_short_2133_, v___x_1512__boxed_2136_, v_____r_2135_);
    return v_res_2137_;
}
pub unsafe fn l_Lake_option___redArg___lam__5(
    mut v_opt_2138_: *mut LeanObject,
    mut v___y_2139_: *mut LeanObject,
    mut v_long_2140_: *mut LeanObject,
    mut v_____r_2141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    v___x_2142_ = lean_unsigned_to_nat(0);
    v___x_2143_ = lean_string_utf8_extract(v_opt_2138_, v___x_2142_, v___y_2139_);
    v___x_2144_ = lean_apply_1(v_long_2140_, v___x_2143_);
    return v___x_2144_;
}
pub unsafe fn l_Lake_option___redArg___lam__5___boxed(
    mut v_opt_2145_: *mut LeanObject,
    mut v___y_2146_: *mut LeanObject,
    mut v_long_2147_: *mut LeanObject,
    mut v_____r_2148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2149_: *mut LeanObject = core::ptr::null_mut();
    v_res_2149_ =
        l_Lake_option___redArg___lam__5(v_opt_2145_, v___y_2146_, v_long_2147_, v_____r_2148_);
    lean_dec(v___y_2146_);
    lean_dec_ref(v_opt_2145_);
    return v_res_2149_;
}
pub unsafe fn l_Lake_option___redArg___lam__3(
    mut v___x_2150_: *mut LeanObject,
    mut v_searcher_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v_long_2153_: *mut LeanObject,
    mut v_____r_2154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    v___x_2155_ = lean_string_utf8_extract(v___x_2150_, v_searcher_2151_, v___y_2152_);
    v___x_2156_ = lean_apply_1(v_long_2153_, v___x_2155_);
    return v___x_2156_;
}
pub unsafe fn l_Lake_option___redArg___lam__3___boxed(
    mut v___x_2157_: *mut LeanObject,
    mut v_searcher_2158_: *mut LeanObject,
    mut v___y_2159_: *mut LeanObject,
    mut v_long_2160_: *mut LeanObject,
    mut v_____r_2161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2162_: *mut LeanObject = core::ptr::null_mut();
    v_res_2162_ = l_Lake_option___redArg___lam__3(
        v___x_2157_,
        v_searcher_2158_,
        v___y_2159_,
        v_long_2160_,
        v_____r_2161_,
    );
    lean_dec(v___y_2159_);
    lean_dec(v_searcher_2158_);
    lean_dec_ref(v___x_2157_);
    return v_res_2162_;
}
pub unsafe fn l_Lake_option___redArg___lam__6(
    mut v_opt_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
    mut v_long_2165_: *mut LeanObject,
    mut v_modifyGet_2166_: *mut LeanObject,
    mut v_toBind_2167_: *mut LeanObject,
    mut v_____r_2168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_searcher_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: u8 = 0;
    let mut v___f_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_searcher_2169_ = lean_unsigned_to_nat(0);
                v___x_2170_ = lean_string_utf8_extract(v_opt_2163_, v_searcher_2169_, v___y_2164_);
                v___x_2182_ = lean_string_utf8_byte_size(v___x_2170_);
                v___x_2183_ = lean_box(0);
                lean_inc_ref(v___x_2170_);
                v___f_2184_ = lean_alloc_closure(
                    l_Lake_longOption___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_2184_, 0, v___x_2182_);
                lean_closure_set(v___f_2184_, 1, v___x_2170_);
                lean_closure_set(v___f_2184_, 2, v___x_2183_);
                v___x_2185_ = l_WellFounded_opaqueFix_u2083___redArg(
                    v___f_2184_,
                    v_searcher_2169_,
                    v___x_2183_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2185_) == 0 {
                    v___y_2172_ = v___x_2182_;
                    state = 1;
                    continue;
                } else {
                    v_val_2186_ = lean_ctor_get(v___x_2185_, 0);
                    lean_inc(v_val_2186_);
                    lean_dec_ref_known(v___x_2185_, 1);
                    v___y_2172_ = v_val_2186_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2173_ = lean_string_utf8_byte_size(v___x_2170_);
                v___x_2174_ = lean_nat_dec_eq(v___y_2172_, v___x_2173_);
                if v___x_2174_ == 0 {
                    lean_inc(v___y_2172_);
                    lean_inc_ref(v___x_2170_);
                    v___f_2175_ = lean_alloc_closure(
                        l_Lake_option___redArg___lam__3___boxed as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    lean_closure_set(v___f_2175_, 0, v___x_2170_);
                    lean_closure_set(v___f_2175_, 1, v_searcher_2169_);
                    lean_closure_set(v___f_2175_, 2, v___y_2172_);
                    lean_closure_set(v___f_2175_, 3, v_long_2165_);
                    v___x_2176_ = lean_string_utf8_next_fast(v___x_2170_, v___y_2172_);
                    lean_dec(v___y_2172_);
                    v___x_2177_ = lean_string_utf8_extract(v___x_2170_, v___x_2176_, v___x_2173_);
                    lean_dec_ref(v___x_2170_);
                    v___f_2178_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2178_, 0, v___x_2177_);
                    v___x_2179_ = lean_apply_2(v_modifyGet_2166_, lean_box(0), v___f_2178_);
                    v___x_2180_ = lean_apply_4(
                        v_toBind_2167_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2179_,
                        v___f_2175_,
                    );
                    return v___x_2180_;
                } else {
                    lean_dec(v___y_2172_);
                    lean_dec(v_toBind_2167_);
                    lean_dec(v_modifyGet_2166_);
                    v___x_2181_ = lean_apply_1(v_long_2165_, v___x_2170_);
                    return v___x_2181_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_option___redArg___lam__6___boxed(
    mut v_opt_2187_: *mut LeanObject,
    mut v___y_2188_: *mut LeanObject,
    mut v_long_2189_: *mut LeanObject,
    mut v_modifyGet_2190_: *mut LeanObject,
    mut v_toBind_2191_: *mut LeanObject,
    mut v_____r_2192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2193_: *mut LeanObject = core::ptr::null_mut();
    v_res_2193_ = l_Lake_option___redArg___lam__6(
        v_opt_2187_,
        v___y_2188_,
        v_long_2189_,
        v_modifyGet_2190_,
        v_toBind_2191_,
        v_____r_2192_,
    );
    lean_dec(v___y_2188_);
    lean_dec_ref(v_opt_2187_);
    return v_res_2193_;
}
pub unsafe fn l_Lake_option___redArg(
    mut v_inst_2194_: *mut LeanObject,
    mut v_inst_2195_: *mut LeanObject,
    mut v_handlers_2196_: *mut LeanObject,
    mut v_opt_2197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u32 = 0;
    let mut v___x_2200_: u32 = 0;
    let mut v___x_2201_: u8 = 0;
    let mut v_short_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_longShort_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u8 = 0;
    let mut v___x_2216_: u32 = 0;
    let mut v___x_2217_: u32 = 0;
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: u32 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2227_: u8 = 0;
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2240_: u8 = 0;
    let mut v_unused_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2256_: u8 = 0;
    let mut v_unused_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_long_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v_toBind_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: u8 = 0;
    let mut v_toBind_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2198_ = lean_unsigned_to_nat(1);
                v___x_2199_ = lean_string_utf8_get(v_opt_2197_, v___x_2198_);
                v___x_2200_ = 45;
                v___x_2201_ = lean_uint32_dec_eq(v___x_2199_, v___x_2200_);
                if v___x_2201_ == 0 {
                    v_short_2202_ = lean_ctor_get(v_handlers_2196_, 1);
                    v_longShort_2203_ = lean_ctor_get(v_handlers_2196_, 2);
                    v_isSharedCheck_2256_ = (!lean_is_exclusive(v_handlers_2196_)) as u8;
                    if v_isSharedCheck_2256_ == 0 {
                        v_unused_2257_ = lean_ctor_get(v_handlers_2196_, 0);
                        lean_dec(v_unused_2257_);
                        v___x_2205_ = v_handlers_2196_;
                        v_isShared_2206_ = v_isSharedCheck_2256_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_longShort_2203_);
                        lean_inc(v_short_2202_);
                        lean_dec(v_handlers_2196_);
                        v___x_2205_ = lean_box(0);
                        v_isShared_2206_ = v_isSharedCheck_2256_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_long_2258_ = lean_ctor_get(v_handlers_2196_, 0);
                    lean_inc(v_long_2258_);
                    lean_dec_ref(v_handlers_2196_);
                    v_searcher_2289_ = lean_unsigned_to_nat(0);
                    v___x_2290_ = lean_string_utf8_byte_size(v_opt_2197_);
                    v___x_2291_ = lean_box(0);
                    lean_inc_ref(v_opt_2197_);
                    v___f_2292_ = lean_alloc_closure(
                        l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    lean_closure_set(v___f_2292_, 0, v___x_2290_);
                    lean_closure_set(v___f_2292_, 1, v_opt_2197_);
                    lean_closure_set(v___f_2292_, 2, v___x_2291_);
                    v___x_2293_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2292_,
                        v_searcher_2289_,
                        v___x_2291_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2293_) == 0 {
                        v___y_2273_ = v___x_2290_;
                        state = 6;
                        continue;
                    } else {
                        v_val_2294_ = lean_ctor_get(v___x_2293_, 0);
                        lean_inc(v_val_2294_);
                        lean_dec_ref_known(v___x_2293_, 1);
                        v___y_2273_ = v_val_2294_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2207_ = lean_unsigned_to_nat(0);
                v___x_2208_ = lean_string_utf8_byte_size(v_opt_2197_);
                lean_inc_ref_n(v_opt_2197_, 2);
                v___f_2209_ = lean_alloc_closure(
                    l_Lake_option___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_2209_, 0, v___x_2208_);
                lean_closure_set(v___f_2209_, 1, v_opt_2197_);
                lean_closure_set(v___f_2209_, 2, v___x_2198_);
                if v_isShared_2206_ == 0 {
                    lean_ctor_set(v___x_2205_, 2, v___x_2208_);
                    lean_ctor_set(v___x_2205_, 1, v___x_2207_);
                    lean_ctor_set(v___x_2205_, 0, v_opt_2197_);
                    v___x_2211_ = v___x_2205_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2255_, 0, v_opt_2197_);
                    lean_ctor_set(v_reuseFailAlloc_2255_, 1, v___x_2207_);
                    lean_ctor_set(v_reuseFailAlloc_2255_, 2, v___x_2208_);
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
                    lean_box(0),
                );
                v___x_2214_ = lean_unsigned_to_nat(2);
                v___x_2215_ = lean_nat_dec_eq(v___x_2213_, v___x_2214_);
                lean_dec(v___x_2213_);
                if v___x_2215_ == 0 {
                    v___x_2216_ = lean_string_utf8_get(v_opt_2197_, v___x_2214_);
                    v___x_2217_ = 61;
                    v___x_2218_ = lean_uint32_dec_eq(v___x_2216_, v___x_2217_);
                    if v___x_2218_ == 0 {
                        v___x_2219_ = 32;
                        v___x_2220_ = lean_uint32_dec_eq(v___x_2216_, v___x_2219_);
                        if v___x_2220_ == 0 {
                            lean_dec_ref(v___x_2211_);
                            lean_dec(v_short_2202_);
                            lean_dec_ref(v_inst_2195_);
                            lean_dec_ref(v_inst_2194_);
                            v___x_2221_ = lean_apply_1(v_longShort_2203_, v_opt_2197_);
                            return v___x_2221_;
                        } else {
                            lean_dec(v_longShort_2203_);
                            v_toBind_2222_ = lean_ctor_get(v_inst_2194_, 1);
                            lean_inc(v_toBind_2222_);
                            lean_dec_ref(v_inst_2194_);
                            v___x_2223_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1_once
                                ),
                                _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                            );
                            v_modifyGet_2224_ = lean_ctor_get(v_inst_2195_, 2);
                            v_isSharedCheck_2240_ = (!lean_is_exclusive(v_inst_2195_)) as u8;
                            if v_isSharedCheck_2240_ == 0 {
                                v_unused_2241_ = lean_ctor_get(v_inst_2195_, 1);
                                lean_dec(v_unused_2241_);
                                v_unused_2242_ = lean_ctor_get(v_inst_2195_, 0);
                                lean_dec(v_unused_2242_);
                                v___x_2226_ = v_inst_2195_;
                                v_isShared_2227_ = v_isSharedCheck_2240_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_modifyGet_2224_);
                                lean_dec(v_inst_2195_);
                                v___x_2226_ = lean_box(0);
                                v_isShared_2227_ = v_isSharedCheck_2240_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_longShort_2203_);
                        v_toBind_2243_ = lean_ctor_get(v_inst_2194_, 1);
                        lean_inc(v_toBind_2243_);
                        lean_dec_ref(v_inst_2194_);
                        v_modifyGet_2244_ = lean_ctor_get(v_inst_2195_, 2);
                        lean_inc(v_modifyGet_2244_);
                        lean_dec_ref(v_inst_2195_);
                        v___x_2245_ = lean_box_uint32(v___x_2199_);
                        v___f_2246_ = lean_alloc_closure(
                            l_Lake_option___redArg___lam__1___boxed as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_2246_, 0, v_short_2202_);
                        lean_closure_set(v___f_2246_, 1, v___x_2245_);
                        v___x_2247_ = lean_unsigned_to_nat(3);
                        v___x_2248_ =
                            l_String_Slice_Pos_nextn(v___x_2211_, v___x_2207_, v___x_2247_);
                        lean_dec_ref(v___x_2211_);
                        v___x_2249_ =
                            lean_string_utf8_extract(v_opt_2197_, v___x_2248_, v___x_2208_);
                        lean_dec(v___x_2248_);
                        lean_dec_ref(v_opt_2197_);
                        v___f_2250_ = lean_alloc_closure(
                            l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        lean_closure_set(v___f_2250_, 0, v___x_2249_);
                        v___x_2251_ = lean_apply_2(v_modifyGet_2244_, lean_box(0), v___f_2250_);
                        v___x_2252_ = lean_apply_4(
                            v_toBind_2243_,
                            lean_box(0),
                            lean_box(0),
                            v___x_2251_,
                            v___f_2246_,
                        );
                        return v___x_2252_;
                    }
                } else {
                    lean_dec_ref(v___x_2211_);
                    lean_dec(v_longShort_2203_);
                    lean_dec_ref(v_opt_2197_);
                    lean_dec_ref(v_inst_2195_);
                    lean_dec_ref(v_inst_2194_);
                    v___x_2253_ = lean_box_uint32(v___x_2199_);
                    v___x_2254_ = lean_apply_1(v_short_2202_, v___x_2253_);
                    return v___x_2254_;
                }
            }
            3 => {
                v___x_2228_ = l_String_Slice_Pos_nextn(v___x_2211_, v___x_2207_, v___x_2214_);
                lean_dec_ref(v___x_2211_);
                v___x_2229_ = lean_box_uint32(v___x_2199_);
                v___f_2230_ = lean_alloc_closure(
                    l_Lake_option___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2230_, 0, v_short_2202_);
                lean_closure_set(v___f_2230_, 1, v___x_2229_);
                lean_inc(v___x_2228_);
                lean_inc_ref(v_opt_2197_);
                if v_isShared_2227_ == 0 {
                    lean_ctor_set(v___x_2226_, 2, v___x_2208_);
                    lean_ctor_set(v___x_2226_, 1, v___x_2228_);
                    lean_ctor_set(v___x_2226_, 0, v_opt_2197_);
                    v___x_2232_ = v___x_2226_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2239_, 0, v_opt_2197_);
                    lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2228_);
                    lean_ctor_set(v_reuseFailAlloc_2239_, 2, v___x_2208_);
                    v___x_2232_ = v_reuseFailAlloc_2239_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2233_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_2232_, v___x_2207_, v___x_2223_);
                lean_dec_ref(v___x_2232_);
                v___x_2234_ = lean_nat_add(v___x_2228_, v___x_2233_);
                lean_dec(v___x_2233_);
                lean_dec(v___x_2228_);
                v___x_2235_ = lean_string_utf8_extract(v_opt_2197_, v___x_2234_, v___x_2208_);
                lean_dec(v___x_2234_);
                lean_dec_ref(v_opt_2197_);
                v___f_2236_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2236_, 0, v___x_2235_);
                v___x_2237_ = lean_apply_2(v_modifyGet_2224_, lean_box(0), v___f_2236_);
                v___x_2238_ = lean_apply_4(
                    v_toBind_2222_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2237_,
                    v___f_2230_,
                );
                return v___x_2238_;
            }
            5 => {
                v___x_2261_ = lean_string_utf8_byte_size(v_opt_2197_);
                v___x_2262_ = lean_nat_dec_eq(v___y_2260_, v___x_2261_);
                if v___x_2262_ == 0 {
                    v_toBind_2263_ = lean_ctor_get(v_inst_2194_, 1);
                    lean_inc(v_toBind_2263_);
                    lean_dec_ref(v_inst_2194_);
                    v_modifyGet_2264_ = lean_ctor_get(v_inst_2195_, 2);
                    lean_inc(v_modifyGet_2264_);
                    lean_dec_ref(v_inst_2195_);
                    lean_inc(v___y_2260_);
                    lean_inc_ref(v_opt_2197_);
                    v___f_2265_ = lean_alloc_closure(
                        l_Lake_option___redArg___lam__5___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_2265_, 0, v_opt_2197_);
                    lean_closure_set(v___f_2265_, 1, v___y_2260_);
                    lean_closure_set(v___f_2265_, 2, v_long_2258_);
                    v___x_2266_ = lean_string_utf8_next_fast(v_opt_2197_, v___y_2260_);
                    lean_dec(v___y_2260_);
                    v___x_2267_ = lean_string_utf8_extract(v_opt_2197_, v___x_2266_, v___x_2261_);
                    lean_dec_ref(v_opt_2197_);
                    v___f_2268_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2268_, 0, v___x_2267_);
                    v___x_2269_ = lean_apply_2(v_modifyGet_2264_, lean_box(0), v___f_2268_);
                    v___x_2270_ = lean_apply_4(
                        v_toBind_2263_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2269_,
                        v___f_2265_,
                    );
                    return v___x_2270_;
                } else {
                    lean_dec(v___y_2260_);
                    lean_dec_ref(v_inst_2195_);
                    lean_dec_ref(v_inst_2194_);
                    v___x_2271_ = lean_apply_1(v_long_2258_, v_opt_2197_);
                    return v___x_2271_;
                }
            }
            6 => {
                v___x_2274_ = lean_string_utf8_byte_size(v_opt_2197_);
                v___x_2275_ = lean_nat_dec_eq(v___y_2273_, v___x_2274_);
                if v___x_2275_ == 0 {
                    v_toBind_2276_ = lean_ctor_get(v_inst_2194_, 1);
                    lean_inc_n(v_toBind_2276_, 2);
                    lean_dec_ref(v_inst_2194_);
                    v_modifyGet_2277_ = lean_ctor_get(v_inst_2195_, 2);
                    lean_inc_n(v_modifyGet_2277_, 2);
                    lean_dec_ref(v_inst_2195_);
                    lean_inc(v___y_2273_);
                    lean_inc_ref(v_opt_2197_);
                    v___f_2278_ = lean_alloc_closure(
                        l_Lake_option___redArg___lam__6___boxed as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    lean_closure_set(v___f_2278_, 0, v_opt_2197_);
                    lean_closure_set(v___f_2278_, 1, v___y_2273_);
                    lean_closure_set(v___f_2278_, 2, v_long_2258_);
                    lean_closure_set(v___f_2278_, 3, v_modifyGet_2277_);
                    lean_closure_set(v___f_2278_, 4, v_toBind_2276_);
                    v___x_2279_ = lean_string_utf8_next_fast(v_opt_2197_, v___y_2273_);
                    lean_dec(v___y_2273_);
                    v___x_2280_ = lean_string_utf8_extract(v_opt_2197_, v___x_2279_, v___x_2274_);
                    lean_dec_ref(v_opt_2197_);
                    v___f_2281_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2281_, 0, v___x_2280_);
                    v___x_2282_ = lean_apply_2(v_modifyGet_2277_, lean_box(0), v___f_2281_);
                    v___x_2283_ = lean_apply_4(
                        v_toBind_2276_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2282_,
                        v___f_2278_,
                    );
                    return v___x_2283_;
                } else {
                    lean_dec(v___y_2273_);
                    v_searcher_2284_ = lean_unsigned_to_nat(0);
                    v___x_2285_ = lean_box(0);
                    lean_inc_ref(v_opt_2197_);
                    v___f_2286_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    lean_closure_set(v___f_2286_, 0, v___x_2274_);
                    lean_closure_set(v___f_2286_, 1, v_opt_2197_);
                    lean_closure_set(v___f_2286_, 2, v___x_2285_);
                    v___x_2287_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2286_,
                        v_searcher_2284_,
                        v___x_2285_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2287_) == 0 {
                        v___y_2260_ = v___x_2274_;
                        state = 5;
                        continue;
                    } else {
                        v_val_2288_ = lean_ctor_get(v___x_2287_, 0);
                        lean_inc(v_val_2288_);
                        lean_dec_ref_known(v___x_2287_, 1);
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
    mut v_m_2295_: *mut LeanObject,
    mut v_inst_2296_: *mut LeanObject,
    mut v_inst_2297_: *mut LeanObject,
    mut v_00_u03b1_2298_: *mut LeanObject,
    mut v_handlers_2299_: *mut LeanObject,
    mut v_opt_2300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: u32 = 0;
    let mut v___x_2303_: u32 = 0;
    let mut v___x_2304_: u8 = 0;
    let mut v_short_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_longShort_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: u8 = 0;
    let mut v___x_2319_: u32 = 0;
    let mut v___x_2320_: u32 = 0;
    let mut v___x_2321_: u8 = 0;
    let mut v___x_2322_: u32 = 0;
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2330_: u8 = 0;
    let mut v___x_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2343_: u8 = 0;
    let mut v_unused_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2359_: u8 = 0;
    let mut v_unused_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_long_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: u8 = 0;
    let mut v_toBind_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: u8 = 0;
    let mut v_toBind_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2301_ = lean_unsigned_to_nat(1);
                v___x_2302_ = lean_string_utf8_get(v_opt_2300_, v___x_2301_);
                v___x_2303_ = 45;
                v___x_2304_ = lean_uint32_dec_eq(v___x_2302_, v___x_2303_);
                if v___x_2304_ == 0 {
                    v_short_2305_ = lean_ctor_get(v_handlers_2299_, 1);
                    v_longShort_2306_ = lean_ctor_get(v_handlers_2299_, 2);
                    v_isSharedCheck_2359_ = (!lean_is_exclusive(v_handlers_2299_)) as u8;
                    if v_isSharedCheck_2359_ == 0 {
                        v_unused_2360_ = lean_ctor_get(v_handlers_2299_, 0);
                        lean_dec(v_unused_2360_);
                        v___x_2308_ = v_handlers_2299_;
                        v_isShared_2309_ = v_isSharedCheck_2359_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_longShort_2306_);
                        lean_inc(v_short_2305_);
                        lean_dec(v_handlers_2299_);
                        v___x_2308_ = lean_box(0);
                        v_isShared_2309_ = v_isSharedCheck_2359_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_long_2361_ = lean_ctor_get(v_handlers_2299_, 0);
                    lean_inc(v_long_2361_);
                    lean_dec_ref(v_handlers_2299_);
                    v_searcher_2392_ = lean_unsigned_to_nat(0);
                    v___x_2393_ = lean_string_utf8_byte_size(v_opt_2300_);
                    v___x_2394_ = lean_box(0);
                    lean_inc_ref(v_opt_2300_);
                    v___f_2395_ = lean_alloc_closure(
                        l_Lake_longOptionOrEq___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    lean_closure_set(v___f_2395_, 0, v___x_2393_);
                    lean_closure_set(v___f_2395_, 1, v_opt_2300_);
                    lean_closure_set(v___f_2395_, 2, v___x_2394_);
                    v___x_2396_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2395_,
                        v_searcher_2392_,
                        v___x_2394_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2396_) == 0 {
                        v___y_2376_ = v___x_2393_;
                        state = 6;
                        continue;
                    } else {
                        v_val_2397_ = lean_ctor_get(v___x_2396_, 0);
                        lean_inc(v_val_2397_);
                        lean_dec_ref_known(v___x_2396_, 1);
                        v___y_2376_ = v_val_2397_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2310_ = lean_unsigned_to_nat(0);
                v___x_2311_ = lean_string_utf8_byte_size(v_opt_2300_);
                lean_inc_ref_n(v_opt_2300_, 2);
                v___f_2312_ = lean_alloc_closure(
                    l_Lake_option___redArg___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    3,
                );
                lean_closure_set(v___f_2312_, 0, v___x_2311_);
                lean_closure_set(v___f_2312_, 1, v_opt_2300_);
                lean_closure_set(v___f_2312_, 2, v___x_2301_);
                if v_isShared_2309_ == 0 {
                    lean_ctor_set(v___x_2308_, 2, v___x_2311_);
                    lean_ctor_set(v___x_2308_, 1, v___x_2310_);
                    lean_ctor_set(v___x_2308_, 0, v_opt_2300_);
                    v___x_2314_ = v___x_2308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_opt_2300_);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 1, v___x_2310_);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 2, v___x_2311_);
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
                    lean_box(0),
                );
                v___x_2317_ = lean_unsigned_to_nat(2);
                v___x_2318_ = lean_nat_dec_eq(v___x_2316_, v___x_2317_);
                lean_dec(v___x_2316_);
                if v___x_2318_ == 0 {
                    v___x_2319_ = lean_string_utf8_get(v_opt_2300_, v___x_2317_);
                    v___x_2320_ = 61;
                    v___x_2321_ = lean_uint32_dec_eq(v___x_2319_, v___x_2320_);
                    if v___x_2321_ == 0 {
                        v___x_2322_ = 32;
                        v___x_2323_ = lean_uint32_dec_eq(v___x_2319_, v___x_2322_);
                        if v___x_2323_ == 0 {
                            lean_dec_ref(v___x_2314_);
                            lean_dec(v_short_2305_);
                            lean_dec_ref(v_inst_2297_);
                            lean_dec_ref(v_inst_2296_);
                            v___x_2324_ = lean_apply_1(v_longShort_2306_, v_opt_2300_);
                            return v___x_2324_;
                        } else {
                            lean_dec(v_longShort_2306_);
                            v_toBind_2325_ = lean_ctor_get(v_inst_2296_, 1);
                            lean_inc(v_toBind_2325_);
                            lean_dec_ref(v_inst_2296_);
                            v___x_2326_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lake_shortOptionWithSpace___redArg___closed__1_once
                                ),
                                _init_l_Lake_shortOptionWithSpace___redArg___closed__1,
                            );
                            v_modifyGet_2327_ = lean_ctor_get(v_inst_2297_, 2);
                            v_isSharedCheck_2343_ = (!lean_is_exclusive(v_inst_2297_)) as u8;
                            if v_isSharedCheck_2343_ == 0 {
                                v_unused_2344_ = lean_ctor_get(v_inst_2297_, 1);
                                lean_dec(v_unused_2344_);
                                v_unused_2345_ = lean_ctor_get(v_inst_2297_, 0);
                                lean_dec(v_unused_2345_);
                                v___x_2329_ = v_inst_2297_;
                                v_isShared_2330_ = v_isSharedCheck_2343_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_modifyGet_2327_);
                                lean_dec(v_inst_2297_);
                                v___x_2329_ = lean_box(0);
                                v_isShared_2330_ = v_isSharedCheck_2343_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_longShort_2306_);
                        v_toBind_2346_ = lean_ctor_get(v_inst_2296_, 1);
                        lean_inc(v_toBind_2346_);
                        lean_dec_ref(v_inst_2296_);
                        v_modifyGet_2347_ = lean_ctor_get(v_inst_2297_, 2);
                        lean_inc(v_modifyGet_2347_);
                        lean_dec_ref(v_inst_2297_);
                        v___x_2348_ = lean_box_uint32(v___x_2302_);
                        v___f_2349_ = lean_alloc_closure(
                            l_Lake_option___redArg___lam__1___boxed as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_2349_, 0, v_short_2305_);
                        lean_closure_set(v___f_2349_, 1, v___x_2348_);
                        v___x_2350_ = lean_unsigned_to_nat(3);
                        v___x_2351_ =
                            l_String_Slice_Pos_nextn(v___x_2314_, v___x_2310_, v___x_2350_);
                        lean_dec_ref(v___x_2314_);
                        v___x_2352_ =
                            lean_string_utf8_extract(v_opt_2300_, v___x_2351_, v___x_2311_);
                        lean_dec(v___x_2351_);
                        lean_dec_ref(v_opt_2300_);
                        v___f_2353_ = lean_alloc_closure(
                            l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                            2,
                            1,
                        );
                        lean_closure_set(v___f_2353_, 0, v___x_2352_);
                        v___x_2354_ = lean_apply_2(v_modifyGet_2347_, lean_box(0), v___f_2353_);
                        v___x_2355_ = lean_apply_4(
                            v_toBind_2346_,
                            lean_box(0),
                            lean_box(0),
                            v___x_2354_,
                            v___f_2349_,
                        );
                        return v___x_2355_;
                    }
                } else {
                    lean_dec_ref(v___x_2314_);
                    lean_dec(v_longShort_2306_);
                    lean_dec_ref(v_opt_2300_);
                    lean_dec_ref(v_inst_2297_);
                    lean_dec_ref(v_inst_2296_);
                    v___x_2356_ = lean_box_uint32(v___x_2302_);
                    v___x_2357_ = lean_apply_1(v_short_2305_, v___x_2356_);
                    return v___x_2357_;
                }
            }
            3 => {
                v___x_2331_ = l_String_Slice_Pos_nextn(v___x_2314_, v___x_2310_, v___x_2317_);
                lean_dec_ref(v___x_2314_);
                v___x_2332_ = lean_box_uint32(v___x_2302_);
                v___f_2333_ = lean_alloc_closure(
                    l_Lake_option___redArg___lam__1___boxed as *mut core::ffi::c_void,
                    3,
                    2,
                );
                lean_closure_set(v___f_2333_, 0, v_short_2305_);
                lean_closure_set(v___f_2333_, 1, v___x_2332_);
                lean_inc(v___x_2331_);
                lean_inc_ref(v_opt_2300_);
                if v_isShared_2330_ == 0 {
                    lean_ctor_set(v___x_2329_, 2, v___x_2311_);
                    lean_ctor_set(v___x_2329_, 1, v___x_2331_);
                    lean_ctor_set(v___x_2329_, 0, v_opt_2300_);
                    v___x_2335_ = v___x_2329_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_opt_2300_);
                    lean_ctor_set(v_reuseFailAlloc_2342_, 1, v___x_2331_);
                    lean_ctor_set(v_reuseFailAlloc_2342_, 2, v___x_2311_);
                    v___x_2335_ = v_reuseFailAlloc_2342_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2336_ =
                    l_String_Slice_Pos_skipWhile___redArg(v___x_2335_, v___x_2310_, v___x_2326_);
                lean_dec_ref(v___x_2335_);
                v___x_2337_ = lean_nat_add(v___x_2331_, v___x_2336_);
                lean_dec(v___x_2336_);
                lean_dec(v___x_2331_);
                v___x_2338_ = lean_string_utf8_extract(v_opt_2300_, v___x_2337_, v___x_2311_);
                lean_dec(v___x_2337_);
                lean_dec_ref(v_opt_2300_);
                v___f_2339_ = lean_alloc_closure(
                    l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_2339_, 0, v___x_2338_);
                v___x_2340_ = lean_apply_2(v_modifyGet_2327_, lean_box(0), v___f_2339_);
                v___x_2341_ = lean_apply_4(
                    v_toBind_2325_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2340_,
                    v___f_2333_,
                );
                return v___x_2341_;
            }
            5 => {
                v___x_2364_ = lean_string_utf8_byte_size(v_opt_2300_);
                v___x_2365_ = lean_nat_dec_eq(v___y_2363_, v___x_2364_);
                if v___x_2365_ == 0 {
                    v_toBind_2366_ = lean_ctor_get(v_inst_2296_, 1);
                    lean_inc(v_toBind_2366_);
                    lean_dec_ref(v_inst_2296_);
                    v_modifyGet_2367_ = lean_ctor_get(v_inst_2297_, 2);
                    lean_inc(v_modifyGet_2367_);
                    lean_dec_ref(v_inst_2297_);
                    lean_inc(v___y_2363_);
                    lean_inc_ref(v_opt_2300_);
                    v___f_2368_ = lean_alloc_closure(
                        l_Lake_option___redArg___lam__5___boxed as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_2368_, 0, v_opt_2300_);
                    lean_closure_set(v___f_2368_, 1, v___y_2363_);
                    lean_closure_set(v___f_2368_, 2, v_long_2361_);
                    v___x_2369_ = lean_string_utf8_next_fast(v_opt_2300_, v___y_2363_);
                    lean_dec(v___y_2363_);
                    v___x_2370_ = lean_string_utf8_extract(v_opt_2300_, v___x_2369_, v___x_2364_);
                    lean_dec_ref(v_opt_2300_);
                    v___f_2371_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2371_, 0, v___x_2370_);
                    v___x_2372_ = lean_apply_2(v_modifyGet_2367_, lean_box(0), v___f_2371_);
                    v___x_2373_ = lean_apply_4(
                        v_toBind_2366_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2372_,
                        v___f_2368_,
                    );
                    return v___x_2373_;
                } else {
                    lean_dec(v___y_2363_);
                    lean_dec_ref(v_inst_2297_);
                    lean_dec_ref(v_inst_2296_);
                    v___x_2374_ = lean_apply_1(v_long_2361_, v_opt_2300_);
                    return v___x_2374_;
                }
            }
            6 => {
                v___x_2377_ = lean_string_utf8_byte_size(v_opt_2300_);
                v___x_2378_ = lean_nat_dec_eq(v___y_2376_, v___x_2377_);
                if v___x_2378_ == 0 {
                    v_toBind_2379_ = lean_ctor_get(v_inst_2296_, 1);
                    lean_inc_n(v_toBind_2379_, 2);
                    lean_dec_ref(v_inst_2296_);
                    v_modifyGet_2380_ = lean_ctor_get(v_inst_2297_, 2);
                    lean_inc_n(v_modifyGet_2380_, 2);
                    lean_dec_ref(v_inst_2297_);
                    lean_inc(v___y_2376_);
                    lean_inc_ref(v_opt_2300_);
                    v___f_2381_ = lean_alloc_closure(
                        l_Lake_option___redArg___lam__6___boxed as *mut core::ffi::c_void,
                        6,
                        5,
                    );
                    lean_closure_set(v___f_2381_, 0, v_opt_2300_);
                    lean_closure_set(v___f_2381_, 1, v___y_2376_);
                    lean_closure_set(v___f_2381_, 2, v_long_2361_);
                    lean_closure_set(v___f_2381_, 3, v_modifyGet_2380_);
                    lean_closure_set(v___f_2381_, 4, v_toBind_2379_);
                    v___x_2382_ = lean_string_utf8_next_fast(v_opt_2300_, v___y_2376_);
                    lean_dec(v___y_2376_);
                    v___x_2383_ = lean_string_utf8_extract(v_opt_2300_, v___x_2382_, v___x_2377_);
                    lean_dec_ref(v_opt_2300_);
                    v___f_2384_ = lean_alloc_closure(
                        l_Lake_shortOptionWithEq___redArg___lam__1 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2384_, 0, v___x_2383_);
                    v___x_2385_ = lean_apply_2(v_modifyGet_2380_, lean_box(0), v___f_2384_);
                    v___x_2386_ = lean_apply_4(
                        v_toBind_2379_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2385_,
                        v___f_2381_,
                    );
                    return v___x_2386_;
                } else {
                    lean_dec(v___y_2376_);
                    v_searcher_2387_ = lean_unsigned_to_nat(0);
                    v___x_2388_ = lean_box(0);
                    lean_inc_ref(v_opt_2300_);
                    v___f_2389_ = lean_alloc_closure(
                        l_Lake_longOptionOrSpace___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    lean_closure_set(v___f_2389_, 0, v___x_2377_);
                    lean_closure_set(v___f_2389_, 1, v_opt_2300_);
                    lean_closure_set(v___f_2389_, 2, v___x_2388_);
                    v___x_2390_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2389_,
                        v_searcher_2387_,
                        v___x_2388_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_2390_) == 0 {
                        v___y_2363_ = v___x_2377_;
                        state = 5;
                        continue;
                    } else {
                        v_val_2391_ = lean_ctor_get(v___x_2390_, 0);
                        lean_inc(v_val_2391_);
                        lean_dec_ref_known(v___x_2390_, 1);
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
    mut v_handle_2398_: *mut LeanObject,
    mut v_head_2399_: *mut LeanObject,
    mut v_____r_2400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2401_: *mut LeanObject = core::ptr::null_mut();
    v___x_2401_ = lean_apply_1(v_handle_2398_, v_head_2399_);
    return v___x_2401_;
}
pub unsafe fn l_Lake_processLeadingOption___redArg___lam__1(
    mut v___x_2402_: *mut LeanObject,
    mut v_head_2403_: *mut LeanObject,
    mut v___x_2404_: *mut LeanObject,
    mut v_it_2405_: *mut LeanObject,
    mut v_acc_2406_: *mut LeanObject,
    mut v_hP_2407_: *mut LeanObject,
    mut v_recur_2408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2409_: u8 = 0;
    v___x_2409_ = lean_nat_dec_eq(v_it_2405_, v___x_2402_);
    if v___x_2409_ == 0 {
        let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
        v___x_2410_ = lean_string_utf8_next_fast(v_head_2403_, v_it_2405_);
        v___x_2411_ = lean_nat_add(v_acc_2406_, v___x_2404_);
        v___x_2412_ = lean_apply_4(
            v_recur_2408_,
            v___x_2410_,
            v___x_2411_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_2412_;
    } else {
        lean_dec_ref(v_recur_2408_);
        lean_inc(v_acc_2406_);
        return v_acc_2406_;
    }
}
pub unsafe fn l_Lake_processLeadingOption___redArg___lam__1___boxed(
    mut v___x_2413_: *mut LeanObject,
    mut v_head_2414_: *mut LeanObject,
    mut v___x_2415_: *mut LeanObject,
    mut v_it_2416_: *mut LeanObject,
    mut v_acc_2417_: *mut LeanObject,
    mut v_hP_2418_: *mut LeanObject,
    mut v_recur_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2420_: *mut LeanObject = core::ptr::null_mut();
    v_res_2420_ = l_Lake_processLeadingOption___redArg___lam__1(
        v___x_2413_,
        v_head_2414_,
        v___x_2415_,
        v_it_2416_,
        v_acc_2417_,
        v_hP_2418_,
        v_recur_2419_,
    );
    lean_dec(v_acc_2417_);
    lean_dec(v_it_2416_);
    lean_dec(v___x_2415_);
    lean_dec_ref(v_head_2414_);
    lean_dec(v___x_2413_);
    return v_res_2420_;
}
pub unsafe fn l_Lake_processLeadingOption___redArg___lam__2(
    mut v_toPure_2421_: *mut LeanObject,
    mut v_handle_2422_: *mut LeanObject,
    mut v_set_2423_: *mut LeanObject,
    mut v_toBind_2424_: *mut LeanObject,
    mut v_____do__lift_2425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2432_: u8 = 0;
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: u32 = 0;
    let mut v___x_2446_: u32 = 0;
    let mut v___x_2447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2425_) == 0 {
                    lean_dec(v_toBind_2424_);
                    lean_dec(v_set_2423_);
                    lean_dec(v_handle_2422_);
                    v___x_2426_ = lean_box(0);
                    v___x_2427_ = lean_apply_2(v_toPure_2421_, lean_box(0), v___x_2426_);
                    return v___x_2427_;
                } else {
                    v_head_2428_ = lean_ctor_get(v_____do__lift_2425_, 0);
                    lean_inc_n(v_head_2428_, 4);
                    v_tail_2429_ = lean_ctor_get(v_____do__lift_2425_, 1);
                    lean_inc(v_tail_2429_);
                    lean_dec_ref_known(v_____do__lift_2425_, 2);
                    v___f_2430_ = lean_alloc_closure(
                        l_Lake_processLeadingOption___redArg___lam__0 as *mut core::ffi::c_void,
                        3,
                        2,
                    );
                    lean_closure_set(v___f_2430_, 0, v_handle_2422_);
                    lean_closure_set(v___f_2430_, 1, v_head_2428_);
                    v___x_2437_ = lean_unsigned_to_nat(1);
                    v___x_2438_ = lean_unsigned_to_nat(0);
                    v___x_2439_ = lean_string_utf8_byte_size(v_head_2428_);
                    v___f_2440_ = lean_alloc_closure(
                        l_Lake_processLeadingOption___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        7,
                        3,
                    );
                    lean_closure_set(v___f_2440_, 0, v___x_2439_);
                    lean_closure_set(v___f_2440_, 1, v_head_2428_);
                    lean_closure_set(v___f_2440_, 2, v___x_2437_);
                    v___x_2441_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2441_, 0, v_head_2428_);
                    lean_ctor_set(v___x_2441_, 1, v___x_2438_);
                    lean_ctor_set(v___x_2441_, 2, v___x_2439_);
                    v___x_2442_ = l_String_Slice_positions(v___x_2441_);
                    lean_dec_ref_known(v___x_2441_, 3);
                    v___x_2443_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2440_,
                        v___x_2442_,
                        v___x_2438_,
                        lean_box(0),
                    );
                    v___x_2444_ = lean_nat_dec_lt(v___x_2437_, v___x_2443_);
                    lean_dec(v___x_2443_);
                    if v___x_2444_ == 0 {
                        lean_dec(v_head_2428_);
                        v___y_2432_ = v___x_2444_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2445_ = lean_string_utf8_get(v_head_2428_, v___x_2438_);
                        lean_dec(v_head_2428_);
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
                    lean_dec_ref(v___f_2430_);
                    lean_dec(v_tail_2429_);
                    lean_dec(v_toBind_2424_);
                    lean_dec(v_set_2423_);
                    v___x_2433_ = lean_box(0);
                    v___x_2434_ = lean_apply_2(v_toPure_2421_, lean_box(0), v___x_2433_);
                    return v___x_2434_;
                } else {
                    lean_dec(v_toPure_2421_);
                    v___x_2435_ = lean_apply_1(v_set_2423_, v_tail_2429_);
                    v___x_2436_ = lean_apply_4(
                        v_toBind_2424_,
                        lean_box(0),
                        lean_box(0),
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
    mut v_inst_2448_: *mut LeanObject,
    mut v_inst_2449_: *mut LeanObject,
    mut v_handle_2450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2451_ = lean_ctor_get(v_inst_2448_, 0);
    lean_inc_ref(v_toApplicative_2451_);
    v_toBind_2452_ = lean_ctor_get(v_inst_2448_, 1);
    lean_inc_n(v_toBind_2452_, 2);
    lean_dec_ref(v_inst_2448_);
    v_get_2453_ = lean_ctor_get(v_inst_2449_, 0);
    lean_inc(v_get_2453_);
    v_set_2454_ = lean_ctor_get(v_inst_2449_, 1);
    lean_inc(v_set_2454_);
    lean_dec_ref(v_inst_2449_);
    v_toPure_2455_ = lean_ctor_get(v_toApplicative_2451_, 1);
    lean_inc(v_toPure_2455_);
    lean_dec_ref(v_toApplicative_2451_);
    v___f_2456_ = lean_alloc_closure(
        l_Lake_processLeadingOption___redArg___lam__2 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2456_, 0, v_toPure_2455_);
    lean_closure_set(v___f_2456_, 1, v_handle_2450_);
    lean_closure_set(v___f_2456_, 2, v_set_2454_);
    lean_closure_set(v___f_2456_, 3, v_toBind_2452_);
    v___x_2457_ = lean_apply_4(
        v_toBind_2452_,
        lean_box(0),
        lean_box(0),
        v_get_2453_,
        v___f_2456_,
    );
    return v___x_2457_;
}
pub unsafe fn l_Lake_processLeadingOption(
    mut v_m_2458_: *mut LeanObject,
    mut v_inst_2459_: *mut LeanObject,
    mut v_inst_2460_: *mut LeanObject,
    mut v_handle_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    v___x_2462_ = l_Lake_processLeadingOption___redArg(v_inst_2459_, v_inst_2460_, v_handle_2461_);
    return v___x_2462_;
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__1(
    mut v___x_2463_: *mut LeanObject,
    mut v_head_2464_: *mut LeanObject,
    mut v_it_2465_: *mut LeanObject,
    mut v_acc_2466_: *mut LeanObject,
    mut v_hP_2467_: *mut LeanObject,
    mut v_recur_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2469_: u8 = 0;
    v___x_2469_ = lean_nat_dec_eq(v_it_2465_, v___x_2463_);
    if v___x_2469_ == 0 {
        let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
        v___x_2470_ = lean_string_utf8_next_fast(v_head_2464_, v_it_2465_);
        v___x_2471_ = lean_unsigned_to_nat(1);
        v___x_2472_ = lean_nat_add(v_acc_2466_, v___x_2471_);
        v___x_2473_ = lean_apply_4(
            v_recur_2468_,
            v___x_2470_,
            v___x_2472_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_2473_;
    } else {
        lean_dec_ref(v_recur_2468_);
        lean_inc(v_acc_2466_);
        return v_acc_2466_;
    }
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__1___boxed(
    mut v___x_2474_: *mut LeanObject,
    mut v_head_2475_: *mut LeanObject,
    mut v_it_2476_: *mut LeanObject,
    mut v_acc_2477_: *mut LeanObject,
    mut v_hP_2478_: *mut LeanObject,
    mut v_recur_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2480_: *mut LeanObject = core::ptr::null_mut();
    v_res_2480_ = l_Lake_processLeadingOptions___redArg___lam__1(
        v___x_2474_,
        v_head_2475_,
        v_it_2476_,
        v_acc_2477_,
        v_hP_2478_,
        v_recur_2479_,
    );
    lean_dec(v_acc_2477_);
    lean_dec(v_it_2476_);
    lean_dec_ref(v_head_2475_);
    lean_dec(v___x_2474_);
    return v_res_2480_;
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__2(
    mut v_handle_2481_: *mut LeanObject,
    mut v_head_2482_: *mut LeanObject,
    mut v_toBind_2483_: *mut LeanObject,
    mut v___f_2484_: *mut LeanObject,
    mut v_____r_2485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    v___x_2486_ = lean_apply_1(v_handle_2481_, v_head_2482_);
    v___x_2487_ = lean_apply_4(
        v_toBind_2483_,
        lean_box(0),
        lean_box(0),
        v___x_2486_,
        v___f_2484_,
    );
    return v___x_2487_;
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__3(
    mut v_handle_2488_: *mut LeanObject,
    mut v_toBind_2489_: *mut LeanObject,
    mut v___f_2490_: *mut LeanObject,
    mut v_toPure_2491_: *mut LeanObject,
    mut v_set_2492_: *mut LeanObject,
    mut v___f_2493_: *mut LeanObject,
    mut v_____do__lift_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_len_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: u8 = 0;
    let mut v___x_2506_: u8 = 0;
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: u8 = 0;
    let mut v___x_2515_: u32 = 0;
    let mut v___x_2516_: u32 = 0;
    let mut v___x_2517_: u8 = 0;
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2494_) == 1 {
                    v_head_2495_ = lean_ctor_get(v_____do__lift_2494_, 0);
                    lean_inc_n(v_head_2495_, 4);
                    v_tail_2496_ = lean_ctor_get(v_____do__lift_2494_, 1);
                    lean_inc(v_tail_2496_);
                    lean_dec_ref_known(v_____do__lift_2494_, 2);
                    lean_inc(v_toBind_2489_);
                    v___f_2497_ = lean_alloc_closure(
                        l_Lake_processLeadingOptions___redArg___lam__2 as *mut core::ffi::c_void,
                        5,
                        4,
                    );
                    lean_closure_set(v___f_2497_, 0, v_handle_2488_);
                    lean_closure_set(v___f_2497_, 1, v_head_2495_);
                    lean_closure_set(v___f_2497_, 2, v_toBind_2489_);
                    lean_closure_set(v___f_2497_, 3, v___f_2490_);
                    v___x_2498_ = lean_unsigned_to_nat(0);
                    v___x_2499_ = lean_string_utf8_byte_size(v_head_2495_);
                    v___f_2500_ = lean_alloc_closure(
                        l_Lake_processLeadingOptions___redArg___lam__1___boxed
                            as *mut core::ffi::c_void,
                        6,
                        2,
                    );
                    lean_closure_set(v___f_2500_, 0, v___x_2499_);
                    lean_closure_set(v___f_2500_, 1, v_head_2495_);
                    v___x_2501_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2501_, 0, v_head_2495_);
                    lean_ctor_set(v___x_2501_, 1, v___x_2498_);
                    lean_ctor_set(v___x_2501_, 2, v___x_2499_);
                    v___x_2502_ = l_String_Slice_positions(v___x_2501_);
                    lean_dec_ref_known(v___x_2501_, 3);
                    v_len_2503_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2500_,
                        v___x_2502_,
                        v___x_2498_,
                        lean_box(0),
                    );
                    v___x_2513_ = lean_unsigned_to_nat(1);
                    v___x_2514_ = lean_nat_dec_lt(v___x_2513_, v_len_2503_);
                    if v___x_2514_ == 0 {
                        lean_dec(v_head_2495_);
                        v___y_2505_ = v___x_2514_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2515_ = lean_string_utf8_get(v_head_2495_, v___x_2498_);
                        lean_dec(v_head_2495_);
                        v___x_2516_ = 45;
                        v___x_2517_ = lean_uint32_dec_eq(v___x_2515_, v___x_2516_);
                        v___y_2505_ = v___x_2517_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_____do__lift_2494_);
                    lean_dec(v___f_2493_);
                    lean_dec(v_set_2492_);
                    lean_dec(v___f_2490_);
                    lean_dec(v_toBind_2489_);
                    lean_dec(v_handle_2488_);
                    v___x_2518_ = lean_box(0);
                    v___x_2519_ = lean_apply_2(v_toPure_2491_, lean_box(0), v___x_2518_);
                    return v___x_2519_;
                }
            }
            1 => {
                if v___y_2505_ == 0 {
                    lean_dec_ref(v___f_2497_);
                    v___x_2506_ = lean_nat_dec_eq(v_len_2503_, v___x_2498_);
                    lean_dec(v_len_2503_);
                    if v___x_2506_ == 0 {
                        lean_dec(v_tail_2496_);
                        lean_dec(v___f_2493_);
                        lean_dec(v_set_2492_);
                        lean_dec(v_toBind_2489_);
                        v___x_2507_ = lean_box(0);
                        v___x_2508_ = lean_apply_2(v_toPure_2491_, lean_box(0), v___x_2507_);
                        return v___x_2508_;
                    } else {
                        lean_dec(v_toPure_2491_);
                        v___x_2509_ = lean_apply_1(v_set_2492_, v_tail_2496_);
                        v___x_2510_ = lean_apply_4(
                            v_toBind_2489_,
                            lean_box(0),
                            lean_box(0),
                            v___x_2509_,
                            v___f_2493_,
                        );
                        return v___x_2510_;
                    }
                } else {
                    lean_dec(v_len_2503_);
                    lean_dec(v___f_2493_);
                    lean_dec(v_toPure_2491_);
                    v___x_2511_ = lean_apply_1(v_set_2492_, v_tail_2496_);
                    v___x_2512_ = lean_apply_4(
                        v_toBind_2489_,
                        lean_box(0),
                        lean_box(0),
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
    mut v_inst_2520_: *mut LeanObject,
    mut v_inst_2521_: *mut LeanObject,
    mut v_handle_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_set_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2523_ = lean_ctor_get(v_inst_2520_, 0);
    v_toBind_2524_ = lean_ctor_get(v_inst_2520_, 1);
    lean_inc_n(v_toBind_2524_, 2);
    v_get_2525_ = lean_ctor_get(v_inst_2521_, 0);
    lean_inc(v_get_2525_);
    v_set_2526_ = lean_ctor_get(v_inst_2521_, 1);
    lean_inc(v_set_2526_);
    v_toPure_2527_ = lean_ctor_get(v_toApplicative_2523_, 1);
    lean_inc(v_toPure_2527_);
    lean_inc(v_handle_2522_);
    v___f_2528_ = lean_alloc_closure(
        l_Lake_processLeadingOptions___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2528_, 0, v_inst_2520_);
    lean_closure_set(v___f_2528_, 1, v_inst_2521_);
    lean_closure_set(v___f_2528_, 2, v_handle_2522_);
    lean_inc_ref(v___f_2528_);
    v___f_2529_ = lean_alloc_closure(
        l_Lake_processLeadingOptions___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2529_, 0, v_handle_2522_);
    lean_closure_set(v___f_2529_, 1, v_toBind_2524_);
    lean_closure_set(v___f_2529_, 2, v___f_2528_);
    lean_closure_set(v___f_2529_, 3, v_toPure_2527_);
    lean_closure_set(v___f_2529_, 4, v_set_2526_);
    lean_closure_set(v___f_2529_, 5, v___f_2528_);
    v___x_2530_ = lean_apply_4(
        v_toBind_2524_,
        lean_box(0),
        lean_box(0),
        v_get_2525_,
        v___f_2529_,
    );
    return v___x_2530_;
}
pub unsafe fn l_Lake_processLeadingOptions___redArg___lam__0(
    mut v_inst_2531_: *mut LeanObject,
    mut v_inst_2532_: *mut LeanObject,
    mut v_handle_2533_: *mut LeanObject,
    mut v_____r_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    v___x_2535_ = l_Lake_processLeadingOptions___redArg(v_inst_2531_, v_inst_2532_, v_handle_2533_);
    return v___x_2535_;
}
pub unsafe fn l_Lake_processLeadingOptions(
    mut v_m_2536_: *mut LeanObject,
    mut v_inst_2537_: *mut LeanObject,
    mut v_inst_2538_: *mut LeanObject,
    mut v_handle_2539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    v___x_2540_ = l_Lake_processLeadingOptions___redArg(v_inst_2537_, v_inst_2538_, v_handle_2539_);
    return v___x_2540_;
}
pub unsafe fn l_Lake_collectArgs___redArg___lam__0(
    mut v_x_2541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2548_: u8 = 0;
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2553_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2541_) == 0 {
                    v___x_2542_ = lean_box(0);
                    v___x_2543_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2543_, 0, v___x_2542_);
                    lean_ctor_set(v___x_2543_, 1, v_x_2541_);
                    return v___x_2543_;
                } else {
                    v_head_2544_ = lean_ctor_get(v_x_2541_, 0);
                    v_tail_2545_ = lean_ctor_get(v_x_2541_, 1);
                    v_isSharedCheck_2553_ = (!lean_is_exclusive(v_x_2541_)) as u8;
                    if v_isSharedCheck_2553_ == 0 {
                        v___x_2547_ = v_x_2541_;
                        v_isShared_2548_ = v_isSharedCheck_2553_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2545_);
                        lean_inc(v_head_2544_);
                        lean_dec(v_x_2541_);
                        v___x_2547_ = lean_box(0);
                        v_isShared_2548_ = v_isSharedCheck_2553_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2549_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2549_, 0, v_head_2544_);
                if v_isShared_2548_ == 0 {
                    lean_ctor_set_tag(v___x_2547_, 0);
                    lean_ctor_set(v___x_2547_, 0, v___x_2549_);
                    v___x_2551_ = v___x_2547_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2552_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2549_);
                    lean_ctor_set(v_reuseFailAlloc_2552_, 1, v_tail_2545_);
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
    mut v___x_2554_: *mut LeanObject,
    mut v_val_2555_: *mut LeanObject,
    mut v_it_2556_: *mut LeanObject,
    mut v_acc_2557_: *mut LeanObject,
    mut v_hP_2558_: *mut LeanObject,
    mut v_recur_2559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2560_: u8 = 0;
    v___x_2560_ = lean_nat_dec_eq(v_it_2556_, v___x_2554_);
    if v___x_2560_ == 0 {
        let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
        v___x_2561_ = lean_string_utf8_next_fast(v_val_2555_, v_it_2556_);
        v___x_2562_ = lean_unsigned_to_nat(1);
        v___x_2563_ = lean_nat_add(v_acc_2557_, v___x_2562_);
        v___x_2564_ = lean_apply_4(
            v_recur_2559_,
            v___x_2561_,
            v___x_2563_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_2564_;
    } else {
        lean_dec_ref(v_recur_2559_);
        lean_inc(v_acc_2557_);
        return v_acc_2557_;
    }
}
pub unsafe fn l_Lake_collectArgs___redArg___lam__2___boxed(
    mut v___x_2565_: *mut LeanObject,
    mut v_val_2566_: *mut LeanObject,
    mut v_it_2567_: *mut LeanObject,
    mut v_acc_2568_: *mut LeanObject,
    mut v_hP_2569_: *mut LeanObject,
    mut v_recur_2570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2571_: *mut LeanObject = core::ptr::null_mut();
    v_res_2571_ = l_Lake_collectArgs___redArg___lam__2(
        v___x_2565_,
        v_val_2566_,
        v_it_2567_,
        v_acc_2568_,
        v_hP_2569_,
        v_recur_2570_,
    );
    lean_dec(v_acc_2568_);
    lean_dec(v_it_2567_);
    lean_dec_ref(v_val_2566_);
    lean_dec(v___x_2565_);
    return v_res_2571_;
}
pub unsafe fn l_Lake_collectArgs___redArg___lam__3(
    mut v_args_2573_: *mut LeanObject,
    mut v_inst_2574_: *mut LeanObject,
    mut v_inst_2575_: *mut LeanObject,
    mut v_option_2576_: *mut LeanObject,
    mut v_toBind_2577_: *mut LeanObject,
    mut v___f_2578_: *mut LeanObject,
    mut v_toPure_2579_: *mut LeanObject,
    mut v_____do__lift_2580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_len_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2589_: u8 = 0;
    let mut v___x_2590_: u8 = 0;
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: u8 = 0;
    let mut v___x_2598_: u32 = 0;
    let mut v___x_2599_: u32 = 0;
    let mut v___x_2600_: u8 = 0;
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2580_) == 1 {
                    lean_dec(v_toPure_2579_);
                    v_val_2581_ = lean_ctor_get(v_____do__lift_2580_, 0);
                    lean_inc_n(v_val_2581_, 3);
                    lean_dec_ref_known(v_____do__lift_2580_, 1);
                    v___x_2582_ = lean_unsigned_to_nat(0);
                    v___x_2583_ = lean_string_utf8_byte_size(v_val_2581_);
                    v___f_2584_ = lean_alloc_closure(
                        l_Lake_collectArgs___redArg___lam__2___boxed as *mut core::ffi::c_void,
                        6,
                        2,
                    );
                    lean_closure_set(v___f_2584_, 0, v___x_2583_);
                    lean_closure_set(v___f_2584_, 1, v_val_2581_);
                    v___x_2585_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_2585_, 0, v_val_2581_);
                    lean_ctor_set(v___x_2585_, 1, v___x_2582_);
                    lean_ctor_set(v___x_2585_, 2, v___x_2583_);
                    v___x_2586_ = l_String_Slice_positions(v___x_2585_);
                    lean_dec_ref_known(v___x_2585_, 3);
                    v_len_2587_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2584_,
                        v___x_2586_,
                        v___x_2582_,
                        lean_box(0),
                    );
                    v___x_2596_ = lean_unsigned_to_nat(1);
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
                    lean_dec(v_____do__lift_2580_);
                    lean_dec(v___f_2578_);
                    lean_dec(v_toBind_2577_);
                    lean_dec(v_option_2576_);
                    lean_dec_ref(v_inst_2575_);
                    lean_dec_ref(v_inst_2574_);
                    v___x_2601_ = lean_apply_2(v_toPure_2579_, lean_box(0), v_args_2573_);
                    return v___x_2601_;
                }
            }
            1 => {
                if v___y_2589_ == 0 {
                    lean_dec(v___f_2578_);
                    lean_dec(v_toBind_2577_);
                    v___x_2590_ = lean_nat_dec_eq(v_len_2587_, v___x_2582_);
                    lean_dec(v_len_2587_);
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
                        lean_dec(v_val_2581_);
                        v___x_2593_ = l_Lake_collectArgs___redArg(
                            v_inst_2574_,
                            v_inst_2575_,
                            v_option_2576_,
                            v_args_2573_,
                        );
                        return v___x_2593_;
                    }
                } else {
                    lean_dec(v_len_2587_);
                    lean_dec_ref(v_inst_2575_);
                    lean_dec_ref(v_inst_2574_);
                    lean_dec_ref(v_args_2573_);
                    v___x_2594_ = lean_apply_1(v_option_2576_, v_val_2581_);
                    v___x_2595_ = lean_apply_4(
                        v_toBind_2577_,
                        lean_box(0),
                        lean_box(0),
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
    mut v_inst_2602_: *mut LeanObject,
    mut v_inst_2603_: *mut LeanObject,
    mut v_option_2604_: *mut LeanObject,
    mut v_args_2605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2606_ = lean_ctor_get(v_inst_2602_, 0);
    v_toBind_2607_ = lean_ctor_get(v_inst_2602_, 1);
    lean_inc_n(v_toBind_2607_, 2);
    v_modifyGet_2608_ = lean_ctor_get(v_inst_2603_, 2);
    v_toPure_2609_ = lean_ctor_get(v_toApplicative_2606_, 1);
    lean_inc(v_toPure_2609_);
    v___f_2610_ = l_Lake_collectArgs___redArg___closed__0;
    lean_inc_ref(v_args_2605_);
    lean_inc(v_option_2604_);
    lean_inc_ref(v_inst_2603_);
    lean_inc_ref(v_inst_2602_);
    v___f_2611_ = lean_alloc_closure(
        l_Lake_collectArgs___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2611_, 0, v_inst_2602_);
    lean_closure_set(v___f_2611_, 1, v_inst_2603_);
    lean_closure_set(v___f_2611_, 2, v_option_2604_);
    lean_closure_set(v___f_2611_, 3, v_args_2605_);
    lean_inc(v_modifyGet_2608_);
    v___x_2612_ = lean_apply_2(v_modifyGet_2608_, lean_box(0), v___f_2610_);
    v___f_2613_ = lean_alloc_closure(
        l_Lake_collectArgs___redArg___lam__3 as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2613_, 0, v_args_2605_);
    lean_closure_set(v___f_2613_, 1, v_inst_2602_);
    lean_closure_set(v___f_2613_, 2, v_inst_2603_);
    lean_closure_set(v___f_2613_, 3, v_option_2604_);
    lean_closure_set(v___f_2613_, 4, v_toBind_2607_);
    lean_closure_set(v___f_2613_, 5, v___f_2611_);
    lean_closure_set(v___f_2613_, 6, v_toPure_2609_);
    v___x_2614_ = lean_apply_4(
        v_toBind_2607_,
        lean_box(0),
        lean_box(0),
        v___x_2612_,
        v___f_2613_,
    );
    return v___x_2614_;
}
pub unsafe fn l_Lake_collectArgs___redArg___lam__1(
    mut v_inst_2615_: *mut LeanObject,
    mut v_inst_2616_: *mut LeanObject,
    mut v_option_2617_: *mut LeanObject,
    mut v_args_2618_: *mut LeanObject,
    mut v_____r_2619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    v___x_2620_ =
        l_Lake_collectArgs___redArg(v_inst_2615_, v_inst_2616_, v_option_2617_, v_args_2618_);
    return v___x_2620_;
}
pub unsafe fn l_Lake_collectArgs(
    mut v_m_2621_: *mut LeanObject,
    mut v_inst_2622_: *mut LeanObject,
    mut v_inst_2623_: *mut LeanObject,
    mut v_option_2624_: *mut LeanObject,
    mut v_args_2625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    v___x_2626_ =
        l_Lake_collectArgs___redArg(v_inst_2622_, v_inst_2623_, v_option_2624_, v_args_2625_);
    return v___x_2626_;
}
pub unsafe fn l_Lake_processOptions___redArg___lam__0(
    mut v_inst_2627_: *mut LeanObject,
    mut v_____do__lift_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_set_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    v_set_2629_ = lean_ctor_get(v_inst_2627_, 1);
    lean_inc(v_set_2629_);
    lean_dec_ref(v_inst_2627_);
    v___x_2630_ = lean_array_to_list(v_____do__lift_2628_);
    v___x_2631_ = lean_apply_1(v_set_2629_, v___x_2630_);
    return v___x_2631_;
}
pub unsafe fn l_Lake_processOptions___redArg(
    mut v_inst_2634_: *mut LeanObject,
    mut v_inst_2635_: *mut LeanObject,
    mut v_handle_2636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2637_ = lean_ctor_get(v_inst_2634_, 1);
    lean_inc(v_toBind_2637_);
    lean_inc_ref(v_inst_2635_);
    v___f_2638_ = lean_alloc_closure(
        l_Lake_processOptions___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2638_, 0, v_inst_2635_);
    v___x_2639_ = l_Lake_processOptions___redArg___closed__0;
    v___x_2640_ =
        l_Lake_collectArgs___redArg(v_inst_2634_, v_inst_2635_, v_handle_2636_, v___x_2639_);
    v___x_2641_ = lean_apply_4(
        v_toBind_2637_,
        lean_box(0),
        lean_box(0),
        v___x_2640_,
        v___f_2638_,
    );
    return v___x_2641_;
}
pub unsafe fn l_Lake_processOptions(
    mut v_m_2642_: *mut LeanObject,
    mut v_inst_2643_: *mut LeanObject,
    mut v_inst_2644_: *mut LeanObject,
    mut v_handle_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2646_ = lean_ctor_get(v_inst_2643_, 1);
    lean_inc(v_toBind_2646_);
    lean_inc_ref(v_inst_2644_);
    v___f_2647_ = lean_alloc_closure(
        l_Lake_processOptions___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2647_, 0, v_inst_2644_);
    v___x_2648_ = l_Lake_processOptions___redArg___closed__0;
    v___x_2649_ =
        l_Lake_collectArgs___redArg(v_inst_2643_, v_inst_2644_, v_handle_2645_, v___x_2648_);
    v___x_2650_ = lean_apply_4(
        v_toBind_2646_,
        lean_box(0),
        lean_box(0),
        v___x_2649_,
        v___f_2647_,
    );
    return v___x_2650_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Cli(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Cli(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Cli(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Cli(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Cli(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Cli(builtin);
}
