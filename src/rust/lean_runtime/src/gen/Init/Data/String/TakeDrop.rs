// Lean compiler output
// Module: Init.Data.String.TakeDrop
// Imports: Init.Data.String.Substring
use crate::r#gen::Init::Data::Char::Basic::l_Char_isWhitespace___boxed;
use crate::r#gen::Init::Data::String::Basic::{l_String_Slice_Pos_nextn, l_String_Slice_pos_x21};
use crate::r#gen::Init::Data::String::FindPos::{l_String_Slice_Pos_prevn, l_String_Slice_posLE};
use crate::r#gen::Init::Data::String::Pattern::Pred::{
    l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool,
    l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool,
};
use crate::r#gen::Init::Data::String::Slice::{
    l_String_Slice_Pos_revSkipWhile___redArg, l_String_Slice_Pos_skipWhile___redArg,
    l_String_Slice_dropPrefix___redArg, l_String_Slice_dropSuffix___redArg,
    l_String_Slice_toString, l_String_Slice_trimAscii,
};
use crate::r#gen::Init::Data::String::Substring::{
    initialize_Init_Data_String_Substring, l_Substring_Raw_takeWhileAux,
    runtime_initialize_Init_Data_String_Substring,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_get_fast,
    lean_string_utf8_next, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_utf8_byte_size, lean_uint32_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_box_uint32, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_uint32,
    lean_unsigned_to_nat,
};
pub static l_String_trimAsciiEnd___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
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
static mut l_String_trimAsciiEnd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_trimAsciiEnd___closed__0_value) as *mut LeanObject;
static mut l_String_trimAsciiEnd___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_trimAsciiEnd___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_String_trimAsciiStart___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_trimAsciiStart___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_String_drop(
    mut v_s_1235_: *mut LeanObject,
    mut v_n_1236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    v___x_1237_ = lean_unsigned_to_nat(0);
    v___x_1238_ = lean_string_utf8_byte_size(v_s_1235_);
    lean_inc_ref(v_s_1235_);
    v___x_1239_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1239_, 0, v_s_1235_);
    lean_ctor_set(v___x_1239_, 1, v___x_1237_);
    lean_ctor_set(v___x_1239_, 2, v___x_1238_);
    v___x_1240_ = l_String_Slice_Pos_nextn(v___x_1239_, v___x_1237_, v_n_1236_);
    lean_dec_ref_known(v___x_1239_, 3);
    v___x_1241_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1241_, 0, v_s_1235_);
    lean_ctor_set(v___x_1241_, 1, v___x_1240_);
    lean_ctor_set(v___x_1241_, 2, v___x_1238_);
    return v___x_1241_;
}
pub unsafe fn lean_string_drop(
    mut v_s_1242_: *mut LeanObject,
    mut v_n_1243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    v___x_1244_ = lean_unsigned_to_nat(0);
    v___x_1245_ = lean_string_utf8_byte_size(v_s_1242_);
    lean_inc_ref(v_s_1242_);
    v___x_1246_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1246_, 0, v_s_1242_);
    lean_ctor_set(v___x_1246_, 1, v___x_1244_);
    lean_ctor_set(v___x_1246_, 2, v___x_1245_);
    v___x_1247_ = l_String_Slice_Pos_nextn(v___x_1246_, v___x_1244_, v_n_1243_);
    lean_dec_ref_known(v___x_1246_, 3);
    v___x_1248_ = lean_string_utf8_extract(v_s_1242_, v___x_1247_, v___x_1245_);
    lean_dec(v___x_1247_);
    lean_dec_ref(v_s_1242_);
    return v___x_1248_;
}
pub unsafe fn l_String_dropEnd(
    mut v_s_1249_: *mut LeanObject,
    mut v_n_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    v___x_1251_ = lean_unsigned_to_nat(0);
    v___x_1252_ = lean_string_utf8_byte_size(v_s_1249_);
    lean_inc_ref(v_s_1249_);
    v___x_1253_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1253_, 0, v_s_1249_);
    lean_ctor_set(v___x_1253_, 1, v___x_1251_);
    lean_ctor_set(v___x_1253_, 2, v___x_1252_);
    v___x_1254_ = l_String_Slice_Pos_prevn(v___x_1253_, v___x_1252_, v_n_1250_);
    lean_dec_ref_known(v___x_1253_, 3);
    v___x_1255_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1255_, 0, v_s_1249_);
    lean_ctor_set(v___x_1255_, 1, v___x_1251_);
    lean_ctor_set(v___x_1255_, 2, v___x_1254_);
    return v___x_1255_;
}
pub unsafe fn l_String_dropRight(
    mut v_s_1256_: *mut LeanObject,
    mut v_n_1257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    v___x_1258_ = lean_unsigned_to_nat(0);
    v___x_1259_ = lean_string_utf8_byte_size(v_s_1256_);
    lean_inc_ref(v_s_1256_);
    v___x_1260_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1260_, 0, v_s_1256_);
    lean_ctor_set(v___x_1260_, 1, v___x_1258_);
    lean_ctor_set(v___x_1260_, 2, v___x_1259_);
    v___x_1261_ = l_String_Slice_Pos_prevn(v___x_1260_, v___x_1259_, v_n_1257_);
    lean_dec_ref_known(v___x_1260_, 3);
    v___x_1262_ = lean_string_utf8_extract(v_s_1256_, v___x_1258_, v___x_1261_);
    lean_dec(v___x_1261_);
    lean_dec_ref(v_s_1256_);
    return v___x_1262_;
}
pub unsafe fn l_String_Slice_dropRight(
    mut v_s_1263_: *mut LeanObject,
    mut v_n_1264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1277_: u8 = 0;
    let mut v_unused_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1265_ = lean_ctor_get(v_s_1263_, 0);
                lean_inc_ref(v_str_1265_);
                v_startInclusive_1266_ = lean_ctor_get(v_s_1263_, 1);
                lean_inc(v_startInclusive_1266_);
                v_endExclusive_1267_ = lean_ctor_get(v_s_1263_, 2);
                v___x_1268_ = lean_nat_sub(v_endExclusive_1267_, v_startInclusive_1266_);
                v___x_1269_ = l_String_Slice_Pos_prevn(v_s_1263_, v___x_1268_, v_n_1264_);
                v_isSharedCheck_1277_ = (!lean_is_exclusive(v_s_1263_)) as u8;
                if v_isSharedCheck_1277_ == 0 {
                    v_unused_1278_ = lean_ctor_get(v_s_1263_, 2);
                    lean_dec(v_unused_1278_);
                    v_unused_1279_ = lean_ctor_get(v_s_1263_, 1);
                    lean_dec(v_unused_1279_);
                    v_unused_1280_ = lean_ctor_get(v_s_1263_, 0);
                    lean_dec(v_unused_1280_);
                    v___x_1271_ = v_s_1263_;
                    v_isShared_1272_ = v_isSharedCheck_1277_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_1263_);
                    v___x_1271_ = lean_box(0);
                    v_isShared_1272_ = v_isSharedCheck_1277_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1273_ = lean_nat_add(v_startInclusive_1266_, v___x_1269_);
                lean_dec(v___x_1269_);
                if v_isShared_1272_ == 0 {
                    lean_ctor_set(v___x_1271_, 2, v___x_1273_);
                    v___x_1275_ = v___x_1271_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1276_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_str_1265_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_startInclusive_1266_);
                    lean_ctor_set(v_reuseFailAlloc_1276_, 2, v___x_1273_);
                    v___x_1275_ = v_reuseFailAlloc_1276_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1275_;
            }
            _ => {}
        }
    }
}
pub unsafe fn lean_string_dropright(
    mut v_s_1281_: *mut LeanObject,
    mut v_n_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    v___x_1283_ = lean_unsigned_to_nat(0);
    v___x_1284_ = lean_string_utf8_byte_size(v_s_1281_);
    lean_inc_ref(v_s_1281_);
    v___x_1285_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1285_, 0, v_s_1281_);
    lean_ctor_set(v___x_1285_, 1, v___x_1283_);
    lean_ctor_set(v___x_1285_, 2, v___x_1284_);
    v___x_1286_ = l_String_Slice_Pos_prevn(v___x_1285_, v___x_1284_, v_n_1282_);
    lean_dec_ref_known(v___x_1285_, 3);
    v___x_1287_ = lean_string_utf8_extract(v_s_1281_, v___x_1283_, v___x_1286_);
    lean_dec(v___x_1286_);
    lean_dec_ref(v_s_1281_);
    return v___x_1287_;
}
pub unsafe fn l_String_take(
    mut v_s_1288_: *mut LeanObject,
    mut v_n_1289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    v___x_1290_ = lean_unsigned_to_nat(0);
    v___x_1291_ = lean_string_utf8_byte_size(v_s_1288_);
    lean_inc_ref(v_s_1288_);
    v___x_1292_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1292_, 0, v_s_1288_);
    lean_ctor_set(v___x_1292_, 1, v___x_1290_);
    lean_ctor_set(v___x_1292_, 2, v___x_1291_);
    v___x_1293_ = l_String_Slice_Pos_nextn(v___x_1292_, v___x_1290_, v_n_1289_);
    lean_dec_ref_known(v___x_1292_, 3);
    v___x_1294_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1294_, 0, v_s_1288_);
    lean_ctor_set(v___x_1294_, 1, v___x_1290_);
    lean_ctor_set(v___x_1294_, 2, v___x_1293_);
    return v___x_1294_;
}
pub unsafe fn l_String_takeEnd(
    mut v_s_1295_: *mut LeanObject,
    mut v_n_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    v___x_1297_ = lean_unsigned_to_nat(0);
    v___x_1298_ = lean_string_utf8_byte_size(v_s_1295_);
    lean_inc_ref(v_s_1295_);
    v___x_1299_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1299_, 0, v_s_1295_);
    lean_ctor_set(v___x_1299_, 1, v___x_1297_);
    lean_ctor_set(v___x_1299_, 2, v___x_1298_);
    v___x_1300_ = l_String_Slice_Pos_prevn(v___x_1299_, v___x_1298_, v_n_1296_);
    lean_dec_ref_known(v___x_1299_, 3);
    v___x_1301_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1301_, 0, v_s_1295_);
    lean_ctor_set(v___x_1301_, 1, v___x_1300_);
    lean_ctor_set(v___x_1301_, 2, v___x_1298_);
    return v___x_1301_;
}
pub unsafe fn l_String_takeRight(
    mut v_s_1302_: *mut LeanObject,
    mut v_n_1303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    v___x_1304_ = lean_unsigned_to_nat(0);
    v___x_1305_ = lean_string_utf8_byte_size(v_s_1302_);
    lean_inc_ref(v_s_1302_);
    v___x_1306_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1306_, 0, v_s_1302_);
    lean_ctor_set(v___x_1306_, 1, v___x_1304_);
    lean_ctor_set(v___x_1306_, 2, v___x_1305_);
    v___x_1307_ = l_String_Slice_Pos_prevn(v___x_1306_, v___x_1305_, v_n_1303_);
    lean_dec_ref_known(v___x_1306_, 3);
    v___x_1308_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1308_, 0, v_s_1302_);
    lean_ctor_set(v___x_1308_, 1, v___x_1307_);
    lean_ctor_set(v___x_1308_, 2, v___x_1305_);
    v___x_1309_ = l_String_Slice_toString(v___x_1308_);
    lean_dec_ref_known(v___x_1308_, 3);
    return v___x_1309_;
}
pub unsafe fn l_String_Slice_takeRight(
    mut v_s_1310_: *mut LeanObject,
    mut v_n_1311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1324_: u8 = 0;
    let mut v_unused_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1312_ = lean_ctor_get(v_s_1310_, 0);
                lean_inc_ref(v_str_1312_);
                v_startInclusive_1313_ = lean_ctor_get(v_s_1310_, 1);
                lean_inc(v_startInclusive_1313_);
                v_endExclusive_1314_ = lean_ctor_get(v_s_1310_, 2);
                lean_inc(v_endExclusive_1314_);
                v___x_1315_ = lean_nat_sub(v_endExclusive_1314_, v_startInclusive_1313_);
                v___x_1316_ = l_String_Slice_Pos_prevn(v_s_1310_, v___x_1315_, v_n_1311_);
                v_isSharedCheck_1324_ = (!lean_is_exclusive(v_s_1310_)) as u8;
                if v_isSharedCheck_1324_ == 0 {
                    v_unused_1325_ = lean_ctor_get(v_s_1310_, 2);
                    lean_dec(v_unused_1325_);
                    v_unused_1326_ = lean_ctor_get(v_s_1310_, 1);
                    lean_dec(v_unused_1326_);
                    v_unused_1327_ = lean_ctor_get(v_s_1310_, 0);
                    lean_dec(v_unused_1327_);
                    v___x_1318_ = v_s_1310_;
                    v_isShared_1319_ = v_isSharedCheck_1324_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_1310_);
                    v___x_1318_ = lean_box(0);
                    v_isShared_1319_ = v_isSharedCheck_1324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1320_ = lean_nat_add(v_startInclusive_1313_, v___x_1316_);
                lean_dec(v___x_1316_);
                lean_dec(v_startInclusive_1313_);
                if v_isShared_1319_ == 0 {
                    lean_ctor_set(v___x_1318_, 1, v___x_1320_);
                    v___x_1322_ = v___x_1318_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_str_1312_);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1320_);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_endExclusive_1314_);
                    v___x_1322_ = v_reuseFailAlloc_1323_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1322_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_takeWhile___redArg(
    mut v_s_1328_: *mut LeanObject,
    mut v_inst_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    v___x_1330_ = lean_unsigned_to_nat(0);
    v___x_1331_ = lean_string_utf8_byte_size(v_s_1328_);
    lean_inc_ref(v_s_1328_);
    v___x_1332_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1332_, 0, v_s_1328_);
    lean_ctor_set(v___x_1332_, 1, v___x_1330_);
    lean_ctor_set(v___x_1332_, 2, v___x_1331_);
    v___x_1333_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1332_, v___x_1330_, v_inst_1329_);
    lean_dec_ref_known(v___x_1332_, 3);
    v___x_1334_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1334_, 0, v_s_1328_);
    lean_ctor_set(v___x_1334_, 1, v___x_1330_);
    lean_ctor_set(v___x_1334_, 2, v___x_1333_);
    return v___x_1334_;
}
pub unsafe fn l_String_takeWhile(
    mut v_00_u03c1_1335_: *mut LeanObject,
    mut v_s_1336_: *mut LeanObject,
    mut v_pat_1337_: *mut LeanObject,
    mut v_inst_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    v___x_1339_ = lean_unsigned_to_nat(0);
    v___x_1340_ = lean_string_utf8_byte_size(v_s_1336_);
    lean_inc_ref(v_s_1336_);
    v___x_1341_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1341_, 0, v_s_1336_);
    lean_ctor_set(v___x_1341_, 1, v___x_1339_);
    lean_ctor_set(v___x_1341_, 2, v___x_1340_);
    v___x_1342_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1341_, v___x_1339_, v_inst_1338_);
    lean_dec_ref_known(v___x_1341_, 3);
    v___x_1343_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1343_, 0, v_s_1336_);
    lean_ctor_set(v___x_1343_, 1, v___x_1339_);
    lean_ctor_set(v___x_1343_, 2, v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn l_String_takeWhile___boxed(
    mut v_00_u03c1_1344_: *mut LeanObject,
    mut v_s_1345_: *mut LeanObject,
    mut v_pat_1346_: *mut LeanObject,
    mut v_inst_1347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1348_: *mut LeanObject = core::ptr::null_mut();
    v_res_1348_ = l_String_takeWhile(v_00_u03c1_1344_, v_s_1345_, v_pat_1346_, v_inst_1347_);
    lean_dec(v_pat_1346_);
    return v_res_1348_;
}
pub unsafe fn l_String_dropWhile___redArg(
    mut v_s_1349_: *mut LeanObject,
    mut v_inst_1350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    v___x_1351_ = lean_unsigned_to_nat(0);
    v___x_1352_ = lean_string_utf8_byte_size(v_s_1349_);
    lean_inc_ref(v_s_1349_);
    v___x_1353_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1353_, 0, v_s_1349_);
    lean_ctor_set(v___x_1353_, 1, v___x_1351_);
    lean_ctor_set(v___x_1353_, 2, v___x_1352_);
    v___x_1354_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1353_, v___x_1351_, v_inst_1350_);
    lean_dec_ref_known(v___x_1353_, 3);
    v___x_1355_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1355_, 0, v_s_1349_);
    lean_ctor_set(v___x_1355_, 1, v___x_1354_);
    lean_ctor_set(v___x_1355_, 2, v___x_1352_);
    return v___x_1355_;
}
pub unsafe fn l_String_dropWhile(
    mut v_00_u03c1_1356_: *mut LeanObject,
    mut v_s_1357_: *mut LeanObject,
    mut v_pat_1358_: *mut LeanObject,
    mut v_inst_1359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    v___x_1360_ = lean_unsigned_to_nat(0);
    v___x_1361_ = lean_string_utf8_byte_size(v_s_1357_);
    lean_inc_ref(v_s_1357_);
    v___x_1362_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1362_, 0, v_s_1357_);
    lean_ctor_set(v___x_1362_, 1, v___x_1360_);
    lean_ctor_set(v___x_1362_, 2, v___x_1361_);
    v___x_1363_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1362_, v___x_1360_, v_inst_1359_);
    lean_dec_ref_known(v___x_1362_, 3);
    v___x_1364_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1364_, 0, v_s_1357_);
    lean_ctor_set(v___x_1364_, 1, v___x_1363_);
    lean_ctor_set(v___x_1364_, 2, v___x_1361_);
    return v___x_1364_;
}
pub unsafe fn l_String_dropWhile___boxed(
    mut v_00_u03c1_1365_: *mut LeanObject,
    mut v_s_1366_: *mut LeanObject,
    mut v_pat_1367_: *mut LeanObject,
    mut v_inst_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1369_: *mut LeanObject = core::ptr::null_mut();
    v_res_1369_ = l_String_dropWhile(v_00_u03c1_1365_, v_s_1366_, v_pat_1367_, v_inst_1368_);
    lean_dec(v_pat_1367_);
    return v_res_1369_;
}
pub unsafe fn l_String_takeEndWhile___redArg(
    mut v_s_1370_: *mut LeanObject,
    mut v_inst_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    v___x_1372_ = lean_unsigned_to_nat(0);
    v___x_1373_ = lean_string_utf8_byte_size(v_s_1370_);
    lean_inc_ref(v_s_1370_);
    v___x_1374_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1374_, 0, v_s_1370_);
    lean_ctor_set(v___x_1374_, 1, v___x_1372_);
    lean_ctor_set(v___x_1374_, 2, v___x_1373_);
    v___x_1375_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1374_, v___x_1373_, v_inst_1371_);
    lean_dec_ref_known(v___x_1374_, 3);
    v___x_1376_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1376_, 0, v_s_1370_);
    lean_ctor_set(v___x_1376_, 1, v___x_1375_);
    lean_ctor_set(v___x_1376_, 2, v___x_1373_);
    return v___x_1376_;
}
pub unsafe fn l_String_takeEndWhile(
    mut v_00_u03c1_1377_: *mut LeanObject,
    mut v_s_1378_: *mut LeanObject,
    mut v_pat_1379_: *mut LeanObject,
    mut v_inst_1380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
    v___x_1381_ = lean_unsigned_to_nat(0);
    v___x_1382_ = lean_string_utf8_byte_size(v_s_1378_);
    lean_inc_ref(v_s_1378_);
    v___x_1383_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1383_, 0, v_s_1378_);
    lean_ctor_set(v___x_1383_, 1, v___x_1381_);
    lean_ctor_set(v___x_1383_, 2, v___x_1382_);
    v___x_1384_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1383_, v___x_1382_, v_inst_1380_);
    lean_dec_ref_known(v___x_1383_, 3);
    v___x_1385_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1385_, 0, v_s_1378_);
    lean_ctor_set(v___x_1385_, 1, v___x_1384_);
    lean_ctor_set(v___x_1385_, 2, v___x_1382_);
    return v___x_1385_;
}
pub unsafe fn l_String_takeEndWhile___boxed(
    mut v_00_u03c1_1386_: *mut LeanObject,
    mut v_s_1387_: *mut LeanObject,
    mut v_pat_1388_: *mut LeanObject,
    mut v_inst_1389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1390_: *mut LeanObject = core::ptr::null_mut();
    v_res_1390_ = l_String_takeEndWhile(v_00_u03c1_1386_, v_s_1387_, v_pat_1388_, v_inst_1389_);
    lean_dec(v_pat_1388_);
    return v_res_1390_;
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
    mut v_p_1391_: *mut LeanObject,
    mut v_s_1392_: *mut LeanObject,
    mut v_pos_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u32 = 0;
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1394_ = lean_ctor_get(v_s_1392_, 0);
                v_startInclusive_1395_ = lean_ctor_get(v_s_1392_, 1);
                v___x_1396_ = lean_nat_add(v_startInclusive_1395_, v_pos_1393_);
                v___x_1397_ = lean_nat_sub(v___x_1396_, v_startInclusive_1395_);
                v___x_1398_ = lean_unsigned_to_nat(0);
                v___x_1399_ = lean_nat_dec_eq(v___x_1397_, v___x_1398_);
                if v___x_1399_ == 0 {
                    lean_inc(v_startInclusive_1395_);
                    lean_inc_ref(v_str_1394_);
                    v___x_1400_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1400_, 0, v_str_1394_);
                    lean_ctor_set(v___x_1400_, 1, v_startInclusive_1395_);
                    lean_ctor_set(v___x_1400_, 2, v___x_1396_);
                    v___x_1401_ = lean_unsigned_to_nat(1);
                    v___x_1402_ = lean_nat_sub(v___x_1397_, v___x_1401_);
                    lean_dec(v___x_1397_);
                    v___x_1403_ = l_String_Slice_posLE(v___x_1400_, v___x_1402_);
                    lean_dec_ref_known(v___x_1400_, 3);
                    v___x_1404_ = lean_nat_add(v_startInclusive_1395_, v___x_1403_);
                    v___x_1405_ = lean_string_utf8_get_fast(v_str_1394_, v___x_1404_);
                    lean_dec(v___x_1404_);
                    v___x_1406_ = lean_box_uint32(v___x_1405_);
                    lean_inc_ref(v_p_1391_);
                    v___x_1407_ = lean_apply_1(v_p_1391_, v___x_1406_);
                    v___x_1408_ = (lean_unbox(v___x_1407_) as u8);
                    if v___x_1408_ == 0 {
                        lean_dec(v___x_1403_);
                        lean_dec_ref(v_p_1391_);
                        return v_pos_1393_;
                    } else {
                        v___x_1409_ = lean_nat_dec_lt(v___x_1403_, v_pos_1393_);
                        if v___x_1409_ == 0 {
                            lean_dec(v___x_1403_);
                            lean_dec_ref(v_p_1391_);
                            return v_pos_1393_;
                        } else {
                            lean_dec(v_pos_1393_);
                            v_pos_1393_ = v___x_1403_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1397_);
                    lean_dec(v___x_1396_);
                    lean_dec_ref(v_p_1391_);
                    return v_pos_1393_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0___boxed(
    mut v_p_1411_: *mut LeanObject,
    mut v_s_1412_: *mut LeanObject,
    mut v_pos_1413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1414_: *mut LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
        v_p_1411_,
        v_s_1412_,
        v_pos_1413_,
    );
    lean_dec_ref(v_s_1412_);
    return v_res_1414_;
}
pub unsafe fn l_String_takeRightWhile(
    mut v_s_1415_: *mut LeanObject,
    mut v_p_1416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut LeanObject = core::ptr::null_mut();
    v___x_1417_ = lean_unsigned_to_nat(0);
    v___x_1418_ = lean_string_utf8_byte_size(v_s_1415_);
    lean_inc_ref(v_s_1415_);
    v___x_1419_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1419_, 0, v_s_1415_);
    lean_ctor_set(v___x_1419_, 1, v___x_1417_);
    lean_ctor_set(v___x_1419_, 2, v___x_1418_);
    v___x_1420_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
        v_p_1416_,
        v___x_1419_,
        v___x_1418_,
    );
    lean_dec_ref_known(v___x_1419_, 3);
    v___x_1421_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1421_, 0, v_s_1415_);
    lean_ctor_set(v___x_1421_, 1, v___x_1420_);
    lean_ctor_set(v___x_1421_, 2, v___x_1418_);
    v___x_1422_ = l_String_Slice_toString(v___x_1421_);
    lean_dec_ref_known(v___x_1421_, 3);
    return v___x_1422_;
}
pub unsafe fn l_String_Slice_takeRightWhile(
    mut v_s_1423_: *mut LeanObject,
    mut v_p_1424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1432_: u8 = 0;
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1437_: u8 = 0;
    let mut v_unused_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1425_ = lean_ctor_get(v_s_1423_, 0);
                lean_inc_ref(v_str_1425_);
                v_startInclusive_1426_ = lean_ctor_get(v_s_1423_, 1);
                lean_inc(v_startInclusive_1426_);
                v_endExclusive_1427_ = lean_ctor_get(v_s_1423_, 2);
                lean_inc(v_endExclusive_1427_);
                v___x_1428_ = lean_nat_sub(v_endExclusive_1427_, v_startInclusive_1426_);
                v___x_1429_ =
                    l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
                        v_p_1424_,
                        v_s_1423_,
                        v___x_1428_,
                    );
                v_isSharedCheck_1437_ = (!lean_is_exclusive(v_s_1423_)) as u8;
                if v_isSharedCheck_1437_ == 0 {
                    v_unused_1438_ = lean_ctor_get(v_s_1423_, 2);
                    lean_dec(v_unused_1438_);
                    v_unused_1439_ = lean_ctor_get(v_s_1423_, 1);
                    lean_dec(v_unused_1439_);
                    v_unused_1440_ = lean_ctor_get(v_s_1423_, 0);
                    lean_dec(v_unused_1440_);
                    v___x_1431_ = v_s_1423_;
                    v_isShared_1432_ = v_isSharedCheck_1437_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_1423_);
                    v___x_1431_ = lean_box(0);
                    v_isShared_1432_ = v_isSharedCheck_1437_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1433_ = lean_nat_add(v_startInclusive_1426_, v___x_1429_);
                lean_dec(v___x_1429_);
                lean_dec(v_startInclusive_1426_);
                if v_isShared_1432_ == 0 {
                    lean_ctor_set(v___x_1431_, 1, v___x_1433_);
                    v___x_1435_ = v___x_1431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_str_1425_);
                    lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1433_);
                    lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_endExclusive_1427_);
                    v___x_1435_ = v_reuseFailAlloc_1436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_dropEndWhile___redArg(
    mut v_s_1441_: *mut LeanObject,
    mut v_inst_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    v___x_1443_ = lean_unsigned_to_nat(0);
    v___x_1444_ = lean_string_utf8_byte_size(v_s_1441_);
    lean_inc_ref(v_s_1441_);
    v___x_1445_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1445_, 0, v_s_1441_);
    lean_ctor_set(v___x_1445_, 1, v___x_1443_);
    lean_ctor_set(v___x_1445_, 2, v___x_1444_);
    v___x_1446_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1445_, v___x_1444_, v_inst_1442_);
    lean_dec_ref_known(v___x_1445_, 3);
    v___x_1447_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1447_, 0, v_s_1441_);
    lean_ctor_set(v___x_1447_, 1, v___x_1443_);
    lean_ctor_set(v___x_1447_, 2, v___x_1446_);
    return v___x_1447_;
}
pub unsafe fn l_String_dropEndWhile(
    mut v_00_u03c1_1448_: *mut LeanObject,
    mut v_s_1449_: *mut LeanObject,
    mut v_pat_1450_: *mut LeanObject,
    mut v_inst_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    v___x_1452_ = lean_unsigned_to_nat(0);
    v___x_1453_ = lean_string_utf8_byte_size(v_s_1449_);
    lean_inc_ref(v_s_1449_);
    v___x_1454_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1454_, 0, v_s_1449_);
    lean_ctor_set(v___x_1454_, 1, v___x_1452_);
    lean_ctor_set(v___x_1454_, 2, v___x_1453_);
    v___x_1455_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1454_, v___x_1453_, v_inst_1451_);
    lean_dec_ref_known(v___x_1454_, 3);
    v___x_1456_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1456_, 0, v_s_1449_);
    lean_ctor_set(v___x_1456_, 1, v___x_1452_);
    lean_ctor_set(v___x_1456_, 2, v___x_1455_);
    return v___x_1456_;
}
pub unsafe fn l_String_dropEndWhile___boxed(
    mut v_00_u03c1_1457_: *mut LeanObject,
    mut v_s_1458_: *mut LeanObject,
    mut v_pat_1459_: *mut LeanObject,
    mut v_inst_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1461_: *mut LeanObject = core::ptr::null_mut();
    v_res_1461_ = l_String_dropEndWhile(v_00_u03c1_1457_, v_s_1458_, v_pat_1459_, v_inst_1460_);
    lean_dec(v_pat_1459_);
    return v_res_1461_;
}
pub unsafe fn l_String_dropRightWhile(
    mut v_s_1462_: *mut LeanObject,
    mut v_p_1463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut LeanObject = core::ptr::null_mut();
    v___x_1464_ = lean_unsigned_to_nat(0);
    v___x_1465_ = lean_string_utf8_byte_size(v_s_1462_);
    lean_inc_ref(v_s_1462_);
    v___x_1466_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1466_, 0, v_s_1462_);
    lean_ctor_set(v___x_1466_, 1, v___x_1464_);
    lean_ctor_set(v___x_1466_, 2, v___x_1465_);
    v___x_1467_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
        v_p_1463_,
        v___x_1466_,
        v___x_1465_,
    );
    lean_dec_ref_known(v___x_1466_, 3);
    v___x_1468_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1468_, 0, v_s_1462_);
    lean_ctor_set(v___x_1468_, 1, v___x_1464_);
    lean_ctor_set(v___x_1468_, 2, v___x_1467_);
    v___x_1469_ = l_String_Slice_toString(v___x_1468_);
    lean_dec_ref_known(v___x_1468_, 3);
    return v___x_1469_;
}
pub unsafe fn l_String_Slice_dropRightWhile(
    mut v_s_1470_: *mut LeanObject,
    mut v_p_1471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut v_unused_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1472_ = lean_ctor_get(v_s_1470_, 0);
                lean_inc_ref(v_str_1472_);
                v_startInclusive_1473_ = lean_ctor_get(v_s_1470_, 1);
                lean_inc(v_startInclusive_1473_);
                v_endExclusive_1474_ = lean_ctor_get(v_s_1470_, 2);
                v___x_1475_ = lean_nat_sub(v_endExclusive_1474_, v_startInclusive_1473_);
                v___x_1476_ =
                    l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
                        v_p_1471_,
                        v_s_1470_,
                        v___x_1475_,
                    );
                v_isSharedCheck_1484_ = (!lean_is_exclusive(v_s_1470_)) as u8;
                if v_isSharedCheck_1484_ == 0 {
                    v_unused_1485_ = lean_ctor_get(v_s_1470_, 2);
                    lean_dec(v_unused_1485_);
                    v_unused_1486_ = lean_ctor_get(v_s_1470_, 1);
                    lean_dec(v_unused_1486_);
                    v_unused_1487_ = lean_ctor_get(v_s_1470_, 0);
                    lean_dec(v_unused_1487_);
                    v___x_1478_ = v_s_1470_;
                    v_isShared_1479_ = v_isSharedCheck_1484_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_1470_);
                    v___x_1478_ = lean_box(0);
                    v_isShared_1479_ = v_isSharedCheck_1484_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1480_ = lean_nat_add(v_startInclusive_1473_, v___x_1476_);
                lean_dec(v___x_1476_);
                if v_isShared_1479_ == 0 {
                    lean_ctor_set(v___x_1478_, 2, v___x_1480_);
                    v___x_1482_ = v___x_1478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_str_1472_);
                    lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_startInclusive_1473_);
                    lean_ctor_set(v_reuseFailAlloc_1483_, 2, v___x_1480_);
                    v___x_1482_ = v_reuseFailAlloc_1483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_skipPrefix_x3f___redArg(
    mut v_s_1488_: *mut LeanObject,
    mut v_inst_1489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipPrefix_x3f_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1503_: u8 = 0;
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_reuseFailAlloc_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v_unused_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_1490_ = lean_ctor_get(v_inst_1489_, 0);
                v_isSharedCheck_1509_ = (!lean_is_exclusive(v_inst_1489_)) as u8;
                if v_isSharedCheck_1509_ == 0 {
                    v_unused_1510_ = lean_ctor_get(v_inst_1489_, 2);
                    lean_dec(v_unused_1510_);
                    v_unused_1511_ = lean_ctor_get(v_inst_1489_, 1);
                    lean_dec(v_unused_1511_);
                    v___x_1492_ = v_inst_1489_;
                    v_isShared_1493_ = v_isSharedCheck_1509_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipPrefix_x3f_1490_);
                    lean_dec(v_inst_1489_);
                    v___x_1492_ = lean_box(0);
                    v_isShared_1493_ = v_isSharedCheck_1509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1494_ = lean_string_utf8_byte_size(v_s_1488_);
                v___x_1495_ = lean_unsigned_to_nat(0);
                if v_isShared_1493_ == 0 {
                    lean_ctor_set(v___x_1492_, 2, v___x_1494_);
                    lean_ctor_set(v___x_1492_, 1, v___x_1495_);
                    lean_ctor_set(v___x_1492_, 0, v_s_1488_);
                    v___x_1497_ = v___x_1492_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_s_1488_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 1, v___x_1495_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 2, v___x_1494_);
                    v___x_1497_ = v_reuseFailAlloc_1508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1498_ = lean_apply_1(v_skipPrefix_x3f_1490_, v___x_1497_);
                if lean_obj_tag(v___x_1498_) == 0 {
                    v___x_1499_ = lean_box(0);
                    return v___x_1499_;
                } else {
                    v_val_1500_ = lean_ctor_get(v___x_1498_, 0);
                    v_isSharedCheck_1507_ = (!lean_is_exclusive(v___x_1498_)) as u8;
                    if v_isSharedCheck_1507_ == 0 {
                        v___x_1502_ = v___x_1498_;
                        v_isShared_1503_ = v_isSharedCheck_1507_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1500_);
                        lean_dec(v___x_1498_);
                        v___x_1502_ = lean_box(0);
                        v_isShared_1503_ = v_isSharedCheck_1507_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1503_ == 0 {
                    v___x_1505_ = v___x_1502_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_val_1500_);
                    v___x_1505_ = v_reuseFailAlloc_1506_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1505_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_skipPrefix_x3f(
    mut v_00_u03c1_1512_: *mut LeanObject,
    mut v_s_1513_: *mut LeanObject,
    mut v_pat_1514_: *mut LeanObject,
    mut v_inst_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipPrefix_x3f_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_reuseFailAlloc_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1535_: u8 = 0;
    let mut v_unused_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_1516_ = lean_ctor_get(v_inst_1515_, 0);
                v_isSharedCheck_1535_ = (!lean_is_exclusive(v_inst_1515_)) as u8;
                if v_isSharedCheck_1535_ == 0 {
                    v_unused_1536_ = lean_ctor_get(v_inst_1515_, 2);
                    lean_dec(v_unused_1536_);
                    v_unused_1537_ = lean_ctor_get(v_inst_1515_, 1);
                    lean_dec(v_unused_1537_);
                    v___x_1518_ = v_inst_1515_;
                    v_isShared_1519_ = v_isSharedCheck_1535_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipPrefix_x3f_1516_);
                    lean_dec(v_inst_1515_);
                    v___x_1518_ = lean_box(0);
                    v_isShared_1519_ = v_isSharedCheck_1535_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1520_ = lean_string_utf8_byte_size(v_s_1513_);
                v___x_1521_ = lean_unsigned_to_nat(0);
                if v_isShared_1519_ == 0 {
                    lean_ctor_set(v___x_1518_, 2, v___x_1520_);
                    lean_ctor_set(v___x_1518_, 1, v___x_1521_);
                    lean_ctor_set(v___x_1518_, 0, v_s_1513_);
                    v___x_1523_ = v___x_1518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_s_1513_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1521_);
                    lean_ctor_set(v_reuseFailAlloc_1534_, 2, v___x_1520_);
                    v___x_1523_ = v_reuseFailAlloc_1534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1524_ = lean_apply_1(v_skipPrefix_x3f_1516_, v___x_1523_);
                if lean_obj_tag(v___x_1524_) == 0 {
                    v___x_1525_ = lean_box(0);
                    return v___x_1525_;
                } else {
                    v_val_1526_ = lean_ctor_get(v___x_1524_, 0);
                    v_isSharedCheck_1533_ = (!lean_is_exclusive(v___x_1524_)) as u8;
                    if v_isSharedCheck_1533_ == 0 {
                        v___x_1528_ = v___x_1524_;
                        v_isShared_1529_ = v_isSharedCheck_1533_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1526_);
                        lean_dec(v___x_1524_);
                        v___x_1528_ = lean_box(0);
                        v_isShared_1529_ = v_isSharedCheck_1533_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1529_ == 0 {
                    v___x_1531_ = v___x_1528_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_val_1526_);
                    v___x_1531_ = v_reuseFailAlloc_1532_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_skipPrefix_x3f___boxed(
    mut v_00_u03c1_1538_: *mut LeanObject,
    mut v_s_1539_: *mut LeanObject,
    mut v_pat_1540_: *mut LeanObject,
    mut v_inst_1541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1542_: *mut LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_String_skipPrefix_x3f(v_00_u03c1_1538_, v_s_1539_, v_pat_1540_, v_inst_1541_);
    lean_dec(v_pat_1540_);
    return v_res_1542_;
}
pub unsafe fn l_String_skipPrefixWhile___redArg(
    mut v_s_1543_: *mut LeanObject,
    mut v_inst_1544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    v___x_1545_ = lean_unsigned_to_nat(0);
    v___x_1546_ = lean_string_utf8_byte_size(v_s_1543_);
    v___x_1547_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1547_, 0, v_s_1543_);
    lean_ctor_set(v___x_1547_, 1, v___x_1545_);
    lean_ctor_set(v___x_1547_, 2, v___x_1546_);
    v___x_1548_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1547_, v___x_1545_, v_inst_1544_);
    lean_dec_ref_known(v___x_1547_, 3);
    return v___x_1548_;
}
pub unsafe fn l_String_skipPrefixWhile(
    mut v_00_u03c1_1549_: *mut LeanObject,
    mut v_s_1550_: *mut LeanObject,
    mut v_pat_1551_: *mut LeanObject,
    mut v_inst_1552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    v___x_1553_ = lean_unsigned_to_nat(0);
    v___x_1554_ = lean_string_utf8_byte_size(v_s_1550_);
    v___x_1555_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1555_, 0, v_s_1550_);
    lean_ctor_set(v___x_1555_, 1, v___x_1553_);
    lean_ctor_set(v___x_1555_, 2, v___x_1554_);
    v___x_1556_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1555_, v___x_1553_, v_inst_1552_);
    lean_dec_ref_known(v___x_1555_, 3);
    return v___x_1556_;
}
pub unsafe fn l_String_skipPrefixWhile___boxed(
    mut v_00_u03c1_1557_: *mut LeanObject,
    mut v_s_1558_: *mut LeanObject,
    mut v_pat_1559_: *mut LeanObject,
    mut v_inst_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1561_: *mut LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_String_skipPrefixWhile(v_00_u03c1_1557_, v_s_1558_, v_pat_1559_, v_inst_1560_);
    lean_dec(v_pat_1559_);
    return v_res_1561_;
}
pub unsafe fn l_String_all___redArg(
    mut v_s_1562_: *mut LeanObject,
    mut v_inst_1563_: *mut LeanObject,
) -> u8 {
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    v___x_1564_ = lean_unsigned_to_nat(0);
    v___x_1565_ = lean_string_utf8_byte_size(v_s_1562_);
    v___x_1566_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1566_, 0, v_s_1562_);
    lean_ctor_set(v___x_1566_, 1, v___x_1564_);
    lean_ctor_set(v___x_1566_, 2, v___x_1565_);
    v___x_1567_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1566_, v___x_1564_, v_inst_1563_);
    lean_dec_ref_known(v___x_1566_, 3);
    v___x_1568_ = lean_nat_dec_eq(v___x_1567_, v___x_1565_);
    lean_dec(v___x_1567_);
    return v___x_1568_;
}
pub unsafe fn l_String_all___redArg___boxed(
    mut v_s_1569_: *mut LeanObject,
    mut v_inst_1570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1571_: u8 = 0;
    let mut v_r_1572_: *mut LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_String_all___redArg(v_s_1569_, v_inst_1570_);
    v_r_1572_ = lean_box((v_res_1571_) as usize);
    return v_r_1572_;
}
pub unsafe fn l_String_all(
    mut v_00_u03c1_1573_: *mut LeanObject,
    mut v_s_1574_: *mut LeanObject,
    mut v_pat_1575_: *mut LeanObject,
    mut v_inst_1576_: *mut LeanObject,
) -> u8 {
    let mut v___x_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    v___x_1577_ = lean_unsigned_to_nat(0);
    v___x_1578_ = lean_string_utf8_byte_size(v_s_1574_);
    v___x_1579_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1579_, 0, v_s_1574_);
    lean_ctor_set(v___x_1579_, 1, v___x_1577_);
    lean_ctor_set(v___x_1579_, 2, v___x_1578_);
    v___x_1580_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1579_, v___x_1577_, v_inst_1576_);
    lean_dec_ref_known(v___x_1579_, 3);
    v___x_1581_ = lean_nat_dec_eq(v___x_1580_, v___x_1578_);
    lean_dec(v___x_1580_);
    return v___x_1581_;
}
pub unsafe fn l_String_all___boxed(
    mut v_00_u03c1_1582_: *mut LeanObject,
    mut v_s_1583_: *mut LeanObject,
    mut v_pat_1584_: *mut LeanObject,
    mut v_inst_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1586_: u8 = 0;
    let mut v_r_1587_: *mut LeanObject = core::ptr::null_mut();
    v_res_1586_ = l_String_all(v_00_u03c1_1582_, v_s_1583_, v_pat_1584_, v_inst_1585_);
    lean_dec(v_pat_1584_);
    v_r_1587_ = lean_box((v_res_1586_) as usize);
    return v_r_1587_;
}
pub unsafe fn l_String_revAll___redArg(
    mut v_s_1588_: *mut LeanObject,
    mut v_inst_1589_: *mut LeanObject,
) -> u8 {
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    v___x_1590_ = lean_unsigned_to_nat(0);
    v___x_1591_ = lean_string_utf8_byte_size(v_s_1588_);
    v___x_1592_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1592_, 0, v_s_1588_);
    lean_ctor_set(v___x_1592_, 1, v___x_1590_);
    lean_ctor_set(v___x_1592_, 2, v___x_1591_);
    v___x_1593_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1592_, v___x_1591_, v_inst_1589_);
    lean_dec_ref_known(v___x_1592_, 3);
    v___x_1594_ = lean_nat_dec_eq(v___x_1593_, v___x_1590_);
    lean_dec(v___x_1593_);
    return v___x_1594_;
}
pub unsafe fn l_String_revAll___redArg___boxed(
    mut v_s_1595_: *mut LeanObject,
    mut v_inst_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1597_: u8 = 0;
    let mut v_r_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1597_ = l_String_revAll___redArg(v_s_1595_, v_inst_1596_);
    v_r_1598_ = lean_box((v_res_1597_) as usize);
    return v_r_1598_;
}
pub unsafe fn l_String_revAll(
    mut v_00_u03c1_1599_: *mut LeanObject,
    mut v_s_1600_: *mut LeanObject,
    mut v_pat_1601_: *mut LeanObject,
    mut v_inst_1602_: *mut LeanObject,
) -> u8 {
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: u8 = 0;
    v___x_1603_ = lean_unsigned_to_nat(0);
    v___x_1604_ = lean_string_utf8_byte_size(v_s_1600_);
    v___x_1605_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1605_, 0, v_s_1600_);
    lean_ctor_set(v___x_1605_, 1, v___x_1603_);
    lean_ctor_set(v___x_1605_, 2, v___x_1604_);
    v___x_1606_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1605_, v___x_1604_, v_inst_1602_);
    lean_dec_ref_known(v___x_1605_, 3);
    v___x_1607_ = lean_nat_dec_eq(v___x_1606_, v___x_1603_);
    lean_dec(v___x_1606_);
    return v___x_1607_;
}
pub unsafe fn l_String_revAll___boxed(
    mut v_00_u03c1_1608_: *mut LeanObject,
    mut v_s_1609_: *mut LeanObject,
    mut v_pat_1610_: *mut LeanObject,
    mut v_inst_1611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1612_: u8 = 0;
    let mut v_r_1613_: *mut LeanObject = core::ptr::null_mut();
    v_res_1612_ = l_String_revAll(v_00_u03c1_1608_, v_s_1609_, v_pat_1610_, v_inst_1611_);
    lean_dec(v_pat_1610_);
    v_r_1613_ = lean_box((v_res_1612_) as usize);
    return v_r_1613_;
}
pub unsafe fn l_String_Pos_skip_x3f___redArg(
    mut v_s_1614_: *mut LeanObject,
    mut v_pos_1615_: *mut LeanObject,
    mut v_inst_1616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipPrefix_x3f_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1634_: u8 = 0;
    let mut v_reuseFailAlloc_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1636_: u8 = 0;
    let mut v_unused_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_1617_ = lean_ctor_get(v_inst_1616_, 0);
                v_isSharedCheck_1636_ = (!lean_is_exclusive(v_inst_1616_)) as u8;
                if v_isSharedCheck_1636_ == 0 {
                    v_unused_1637_ = lean_ctor_get(v_inst_1616_, 2);
                    lean_dec(v_unused_1637_);
                    v_unused_1638_ = lean_ctor_get(v_inst_1616_, 1);
                    lean_dec(v_unused_1638_);
                    v___x_1619_ = v_inst_1616_;
                    v_isShared_1620_ = v_isSharedCheck_1636_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipPrefix_x3f_1617_);
                    lean_dec(v_inst_1616_);
                    v___x_1619_ = lean_box(0);
                    v_isShared_1620_ = v_isSharedCheck_1636_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1621_ = lean_string_utf8_byte_size(v_s_1614_);
                lean_inc(v_pos_1615_);
                if v_isShared_1620_ == 0 {
                    lean_ctor_set(v___x_1619_, 2, v___x_1621_);
                    lean_ctor_set(v___x_1619_, 1, v_pos_1615_);
                    lean_ctor_set(v___x_1619_, 0, v_s_1614_);
                    v___x_1623_ = v___x_1619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1635_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_s_1614_);
                    lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_pos_1615_);
                    lean_ctor_set(v_reuseFailAlloc_1635_, 2, v___x_1621_);
                    v___x_1623_ = v_reuseFailAlloc_1635_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1624_ = lean_apply_1(v_skipPrefix_x3f_1617_, v___x_1623_);
                if lean_obj_tag(v___x_1624_) == 0 {
                    lean_dec(v_pos_1615_);
                    v___x_1625_ = lean_box(0);
                    return v___x_1625_;
                } else {
                    v_val_1626_ = lean_ctor_get(v___x_1624_, 0);
                    v_isSharedCheck_1634_ = (!lean_is_exclusive(v___x_1624_)) as u8;
                    if v_isSharedCheck_1634_ == 0 {
                        v___x_1628_ = v___x_1624_;
                        v_isShared_1629_ = v_isSharedCheck_1634_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1626_);
                        lean_dec(v___x_1624_);
                        v___x_1628_ = lean_box(0);
                        v_isShared_1629_ = v_isSharedCheck_1634_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1630_ = lean_nat_add(v_pos_1615_, v_val_1626_);
                lean_dec(v_val_1626_);
                lean_dec(v_pos_1615_);
                if v_isShared_1629_ == 0 {
                    lean_ctor_set(v___x_1628_, 0, v___x_1630_);
                    v___x_1632_ = v___x_1628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
                    v___x_1632_ = v_reuseFailAlloc_1633_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_skip_x3f(
    mut v_00_u03c1_1639_: *mut LeanObject,
    mut v_s_1640_: *mut LeanObject,
    mut v_pos_1641_: *mut LeanObject,
    mut v_pat_1642_: *mut LeanObject,
    mut v_inst_1643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipPrefix_x3f_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut v_reuseFailAlloc_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut v_unused_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_1644_ = lean_ctor_get(v_inst_1643_, 0);
                v_isSharedCheck_1663_ = (!lean_is_exclusive(v_inst_1643_)) as u8;
                if v_isSharedCheck_1663_ == 0 {
                    v_unused_1664_ = lean_ctor_get(v_inst_1643_, 2);
                    lean_dec(v_unused_1664_);
                    v_unused_1665_ = lean_ctor_get(v_inst_1643_, 1);
                    lean_dec(v_unused_1665_);
                    v___x_1646_ = v_inst_1643_;
                    v_isShared_1647_ = v_isSharedCheck_1663_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipPrefix_x3f_1644_);
                    lean_dec(v_inst_1643_);
                    v___x_1646_ = lean_box(0);
                    v_isShared_1647_ = v_isSharedCheck_1663_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1648_ = lean_string_utf8_byte_size(v_s_1640_);
                lean_inc(v_pos_1641_);
                if v_isShared_1647_ == 0 {
                    lean_ctor_set(v___x_1646_, 2, v___x_1648_);
                    lean_ctor_set(v___x_1646_, 1, v_pos_1641_);
                    lean_ctor_set(v___x_1646_, 0, v_s_1640_);
                    v___x_1650_ = v___x_1646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_s_1640_);
                    lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_pos_1641_);
                    lean_ctor_set(v_reuseFailAlloc_1662_, 2, v___x_1648_);
                    v___x_1650_ = v_reuseFailAlloc_1662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1651_ = lean_apply_1(v_skipPrefix_x3f_1644_, v___x_1650_);
                if lean_obj_tag(v___x_1651_) == 0 {
                    lean_dec(v_pos_1641_);
                    v___x_1652_ = lean_box(0);
                    return v___x_1652_;
                } else {
                    v_val_1653_ = lean_ctor_get(v___x_1651_, 0);
                    v_isSharedCheck_1661_ = (!lean_is_exclusive(v___x_1651_)) as u8;
                    if v_isSharedCheck_1661_ == 0 {
                        v___x_1655_ = v___x_1651_;
                        v_isShared_1656_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1653_);
                        lean_dec(v___x_1651_);
                        v___x_1655_ = lean_box(0);
                        v_isShared_1656_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1657_ = lean_nat_add(v_pos_1641_, v_val_1653_);
                lean_dec(v_val_1653_);
                lean_dec(v_pos_1641_);
                if v_isShared_1656_ == 0 {
                    lean_ctor_set(v___x_1655_, 0, v___x_1657_);
                    v___x_1659_ = v___x_1655_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
                    v___x_1659_ = v_reuseFailAlloc_1660_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1659_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_skip_x3f___boxed(
    mut v_00_u03c1_1666_: *mut LeanObject,
    mut v_s_1667_: *mut LeanObject,
    mut v_pos_1668_: *mut LeanObject,
    mut v_pat_1669_: *mut LeanObject,
    mut v_inst_1670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1671_: *mut LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_String_Pos_skip_x3f(
        v_00_u03c1_1666_,
        v_s_1667_,
        v_pos_1668_,
        v_pat_1669_,
        v_inst_1670_,
    );
    lean_dec(v_pat_1669_);
    return v_res_1671_;
}
pub unsafe fn l_String_Pos_skipWhile___redArg(
    mut v_s_1672_: *mut LeanObject,
    mut v_pos_1673_: *mut LeanObject,
    mut v_inst_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    v___x_1675_ = lean_unsigned_to_nat(0);
    v___x_1676_ = lean_string_utf8_byte_size(v_s_1672_);
    v___x_1677_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1677_, 0, v_s_1672_);
    lean_ctor_set(v___x_1677_, 1, v___x_1675_);
    lean_ctor_set(v___x_1677_, 2, v___x_1676_);
    v___x_1678_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1677_, v_pos_1673_, v_inst_1674_);
    lean_dec_ref_known(v___x_1677_, 3);
    return v___x_1678_;
}
pub unsafe fn l_String_Pos_skipWhile(
    mut v_00_u03c1_1679_: *mut LeanObject,
    mut v_s_1680_: *mut LeanObject,
    mut v_pos_1681_: *mut LeanObject,
    mut v_pat_1682_: *mut LeanObject,
    mut v_inst_1683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    v___x_1684_ = lean_unsigned_to_nat(0);
    v___x_1685_ = lean_string_utf8_byte_size(v_s_1680_);
    v___x_1686_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1686_, 0, v_s_1680_);
    lean_ctor_set(v___x_1686_, 1, v___x_1684_);
    lean_ctor_set(v___x_1686_, 2, v___x_1685_);
    v___x_1687_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1686_, v_pos_1681_, v_inst_1683_);
    lean_dec_ref_known(v___x_1686_, 3);
    return v___x_1687_;
}
pub unsafe fn l_String_Pos_skipWhile___boxed(
    mut v_00_u03c1_1688_: *mut LeanObject,
    mut v_s_1689_: *mut LeanObject,
    mut v_pos_1690_: *mut LeanObject,
    mut v_pat_1691_: *mut LeanObject,
    mut v_inst_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_String_Pos_skipWhile(
        v_00_u03c1_1688_,
        v_s_1689_,
        v_pos_1690_,
        v_pat_1691_,
        v_inst_1692_,
    );
    lean_dec(v_pat_1691_);
    return v_res_1693_;
}
pub unsafe fn l_String_startsWith___redArg(
    mut v_s_1694_: *mut LeanObject,
    mut v_inst_1695_: *mut LeanObject,
) -> u8 {
    let mut v_startsWith_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    let mut v_reuseFailAlloc_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut v_unused_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startsWith_1696_ = lean_ctor_get(v_inst_1695_, 2);
                v_isSharedCheck_1707_ = (!lean_is_exclusive(v_inst_1695_)) as u8;
                if v_isSharedCheck_1707_ == 0 {
                    v_unused_1708_ = lean_ctor_get(v_inst_1695_, 1);
                    lean_dec(v_unused_1708_);
                    v_unused_1709_ = lean_ctor_get(v_inst_1695_, 0);
                    lean_dec(v_unused_1709_);
                    v___x_1698_ = v_inst_1695_;
                    v_isShared_1699_ = v_isSharedCheck_1707_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_startsWith_1696_);
                    lean_dec(v_inst_1695_);
                    v___x_1698_ = lean_box(0);
                    v_isShared_1699_ = v_isSharedCheck_1707_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1700_ = lean_string_utf8_byte_size(v_s_1694_);
                v___x_1701_ = lean_unsigned_to_nat(0);
                if v_isShared_1699_ == 0 {
                    lean_ctor_set(v___x_1698_, 2, v___x_1700_);
                    lean_ctor_set(v___x_1698_, 1, v___x_1701_);
                    lean_ctor_set(v___x_1698_, 0, v_s_1694_);
                    v___x_1703_ = v___x_1698_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_s_1694_);
                    lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1701_);
                    lean_ctor_set(v_reuseFailAlloc_1706_, 2, v___x_1700_);
                    v___x_1703_ = v_reuseFailAlloc_1706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1704_ = lean_apply_1(v_startsWith_1696_, v___x_1703_);
                v___x_1705_ = (lean_unbox(v___x_1704_) as u8);
                return v___x_1705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_startsWith___redArg___boxed(
    mut v_s_1710_: *mut LeanObject,
    mut v_inst_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1712_: u8 = 0;
    let mut v_r_1713_: *mut LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_String_startsWith___redArg(v_s_1710_, v_inst_1711_);
    v_r_1713_ = lean_box((v_res_1712_) as usize);
    return v_r_1713_;
}
pub unsafe fn l_String_startsWith(
    mut v_00_u03c1_1714_: *mut LeanObject,
    mut v_s_1715_: *mut LeanObject,
    mut v_pat_1716_: *mut LeanObject,
    mut v_inst_1717_: *mut LeanObject,
) -> u8 {
    let mut v_startsWith_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1721_: u8 = 0;
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v_reuseFailAlloc_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut v_unused_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startsWith_1718_ = lean_ctor_get(v_inst_1717_, 2);
                v_isSharedCheck_1729_ = (!lean_is_exclusive(v_inst_1717_)) as u8;
                if v_isSharedCheck_1729_ == 0 {
                    v_unused_1730_ = lean_ctor_get(v_inst_1717_, 1);
                    lean_dec(v_unused_1730_);
                    v_unused_1731_ = lean_ctor_get(v_inst_1717_, 0);
                    lean_dec(v_unused_1731_);
                    v___x_1720_ = v_inst_1717_;
                    v_isShared_1721_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_startsWith_1718_);
                    lean_dec(v_inst_1717_);
                    v___x_1720_ = lean_box(0);
                    v_isShared_1721_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1722_ = lean_string_utf8_byte_size(v_s_1715_);
                v___x_1723_ = lean_unsigned_to_nat(0);
                if v_isShared_1721_ == 0 {
                    lean_ctor_set(v___x_1720_, 2, v___x_1722_);
                    lean_ctor_set(v___x_1720_, 1, v___x_1723_);
                    lean_ctor_set(v___x_1720_, 0, v_s_1715_);
                    v___x_1725_ = v___x_1720_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_s_1715_);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1723_);
                    lean_ctor_set(v_reuseFailAlloc_1728_, 2, v___x_1722_);
                    v___x_1725_ = v_reuseFailAlloc_1728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1726_ = lean_apply_1(v_startsWith_1718_, v___x_1725_);
                v___x_1727_ = (lean_unbox(v___x_1726_) as u8);
                return v___x_1727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_startsWith___boxed(
    mut v_00_u03c1_1732_: *mut LeanObject,
    mut v_s_1733_: *mut LeanObject,
    mut v_pat_1734_: *mut LeanObject,
    mut v_inst_1735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1736_: u8 = 0;
    let mut v_r_1737_: *mut LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_String_startsWith(v_00_u03c1_1732_, v_s_1733_, v_pat_1734_, v_inst_1735_);
    lean_dec(v_pat_1734_);
    v_r_1737_ = lean_box((v_res_1736_) as usize);
    return v_r_1737_;
}
pub unsafe fn l_String_isPrefixOf(
    mut v_p_1738_: *mut LeanObject,
    mut v_s_1739_: *mut LeanObject,
) -> u8 {
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    v___x_1740_ = lean_string_utf8_byte_size(v_s_1739_);
    v___x_1741_ = lean_string_utf8_byte_size(v_p_1738_);
    v___x_1742_ = lean_nat_dec_le(v___x_1741_, v___x_1740_);
    if v___x_1742_ == 0 {
        return v___x_1742_;
    } else {
        let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: u8 = 0;
        v___x_1743_ = lean_unsigned_to_nat(0);
        v___x_1744_ =
            lean_string_memcmp(v_s_1739_, v_p_1738_, v___x_1743_, v___x_1743_, v___x_1741_);
        return v___x_1744_;
    }
}
pub unsafe fn l_String_isPrefixOf___boxed(
    mut v_p_1745_: *mut LeanObject,
    mut v_s_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1747_: u8 = 0;
    let mut v_r_1748_: *mut LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_String_isPrefixOf(v_p_1745_, v_s_1746_);
    lean_dec_ref(v_s_1746_);
    lean_dec_ref(v_p_1745_);
    v_r_1748_ = lean_box((v_res_1747_) as usize);
    return v_r_1748_;
}
pub unsafe fn lean_string_isprefixof(
    mut v_p_1749_: *mut LeanObject,
    mut v_s_1750_: *mut LeanObject,
) -> u8 {
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    v___x_1751_ = lean_string_utf8_byte_size(v_s_1750_);
    v___x_1752_ = lean_string_utf8_byte_size(v_p_1749_);
    v___x_1753_ = lean_nat_dec_le(v___x_1752_, v___x_1751_);
    if v___x_1753_ == 0 {
        lean_dec_ref(v_s_1750_);
        lean_dec_ref(v_p_1749_);
        return v___x_1753_;
    } else {
        let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: u8 = 0;
        v___x_1754_ = lean_unsigned_to_nat(0);
        v___x_1755_ =
            lean_string_memcmp(v_s_1750_, v_p_1749_, v___x_1754_, v___x_1754_, v___x_1752_);
        lean_dec_ref(v_p_1749_);
        lean_dec_ref(v_s_1750_);
        return v___x_1755_;
    }
}
pub unsafe fn l_String_Internal_isPrefixOfImpl___boxed(
    mut v_p_1756_: *mut LeanObject,
    mut v_s_1757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1758_: u8 = 0;
    let mut v_r_1759_: *mut LeanObject = core::ptr::null_mut();
    v_res_1758_ = lean_string_isprefixof(v_p_1756_, v_s_1757_);
    v_r_1759_ = lean_box((v_res_1758_) as usize);
    return v_r_1759_;
}
pub unsafe fn l_String_endsWith___redArg(
    mut v_s_1760_: *mut LeanObject,
    mut v_inst_1761_: *mut LeanObject,
) -> u8 {
    let mut v_endsWith_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v_reuseFailAlloc_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v_unused_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_endsWith_1762_ = lean_ctor_get(v_inst_1761_, 2);
                v_isSharedCheck_1773_ = (!lean_is_exclusive(v_inst_1761_)) as u8;
                if v_isSharedCheck_1773_ == 0 {
                    v_unused_1774_ = lean_ctor_get(v_inst_1761_, 1);
                    lean_dec(v_unused_1774_);
                    v_unused_1775_ = lean_ctor_get(v_inst_1761_, 0);
                    lean_dec(v_unused_1775_);
                    v___x_1764_ = v_inst_1761_;
                    v_isShared_1765_ = v_isSharedCheck_1773_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_endsWith_1762_);
                    lean_dec(v_inst_1761_);
                    v___x_1764_ = lean_box(0);
                    v_isShared_1765_ = v_isSharedCheck_1773_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1766_ = lean_string_utf8_byte_size(v_s_1760_);
                v___x_1767_ = lean_unsigned_to_nat(0);
                if v_isShared_1765_ == 0 {
                    lean_ctor_set(v___x_1764_, 2, v___x_1766_);
                    lean_ctor_set(v___x_1764_, 1, v___x_1767_);
                    lean_ctor_set(v___x_1764_, 0, v_s_1760_);
                    v___x_1769_ = v___x_1764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_s_1760_);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1767_);
                    lean_ctor_set(v_reuseFailAlloc_1772_, 2, v___x_1766_);
                    v___x_1769_ = v_reuseFailAlloc_1772_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1770_ = lean_apply_1(v_endsWith_1762_, v___x_1769_);
                v___x_1771_ = (lean_unbox(v___x_1770_) as u8);
                return v___x_1771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_endsWith___redArg___boxed(
    mut v_s_1776_: *mut LeanObject,
    mut v_inst_1777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1778_: u8 = 0;
    let mut v_r_1779_: *mut LeanObject = core::ptr::null_mut();
    v_res_1778_ = l_String_endsWith___redArg(v_s_1776_, v_inst_1777_);
    v_r_1779_ = lean_box((v_res_1778_) as usize);
    return v_r_1779_;
}
pub unsafe fn l_String_endsWith(
    mut v_00_u03c1_1780_: *mut LeanObject,
    mut v_s_1781_: *mut LeanObject,
    mut v_pat_1782_: *mut LeanObject,
    mut v_inst_1783_: *mut LeanObject,
) -> u8 {
    let mut v_endsWith_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v_reuseFailAlloc_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_unused_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_endsWith_1784_ = lean_ctor_get(v_inst_1783_, 2);
                v_isSharedCheck_1795_ = (!lean_is_exclusive(v_inst_1783_)) as u8;
                if v_isSharedCheck_1795_ == 0 {
                    v_unused_1796_ = lean_ctor_get(v_inst_1783_, 1);
                    lean_dec(v_unused_1796_);
                    v_unused_1797_ = lean_ctor_get(v_inst_1783_, 0);
                    lean_dec(v_unused_1797_);
                    v___x_1786_ = v_inst_1783_;
                    v_isShared_1787_ = v_isSharedCheck_1795_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_endsWith_1784_);
                    lean_dec(v_inst_1783_);
                    v___x_1786_ = lean_box(0);
                    v_isShared_1787_ = v_isSharedCheck_1795_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1788_ = lean_string_utf8_byte_size(v_s_1781_);
                v___x_1789_ = lean_unsigned_to_nat(0);
                if v_isShared_1787_ == 0 {
                    lean_ctor_set(v___x_1786_, 2, v___x_1788_);
                    lean_ctor_set(v___x_1786_, 1, v___x_1789_);
                    lean_ctor_set(v___x_1786_, 0, v_s_1781_);
                    v___x_1791_ = v___x_1786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_s_1781_);
                    lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___x_1789_);
                    lean_ctor_set(v_reuseFailAlloc_1794_, 2, v___x_1788_);
                    v___x_1791_ = v_reuseFailAlloc_1794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1792_ = lean_apply_1(v_endsWith_1784_, v___x_1791_);
                v___x_1793_ = (lean_unbox(v___x_1792_) as u8);
                return v___x_1793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_endsWith___boxed(
    mut v_00_u03c1_1798_: *mut LeanObject,
    mut v_s_1799_: *mut LeanObject,
    mut v_pat_1800_: *mut LeanObject,
    mut v_inst_1801_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1802_: u8 = 0;
    let mut v_r_1803_: *mut LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_String_endsWith(v_00_u03c1_1798_, v_s_1799_, v_pat_1800_, v_inst_1801_);
    lean_dec(v_pat_1800_);
    v_r_1803_ = lean_box((v_res_1802_) as usize);
    return v_r_1803_;
}
pub unsafe fn l_String_skipSuffix_x3f___redArg(
    mut v_s_1804_: *mut LeanObject,
    mut v_inst_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipSuffix_x3f_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut v_reuseFailAlloc_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut v_unused_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_1806_ = lean_ctor_get(v_inst_1805_, 0);
                v_isSharedCheck_1825_ = (!lean_is_exclusive(v_inst_1805_)) as u8;
                if v_isSharedCheck_1825_ == 0 {
                    v_unused_1826_ = lean_ctor_get(v_inst_1805_, 2);
                    lean_dec(v_unused_1826_);
                    v_unused_1827_ = lean_ctor_get(v_inst_1805_, 1);
                    lean_dec(v_unused_1827_);
                    v___x_1808_ = v_inst_1805_;
                    v_isShared_1809_ = v_isSharedCheck_1825_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipSuffix_x3f_1806_);
                    lean_dec(v_inst_1805_);
                    v___x_1808_ = lean_box(0);
                    v_isShared_1809_ = v_isSharedCheck_1825_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1810_ = lean_string_utf8_byte_size(v_s_1804_);
                v___x_1811_ = lean_unsigned_to_nat(0);
                if v_isShared_1809_ == 0 {
                    lean_ctor_set(v___x_1808_, 2, v___x_1810_);
                    lean_ctor_set(v___x_1808_, 1, v___x_1811_);
                    lean_ctor_set(v___x_1808_, 0, v_s_1804_);
                    v___x_1813_ = v___x_1808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_s_1804_);
                    lean_ctor_set(v_reuseFailAlloc_1824_, 1, v___x_1811_);
                    lean_ctor_set(v_reuseFailAlloc_1824_, 2, v___x_1810_);
                    v___x_1813_ = v_reuseFailAlloc_1824_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1814_ = lean_apply_1(v_skipSuffix_x3f_1806_, v___x_1813_);
                if lean_obj_tag(v___x_1814_) == 0 {
                    v___x_1815_ = lean_box(0);
                    return v___x_1815_;
                } else {
                    v_val_1816_ = lean_ctor_get(v___x_1814_, 0);
                    v_isSharedCheck_1823_ = (!lean_is_exclusive(v___x_1814_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v___x_1818_ = v___x_1814_;
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1816_);
                        lean_dec(v___x_1814_);
                        v___x_1818_ = lean_box(0);
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1819_ == 0 {
                    v___x_1821_ = v___x_1818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_val_1816_);
                    v___x_1821_ = v_reuseFailAlloc_1822_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_skipSuffix_x3f(
    mut v_00_u03c1_1828_: *mut LeanObject,
    mut v_s_1829_: *mut LeanObject,
    mut v_pat_1830_: *mut LeanObject,
    mut v_inst_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipSuffix_x3f_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1845_: u8 = 0;
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1849_: u8 = 0;
    let mut v_reuseFailAlloc_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut v_unused_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_1832_ = lean_ctor_get(v_inst_1831_, 0);
                v_isSharedCheck_1851_ = (!lean_is_exclusive(v_inst_1831_)) as u8;
                if v_isSharedCheck_1851_ == 0 {
                    v_unused_1852_ = lean_ctor_get(v_inst_1831_, 2);
                    lean_dec(v_unused_1852_);
                    v_unused_1853_ = lean_ctor_get(v_inst_1831_, 1);
                    lean_dec(v_unused_1853_);
                    v___x_1834_ = v_inst_1831_;
                    v_isShared_1835_ = v_isSharedCheck_1851_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipSuffix_x3f_1832_);
                    lean_dec(v_inst_1831_);
                    v___x_1834_ = lean_box(0);
                    v_isShared_1835_ = v_isSharedCheck_1851_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1836_ = lean_string_utf8_byte_size(v_s_1829_);
                v___x_1837_ = lean_unsigned_to_nat(0);
                if v_isShared_1835_ == 0 {
                    lean_ctor_set(v___x_1834_, 2, v___x_1836_);
                    lean_ctor_set(v___x_1834_, 1, v___x_1837_);
                    lean_ctor_set(v___x_1834_, 0, v_s_1829_);
                    v___x_1839_ = v___x_1834_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_s_1829_);
                    lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___x_1837_);
                    lean_ctor_set(v_reuseFailAlloc_1850_, 2, v___x_1836_);
                    v___x_1839_ = v_reuseFailAlloc_1850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1840_ = lean_apply_1(v_skipSuffix_x3f_1832_, v___x_1839_);
                if lean_obj_tag(v___x_1840_) == 0 {
                    v___x_1841_ = lean_box(0);
                    return v___x_1841_;
                } else {
                    v_val_1842_ = lean_ctor_get(v___x_1840_, 0);
                    v_isSharedCheck_1849_ = (!lean_is_exclusive(v___x_1840_)) as u8;
                    if v_isSharedCheck_1849_ == 0 {
                        v___x_1844_ = v___x_1840_;
                        v_isShared_1845_ = v_isSharedCheck_1849_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1842_);
                        lean_dec(v___x_1840_);
                        v___x_1844_ = lean_box(0);
                        v_isShared_1845_ = v_isSharedCheck_1849_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1845_ == 0 {
                    v___x_1847_ = v___x_1844_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_val_1842_);
                    v___x_1847_ = v_reuseFailAlloc_1848_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_skipSuffix_x3f___boxed(
    mut v_00_u03c1_1854_: *mut LeanObject,
    mut v_s_1855_: *mut LeanObject,
    mut v_pat_1856_: *mut LeanObject,
    mut v_inst_1857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1858_: *mut LeanObject = core::ptr::null_mut();
    v_res_1858_ = l_String_skipSuffix_x3f(v_00_u03c1_1854_, v_s_1855_, v_pat_1856_, v_inst_1857_);
    lean_dec(v_pat_1856_);
    return v_res_1858_;
}
pub unsafe fn l_String_skipSuffixWhile___redArg(
    mut v_s_1859_: *mut LeanObject,
    mut v_inst_1860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1861_ = lean_unsigned_to_nat(0);
    v___x_1862_ = lean_string_utf8_byte_size(v_s_1859_);
    v___x_1863_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1863_, 0, v_s_1859_);
    lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    lean_ctor_set(v___x_1863_, 2, v___x_1862_);
    v___x_1864_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1863_, v___x_1862_, v_inst_1860_);
    lean_dec_ref_known(v___x_1863_, 3);
    return v___x_1864_;
}
pub unsafe fn l_String_skipSuffixWhile(
    mut v_00_u03c1_1865_: *mut LeanObject,
    mut v_s_1866_: *mut LeanObject,
    mut v_pat_1867_: *mut LeanObject,
    mut v_inst_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    v___x_1869_ = lean_unsigned_to_nat(0);
    v___x_1870_ = lean_string_utf8_byte_size(v_s_1866_);
    v___x_1871_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1871_, 0, v_s_1866_);
    lean_ctor_set(v___x_1871_, 1, v___x_1869_);
    lean_ctor_set(v___x_1871_, 2, v___x_1870_);
    v___x_1872_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1871_, v___x_1870_, v_inst_1868_);
    lean_dec_ref_known(v___x_1871_, 3);
    return v___x_1872_;
}
pub unsafe fn l_String_skipSuffixWhile___boxed(
    mut v_00_u03c1_1873_: *mut LeanObject,
    mut v_s_1874_: *mut LeanObject,
    mut v_pat_1875_: *mut LeanObject,
    mut v_inst_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1877_: *mut LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_String_skipSuffixWhile(v_00_u03c1_1873_, v_s_1874_, v_pat_1875_, v_inst_1876_);
    lean_dec(v_pat_1875_);
    return v_res_1877_;
}
pub unsafe fn l_String_Pos_revSkip_x3f___redArg(
    mut v_s_1878_: *mut LeanObject,
    mut v_pos_1879_: *mut LeanObject,
    mut v_inst_1880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipSuffix_x3f_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1893_: u8 = 0;
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_reuseFailAlloc_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_unused_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_1881_ = lean_ctor_get(v_inst_1880_, 0);
                v_isSharedCheck_1899_ = (!lean_is_exclusive(v_inst_1880_)) as u8;
                if v_isSharedCheck_1899_ == 0 {
                    v_unused_1900_ = lean_ctor_get(v_inst_1880_, 2);
                    lean_dec(v_unused_1900_);
                    v_unused_1901_ = lean_ctor_get(v_inst_1880_, 1);
                    lean_dec(v_unused_1901_);
                    v___x_1883_ = v_inst_1880_;
                    v_isShared_1884_ = v_isSharedCheck_1899_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipSuffix_x3f_1881_);
                    lean_dec(v_inst_1880_);
                    v___x_1883_ = lean_box(0);
                    v_isShared_1884_ = v_isSharedCheck_1899_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1885_ = lean_unsigned_to_nat(0);
                if v_isShared_1884_ == 0 {
                    lean_ctor_set(v___x_1883_, 2, v_pos_1879_);
                    lean_ctor_set(v___x_1883_, 1, v___x_1885_);
                    lean_ctor_set(v___x_1883_, 0, v_s_1878_);
                    v___x_1887_ = v___x_1883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1898_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_s_1878_);
                    lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1885_);
                    lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_pos_1879_);
                    v___x_1887_ = v_reuseFailAlloc_1898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1888_ = lean_apply_1(v_skipSuffix_x3f_1881_, v___x_1887_);
                if lean_obj_tag(v___x_1888_) == 0 {
                    v___x_1889_ = lean_box(0);
                    return v___x_1889_;
                } else {
                    v_val_1890_ = lean_ctor_get(v___x_1888_, 0);
                    v_isSharedCheck_1897_ = (!lean_is_exclusive(v___x_1888_)) as u8;
                    if v_isSharedCheck_1897_ == 0 {
                        v___x_1892_ = v___x_1888_;
                        v_isShared_1893_ = v_isSharedCheck_1897_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1890_);
                        lean_dec(v___x_1888_);
                        v___x_1892_ = lean_box(0);
                        v_isShared_1893_ = v_isSharedCheck_1897_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1893_ == 0 {
                    v___x_1895_ = v___x_1892_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_val_1890_);
                    v___x_1895_ = v_reuseFailAlloc_1896_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_revSkip_x3f(
    mut v_00_u03c1_1902_: *mut LeanObject,
    mut v_s_1903_: *mut LeanObject,
    mut v_pos_1904_: *mut LeanObject,
    mut v_pat_1905_: *mut LeanObject,
    mut v_inst_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipSuffix_x3f_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1910_: u8 = 0;
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1919_: u8 = 0;
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut v_reuseFailAlloc_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1925_: u8 = 0;
    let mut v_unused_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_1907_ = lean_ctor_get(v_inst_1906_, 0);
                v_isSharedCheck_1925_ = (!lean_is_exclusive(v_inst_1906_)) as u8;
                if v_isSharedCheck_1925_ == 0 {
                    v_unused_1926_ = lean_ctor_get(v_inst_1906_, 2);
                    lean_dec(v_unused_1926_);
                    v_unused_1927_ = lean_ctor_get(v_inst_1906_, 1);
                    lean_dec(v_unused_1927_);
                    v___x_1909_ = v_inst_1906_;
                    v_isShared_1910_ = v_isSharedCheck_1925_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipSuffix_x3f_1907_);
                    lean_dec(v_inst_1906_);
                    v___x_1909_ = lean_box(0);
                    v_isShared_1910_ = v_isSharedCheck_1925_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1911_ = lean_unsigned_to_nat(0);
                if v_isShared_1910_ == 0 {
                    lean_ctor_set(v___x_1909_, 2, v_pos_1904_);
                    lean_ctor_set(v___x_1909_, 1, v___x_1911_);
                    lean_ctor_set(v___x_1909_, 0, v_s_1903_);
                    v___x_1913_ = v___x_1909_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_s_1903_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1911_);
                    lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_pos_1904_);
                    v___x_1913_ = v_reuseFailAlloc_1924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1914_ = lean_apply_1(v_skipSuffix_x3f_1907_, v___x_1913_);
                if lean_obj_tag(v___x_1914_) == 0 {
                    v___x_1915_ = lean_box(0);
                    return v___x_1915_;
                } else {
                    v_val_1916_ = lean_ctor_get(v___x_1914_, 0);
                    v_isSharedCheck_1923_ = (!lean_is_exclusive(v___x_1914_)) as u8;
                    if v_isSharedCheck_1923_ == 0 {
                        v___x_1918_ = v___x_1914_;
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1916_);
                        lean_dec(v___x_1914_);
                        v___x_1918_ = lean_box(0);
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1919_ == 0 {
                    v___x_1921_ = v___x_1918_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_val_1916_);
                    v___x_1921_ = v_reuseFailAlloc_1922_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1921_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_revSkip_x3f___boxed(
    mut v_00_u03c1_1928_: *mut LeanObject,
    mut v_s_1929_: *mut LeanObject,
    mut v_pos_1930_: *mut LeanObject,
    mut v_pat_1931_: *mut LeanObject,
    mut v_inst_1932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1933_: *mut LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_String_Pos_revSkip_x3f(
        v_00_u03c1_1928_,
        v_s_1929_,
        v_pos_1930_,
        v_pat_1931_,
        v_inst_1932_,
    );
    lean_dec(v_pat_1931_);
    return v_res_1933_;
}
pub unsafe fn l_String_Pos_revSkipWhile___redArg(
    mut v_s_1934_: *mut LeanObject,
    mut v_pos_1935_: *mut LeanObject,
    mut v_inst_1936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    v___x_1937_ = lean_unsigned_to_nat(0);
    v___x_1938_ = lean_string_utf8_byte_size(v_s_1934_);
    v___x_1939_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1939_, 0, v_s_1934_);
    lean_ctor_set(v___x_1939_, 1, v___x_1937_);
    lean_ctor_set(v___x_1939_, 2, v___x_1938_);
    v___x_1940_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1939_, v_pos_1935_, v_inst_1936_);
    lean_dec_ref_known(v___x_1939_, 3);
    return v___x_1940_;
}
pub unsafe fn l_String_Pos_revSkipWhile(
    mut v_00_u03c1_1941_: *mut LeanObject,
    mut v_s_1942_: *mut LeanObject,
    mut v_pos_1943_: *mut LeanObject,
    mut v_pat_1944_: *mut LeanObject,
    mut v_inst_1945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    v___x_1946_ = lean_unsigned_to_nat(0);
    v___x_1947_ = lean_string_utf8_byte_size(v_s_1942_);
    v___x_1948_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1948_, 0, v_s_1942_);
    lean_ctor_set(v___x_1948_, 1, v___x_1946_);
    lean_ctor_set(v___x_1948_, 2, v___x_1947_);
    v___x_1949_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1948_, v_pos_1943_, v_inst_1945_);
    lean_dec_ref_known(v___x_1948_, 3);
    return v___x_1949_;
}
pub unsafe fn l_String_Pos_revSkipWhile___boxed(
    mut v_00_u03c1_1950_: *mut LeanObject,
    mut v_s_1951_: *mut LeanObject,
    mut v_pos_1952_: *mut LeanObject,
    mut v_pat_1953_: *mut LeanObject,
    mut v_inst_1954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1955_: *mut LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_String_Pos_revSkipWhile(
        v_00_u03c1_1950_,
        v_s_1951_,
        v_pos_1952_,
        v_pat_1953_,
        v_inst_1954_,
    );
    lean_dec(v_pat_1953_);
    return v_res_1955_;
}
pub unsafe fn _init_l_String_trimAsciiEnd___closed__1() -> *mut LeanObject {
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    v___x_1957_ = l_String_trimAsciiEnd___closed__0;
    v___x_1958_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_1957_);
    return v___x_1958_;
}
pub unsafe fn l_String_trimAsciiEnd(mut v_s_1959_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    v___x_1960_ = lean_unsigned_to_nat(0);
    v___x_1961_ = lean_string_utf8_byte_size(v_s_1959_);
    lean_inc_ref(v_s_1959_);
    v___x_1962_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1962_, 0, v_s_1959_);
    lean_ctor_set(v___x_1962_, 1, v___x_1960_);
    lean_ctor_set(v___x_1962_, 2, v___x_1961_);
    v___x_1963_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_String_trimAsciiEnd___closed__1),
        core::ptr::addr_of_mut!(l_String_trimAsciiEnd___closed__1_once),
        _init_l_String_trimAsciiEnd___closed__1,
    );
    v___x_1964_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1962_, v___x_1961_, v___x_1963_);
    lean_dec_ref_known(v___x_1962_, 3);
    v___x_1965_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1965_, 0, v_s_1959_);
    lean_ctor_set(v___x_1965_, 1, v___x_1960_);
    lean_ctor_set(v___x_1965_, 2, v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(
    mut v_s_1966_: *mut LeanObject,
    mut v_pos_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___y_1982_: u8 = 0;
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: u32 = 0;
    let mut v___y_1986_: u8 = 0;
    let mut v___x_1987_: u32 = 0;
    let mut v___x_1988_: u8 = 0;
    let mut v___x_1989_: u32 = 0;
    let mut v___x_1990_: u8 = 0;
    let mut v___x_1991_: u32 = 0;
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: u32 = 0;
    let mut v___x_1994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1968_ = lean_ctor_get(v_s_1966_, 0);
                v_startInclusive_1969_ = lean_ctor_get(v_s_1966_, 1);
                v___x_1970_ = lean_nat_add(v_startInclusive_1969_, v_pos_1967_);
                v___x_1971_ = lean_nat_sub(v___x_1970_, v_startInclusive_1969_);
                v___x_1972_ = lean_unsigned_to_nat(0);
                v___x_1973_ = lean_nat_dec_eq(v___x_1971_, v___x_1972_);
                if v___x_1973_ == 0 {
                    lean_inc(v_startInclusive_1969_);
                    lean_inc_ref(v_str_1968_);
                    v___x_1974_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v___x_1974_, 0, v_str_1968_);
                    lean_ctor_set(v___x_1974_, 1, v_startInclusive_1969_);
                    lean_ctor_set(v___x_1974_, 2, v___x_1970_);
                    v___x_1975_ = lean_unsigned_to_nat(1);
                    v___x_1976_ = lean_nat_sub(v___x_1971_, v___x_1975_);
                    lean_dec(v___x_1971_);
                    v___x_1977_ = l_String_Slice_posLE(v___x_1974_, v___x_1976_);
                    lean_dec_ref_known(v___x_1974_, 3);
                    v___x_1983_ = lean_nat_add(v_startInclusive_1969_, v___x_1977_);
                    v___x_1984_ = lean_string_utf8_get_fast(v_str_1968_, v___x_1983_);
                    lean_dec(v___x_1983_);
                    v___x_1991_ = 32;
                    v___x_1992_ = lean_uint32_dec_eq(v___x_1984_, v___x_1991_);
                    if v___x_1992_ == 0 {
                        v___x_1993_ = 9;
                        v___x_1994_ = lean_uint32_dec_eq(v___x_1984_, v___x_1993_);
                        v___y_1986_ = v___x_1994_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1986_ = v___x_1992_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1971_);
                    lean_dec(v___x_1970_);
                    return v_pos_1967_;
                }
            }
            1 => {
                v___x_1979_ = lean_nat_dec_lt(v___x_1977_, v_pos_1967_);
                if v___x_1979_ == 0 {
                    lean_dec(v___x_1977_);
                    return v_pos_1967_;
                } else {
                    lean_dec(v_pos_1967_);
                    v_pos_1967_ = v___x_1977_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_1982_ == 0 {
                    lean_dec(v___x_1977_);
                    return v_pos_1967_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1986_ == 0 {
                    v___x_1987_ = 13;
                    v___x_1988_ = lean_uint32_dec_eq(v___x_1984_, v___x_1987_);
                    if v___x_1988_ == 0 {
                        v___x_1989_ = 10;
                        v___x_1990_ = lean_uint32_dec_eq(v___x_1984_, v___x_1989_);
                        v___y_1982_ = v___x_1990_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1982_ = v___x_1988_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0___boxed(
    mut v_s_1995_: *mut LeanObject,
    mut v_pos_1996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1997_: *mut LeanObject = core::ptr::null_mut();
    v_res_1997_ =
        l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v_s_1995_, v_pos_1996_);
    lean_dec_ref(v_s_1995_);
    return v_res_1997_;
}
pub unsafe fn l_String_trimRight(mut v_s_1998_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    v___x_1999_ = lean_unsigned_to_nat(0);
    v___x_2000_ = lean_string_utf8_byte_size(v_s_1998_);
    lean_inc_ref(v_s_1998_);
    v___x_2001_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2001_, 0, v_s_1998_);
    lean_ctor_set(v___x_2001_, 1, v___x_1999_);
    lean_ctor_set(v___x_2001_, 2, v___x_2000_);
    v___x_2002_ =
        l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v___x_2001_, v___x_2000_);
    lean_dec_ref_known(v___x_2001_, 3);
    v___x_2003_ = lean_string_utf8_extract(v_s_1998_, v___x_1999_, v___x_2002_);
    lean_dec(v___x_2002_);
    lean_dec_ref(v_s_1998_);
    return v___x_2003_;
}
pub unsafe fn l_String_Slice_trimRight(mut v_s_2004_: *mut LeanObject) -> *mut LeanObject {
    let mut v_str_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_unused_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2005_ = lean_ctor_get(v_s_2004_, 0);
                lean_inc_ref(v_str_2005_);
                v_startInclusive_2006_ = lean_ctor_get(v_s_2004_, 1);
                lean_inc(v_startInclusive_2006_);
                v_endExclusive_2007_ = lean_ctor_get(v_s_2004_, 2);
                v___x_2008_ = lean_nat_sub(v_endExclusive_2007_, v_startInclusive_2006_);
                v___x_2009_ = l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(
                    v_s_2004_,
                    v___x_2008_,
                );
                v_isSharedCheck_2017_ = (!lean_is_exclusive(v_s_2004_)) as u8;
                if v_isSharedCheck_2017_ == 0 {
                    v_unused_2018_ = lean_ctor_get(v_s_2004_, 2);
                    lean_dec(v_unused_2018_);
                    v_unused_2019_ = lean_ctor_get(v_s_2004_, 1);
                    lean_dec(v_unused_2019_);
                    v_unused_2020_ = lean_ctor_get(v_s_2004_, 0);
                    lean_dec(v_unused_2020_);
                    v___x_2011_ = v_s_2004_;
                    v_isShared_2012_ = v_isSharedCheck_2017_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_2004_);
                    v___x_2011_ = lean_box(0);
                    v_isShared_2012_ = v_isSharedCheck_2017_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2013_ = lean_nat_add(v_startInclusive_2006_, v___x_2009_);
                lean_dec(v___x_2009_);
                if v_isShared_2012_ == 0 {
                    lean_ctor_set(v___x_2011_, 2, v___x_2013_);
                    v___x_2015_ = v___x_2011_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_str_2005_);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_startInclusive_2006_);
                    lean_ctor_set(v_reuseFailAlloc_2016_, 2, v___x_2013_);
                    v___x_2015_ = v_reuseFailAlloc_2016_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_String_trimAsciiStart___closed__0() -> *mut LeanObject {
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    v___x_2021_ = l_String_trimAsciiEnd___closed__0;
    v___x_2022_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_2021_);
    return v___x_2022_;
}
pub unsafe fn l_String_trimAsciiStart(mut v_s_2023_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    v___x_2024_ = lean_unsigned_to_nat(0);
    v___x_2025_ = lean_string_utf8_byte_size(v_s_2023_);
    lean_inc_ref(v_s_2023_);
    v___x_2026_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2026_, 0, v_s_2023_);
    lean_ctor_set(v___x_2026_, 1, v___x_2024_);
    lean_ctor_set(v___x_2026_, 2, v___x_2025_);
    v___x_2027_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_String_trimAsciiStart___closed__0),
        core::ptr::addr_of_mut!(l_String_trimAsciiStart___closed__0_once),
        _init_l_String_trimAsciiStart___closed__0,
    );
    v___x_2028_ = l_String_Slice_Pos_skipWhile___redArg(v___x_2026_, v___x_2024_, v___x_2027_);
    lean_dec_ref_known(v___x_2026_, 3);
    v___x_2029_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2029_, 0, v_s_2023_);
    lean_ctor_set(v___x_2029_, 1, v___x_2028_);
    lean_ctor_set(v___x_2029_, 2, v___x_2025_);
    return v___x_2029_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(
    mut v_s_2030_: *mut LeanObject,
    mut v_pos_2031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: u8 = 0;
    let mut v___y_2043_: u8 = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: u8 = 0;
    let mut v___x_2047_: u32 = 0;
    let mut v___y_2049_: u8 = 0;
    let mut v___x_2050_: u32 = 0;
    let mut v___x_2051_: u8 = 0;
    let mut v___x_2052_: u32 = 0;
    let mut v___x_2053_: u8 = 0;
    let mut v___x_2054_: u32 = 0;
    let mut v___x_2055_: u8 = 0;
    let mut v___x_2056_: u32 = 0;
    let mut v___x_2057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2032_ = lean_ctor_get(v_s_2030_, 0);
                v_startInclusive_2033_ = lean_ctor_get(v_s_2030_, 1);
                v_endExclusive_2034_ = lean_ctor_get(v_s_2030_, 2);
                v___x_2035_ = lean_nat_add(v_startInclusive_2033_, v_pos_2031_);
                v___x_2044_ = lean_unsigned_to_nat(0);
                v___x_2045_ = lean_nat_sub(v_endExclusive_2034_, v___x_2035_);
                v___x_2046_ = lean_nat_dec_eq(v___x_2044_, v___x_2045_);
                lean_dec(v___x_2045_);
                if v___x_2046_ == 0 {
                    v___x_2047_ = lean_string_utf8_get_fast(v_str_2032_, v___x_2035_);
                    v___x_2054_ = 32;
                    v___x_2055_ = lean_uint32_dec_eq(v___x_2047_, v___x_2054_);
                    if v___x_2055_ == 0 {
                        v___x_2056_ = 9;
                        v___x_2057_ = lean_uint32_dec_eq(v___x_2047_, v___x_2056_);
                        v___y_2049_ = v___x_2057_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2049_ = v___x_2055_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2035_);
                    return v_pos_2031_;
                }
            }
            1 => {
                v___x_2037_ = lean_string_utf8_next_fast(v_str_2032_, v___x_2035_);
                v___x_2038_ = lean_nat_sub(v___x_2037_, v___x_2035_);
                lean_dec(v___x_2035_);
                v___x_2039_ = lean_nat_add(v_pos_2031_, v___x_2038_);
                lean_dec(v___x_2038_);
                v___x_2040_ = lean_nat_dec_lt(v_pos_2031_, v___x_2039_);
                if v___x_2040_ == 0 {
                    lean_dec(v___x_2039_);
                    return v_pos_2031_;
                } else {
                    lean_dec(v_pos_2031_);
                    v_pos_2031_ = v___x_2039_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_2043_ == 0 {
                    lean_dec(v___x_2035_);
                    return v_pos_2031_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_2049_ == 0 {
                    v___x_2050_ = 13;
                    v___x_2051_ = lean_uint32_dec_eq(v___x_2047_, v___x_2050_);
                    if v___x_2051_ == 0 {
                        v___x_2052_ = 10;
                        v___x_2053_ = lean_uint32_dec_eq(v___x_2047_, v___x_2052_);
                        v___y_2043_ = v___x_2053_;
                        state = 2;
                        continue;
                    } else {
                        v___y_2043_ = v___x_2051_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0___boxed(
    mut v_s_2058_: *mut LeanObject,
    mut v_pos_2059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2060_: *mut LeanObject = core::ptr::null_mut();
    v_res_2060_ =
        l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v_s_2058_, v_pos_2059_);
    lean_dec_ref(v_s_2058_);
    return v_res_2060_;
}
pub unsafe fn l_String_trimLeft(mut v_s_2061_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    v___x_2062_ = lean_unsigned_to_nat(0);
    v___x_2063_ = lean_string_utf8_byte_size(v_s_2061_);
    lean_inc_ref(v_s_2061_);
    v___x_2064_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2064_, 0, v_s_2061_);
    lean_ctor_set(v___x_2064_, 1, v___x_2062_);
    lean_ctor_set(v___x_2064_, 2, v___x_2063_);
    v___x_2065_ =
        l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v___x_2064_, v___x_2062_);
    lean_dec_ref_known(v___x_2064_, 3);
    v___x_2066_ = lean_string_utf8_extract(v_s_2061_, v___x_2065_, v___x_2063_);
    lean_dec(v___x_2065_);
    lean_dec_ref(v_s_2061_);
    return v___x_2066_;
}
pub unsafe fn l_String_Slice_trimLeft(mut v_s_2067_: *mut LeanObject) -> *mut LeanObject {
    let mut v_str_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_unused_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2068_ = lean_ctor_get(v_s_2067_, 0);
                lean_inc_ref(v_str_2068_);
                v_startInclusive_2069_ = lean_ctor_get(v_s_2067_, 1);
                lean_inc(v_startInclusive_2069_);
                v_endExclusive_2070_ = lean_ctor_get(v_s_2067_, 2);
                lean_inc(v_endExclusive_2070_);
                v___x_2071_ = lean_unsigned_to_nat(0);
                v___x_2072_ = l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(
                    v_s_2067_,
                    v___x_2071_,
                );
                v_isSharedCheck_2080_ = (!lean_is_exclusive(v_s_2067_)) as u8;
                if v_isSharedCheck_2080_ == 0 {
                    v_unused_2081_ = lean_ctor_get(v_s_2067_, 2);
                    lean_dec(v_unused_2081_);
                    v_unused_2082_ = lean_ctor_get(v_s_2067_, 1);
                    lean_dec(v_unused_2082_);
                    v_unused_2083_ = lean_ctor_get(v_s_2067_, 0);
                    lean_dec(v_unused_2083_);
                    v___x_2074_ = v_s_2067_;
                    v_isShared_2075_ = v_isSharedCheck_2080_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v_s_2067_);
                    v___x_2074_ = lean_box(0);
                    v_isShared_2075_ = v_isSharedCheck_2080_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2076_ = lean_nat_add(v_startInclusive_2069_, v___x_2072_);
                lean_dec(v___x_2072_);
                lean_dec(v_startInclusive_2069_);
                if v_isShared_2075_ == 0 {
                    lean_ctor_set(v___x_2074_, 1, v___x_2076_);
                    v___x_2078_ = v___x_2074_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_str_2068_);
                    lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2076_);
                    lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_endExclusive_2070_);
                    v___x_2078_ = v_reuseFailAlloc_2079_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2078_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_trimAscii(mut v_s_2084_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    v___x_2085_ = lean_unsigned_to_nat(0);
    v___x_2086_ = lean_string_utf8_byte_size(v_s_2084_);
    v___x_2087_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2087_, 0, v_s_2084_);
    lean_ctor_set(v___x_2087_, 1, v___x_2085_);
    lean_ctor_set(v___x_2087_, 2, v___x_2086_);
    v___x_2088_ = l_String_Slice_trimAscii(v___x_2087_);
    return v___x_2088_;
}
pub unsafe fn l_String_trim(mut v_s_2089_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    v___x_2090_ = lean_unsigned_to_nat(0);
    v___x_2091_ = lean_string_utf8_byte_size(v_s_2089_);
    v___x_2092_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2092_, 0, v_s_2089_);
    lean_ctor_set(v___x_2092_, 1, v___x_2090_);
    lean_ctor_set(v___x_2092_, 2, v___x_2091_);
    v___x_2093_ = l_String_Slice_trimAscii(v___x_2092_);
    v_str_2094_ = lean_ctor_get(v___x_2093_, 0);
    lean_inc_ref(v_str_2094_);
    v_startInclusive_2095_ = lean_ctor_get(v___x_2093_, 1);
    lean_inc(v_startInclusive_2095_);
    v_endExclusive_2096_ = lean_ctor_get(v___x_2093_, 2);
    lean_inc(v_endExclusive_2096_);
    lean_dec_ref(v___x_2093_);
    v___x_2097_ =
        lean_string_utf8_extract(v_str_2094_, v_startInclusive_2095_, v_endExclusive_2096_);
    lean_dec(v_endExclusive_2096_);
    lean_dec(v_startInclusive_2095_);
    lean_dec_ref(v_str_2094_);
    return v___x_2097_;
}
pub unsafe fn l_String_Slice_trim(mut v_s_2098_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    v___x_2099_ = l_String_Slice_trimAscii(v_s_2098_);
    return v___x_2099_;
}
pub unsafe fn lean_string_trim(mut v_s_2100_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    v___x_2101_ = lean_unsigned_to_nat(0);
    v___x_2102_ = lean_string_utf8_byte_size(v_s_2100_);
    v___x_2103_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2103_, 0, v_s_2100_);
    lean_ctor_set(v___x_2103_, 1, v___x_2101_);
    lean_ctor_set(v___x_2103_, 2, v___x_2102_);
    v___x_2104_ = l_String_Slice_trimAscii(v___x_2103_);
    v_str_2105_ = lean_ctor_get(v___x_2104_, 0);
    lean_inc_ref(v_str_2105_);
    v_startInclusive_2106_ = lean_ctor_get(v___x_2104_, 1);
    lean_inc(v_startInclusive_2106_);
    v_endExclusive_2107_ = lean_ctor_get(v___x_2104_, 2);
    lean_inc(v_endExclusive_2107_);
    lean_dec_ref(v___x_2104_);
    v___x_2108_ =
        lean_string_utf8_extract(v_str_2105_, v_startInclusive_2106_, v_endExclusive_2107_);
    lean_dec(v_endExclusive_2107_);
    lean_dec(v_startInclusive_2106_);
    lean_dec_ref(v_str_2105_);
    return v___x_2108_;
}
pub unsafe fn l_String_Pos_Raw_nextWhile(
    mut v_s_2109_: *mut LeanObject,
    mut v_p_2110_: *mut LeanObject,
    mut v_i_2111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    v___x_2112_ = lean_string_utf8_byte_size(v_s_2109_);
    v___x_2113_ = l_Substring_Raw_takeWhileAux(v_s_2109_, v___x_2112_, v_p_2110_, v_i_2111_);
    return v___x_2113_;
}
pub unsafe fn l_String_Pos_Raw_nextWhile___boxed(
    mut v_s_2114_: *mut LeanObject,
    mut v_p_2115_: *mut LeanObject,
    mut v_i_2116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2117_: *mut LeanObject = core::ptr::null_mut();
    v_res_2117_ = l_String_Pos_Raw_nextWhile(v_s_2114_, v_p_2115_, v_i_2116_);
    lean_dec_ref(v_s_2114_);
    return v_res_2117_;
}
pub unsafe fn l_String_nextWhile(
    mut v_s_2118_: *mut LeanObject,
    mut v_p_2119_: *mut LeanObject,
    mut v_i_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    v___x_2121_ = lean_string_utf8_byte_size(v_s_2118_);
    v___x_2122_ = l_Substring_Raw_takeWhileAux(v_s_2118_, v___x_2121_, v_p_2119_, v_i_2120_);
    return v___x_2122_;
}
pub unsafe fn l_String_nextWhile___boxed(
    mut v_s_2123_: *mut LeanObject,
    mut v_p_2124_: *mut LeanObject,
    mut v_i_2125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2126_: *mut LeanObject = core::ptr::null_mut();
    v_res_2126_ = l_String_nextWhile(v_s_2123_, v_p_2124_, v_i_2125_);
    lean_dec_ref(v_s_2123_);
    return v_res_2126_;
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(
    mut v_p_2127_: *mut LeanObject,
    mut v_s_2128_: *mut LeanObject,
    mut v_stopPos_2129_: *mut LeanObject,
    mut v_i_2130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: u32 = 0;
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2131_ = lean_nat_dec_lt(v_i_2130_, v_stopPos_2129_);
                if v___x_2131_ == 0 {
                    lean_dec_ref(v_p_2127_);
                    return v_i_2130_;
                } else {
                    v___x_2132_ = lean_string_utf8_get(v_s_2128_, v_i_2130_);
                    v___x_2133_ = lean_box_uint32(v___x_2132_);
                    lean_inc_ref(v_p_2127_);
                    v___x_2134_ = lean_apply_1(v_p_2127_, v___x_2133_);
                    v___x_2135_ = (lean_unbox(v___x_2134_) as u8);
                    if v___x_2135_ == 0 {
                        lean_dec_ref(v_p_2127_);
                        return v_i_2130_;
                    } else {
                        v___x_2136_ = lean_string_utf8_next(v_s_2128_, v_i_2130_);
                        lean_dec(v_i_2130_);
                        v_i_2130_ = v___x_2136_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0___boxed(
    mut v_p_2138_: *mut LeanObject,
    mut v_s_2139_: *mut LeanObject,
    mut v_stopPos_2140_: *mut LeanObject,
    mut v_i_2141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2142_: *mut LeanObject = core::ptr::null_mut();
    v_res_2142_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(
        v_p_2138_,
        v_s_2139_,
        v_stopPos_2140_,
        v_i_2141_,
    );
    lean_dec(v_stopPos_2140_);
    lean_dec_ref(v_s_2139_);
    return v_res_2142_;
}
pub unsafe fn lean_string_nextwhile(
    mut v_s_2143_: *mut LeanObject,
    mut v_p_2144_: *mut LeanObject,
    mut v_i_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    v___x_2146_ = lean_string_utf8_byte_size(v_s_2143_);
    v___x_2147_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(
        v_p_2144_,
        v_s_2143_,
        v___x_2146_,
        v_i_2145_,
    );
    lean_dec_ref(v_s_2143_);
    return v___x_2147_;
}
pub unsafe fn l_String_Pos_Raw_nextUntil___lam__0(
    mut v_p_2148_: *mut LeanObject,
    mut v_c_2149_: u32,
) -> u8 {
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: u8 = 0;
    v___x_2150_ = lean_box_uint32(v_c_2149_);
    v___x_2151_ = lean_apply_1(v_p_2148_, v___x_2150_);
    v___x_2152_ = (lean_unbox(v___x_2151_) as u8);
    if v___x_2152_ == 0 {
        let mut v___x_2153_: u8 = 0;
        v___x_2153_ = 1;
        return v___x_2153_;
    } else {
        let mut v___x_2154_: u8 = 0;
        v___x_2154_ = 0;
        return v___x_2154_;
    }
}
pub unsafe fn l_String_Pos_Raw_nextUntil___lam__0___boxed(
    mut v_p_2155_: *mut LeanObject,
    mut v_c_2156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_2157_: u32 = 0;
    let mut v_res_2158_: u8 = 0;
    let mut v_r_2159_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_2157_ = lean_unbox_uint32(v_c_2156_);
    lean_dec(v_c_2156_);
    v_res_2158_ = l_String_Pos_Raw_nextUntil___lam__0(v_p_2155_, v_c_boxed_2157_);
    v_r_2159_ = lean_box((v_res_2158_) as usize);
    return v_r_2159_;
}
pub unsafe fn l_String_Pos_Raw_nextUntil(
    mut v_s_2160_: *mut LeanObject,
    mut v_p_2161_: *mut LeanObject,
    mut v_i_2162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    v___f_2163_ = lean_alloc_closure(
        l_String_Pos_Raw_nextUntil___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2163_, 0, v_p_2161_);
    v___x_2164_ = lean_string_utf8_byte_size(v_s_2160_);
    v___x_2165_ = l_Substring_Raw_takeWhileAux(v_s_2160_, v___x_2164_, v___f_2163_, v_i_2162_);
    return v___x_2165_;
}
pub unsafe fn l_String_Pos_Raw_nextUntil___boxed(
    mut v_s_2166_: *mut LeanObject,
    mut v_p_2167_: *mut LeanObject,
    mut v_i_2168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2169_: *mut LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_String_Pos_Raw_nextUntil(v_s_2166_, v_p_2167_, v_i_2168_);
    lean_dec_ref(v_s_2166_);
    return v_res_2169_;
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(
    mut v_p_2170_: *mut LeanObject,
    mut v_s_2171_: *mut LeanObject,
    mut v_stopPos_2172_: *mut LeanObject,
    mut v_i_2173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2174_: u8 = 0;
    let mut v___x_2175_: u32 = 0;
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2174_ = lean_nat_dec_lt(v_i_2173_, v_stopPos_2172_);
                if v___x_2174_ == 0 {
                    lean_dec_ref(v_p_2170_);
                    return v_i_2173_;
                } else {
                    v___x_2175_ = lean_string_utf8_get(v_s_2171_, v_i_2173_);
                    v___x_2176_ = lean_box_uint32(v___x_2175_);
                    lean_inc_ref(v_p_2170_);
                    v___x_2177_ = lean_apply_1(v_p_2170_, v___x_2176_);
                    v___x_2178_ = (lean_unbox(v___x_2177_) as u8);
                    if v___x_2178_ == 0 {
                        v___x_2179_ = lean_string_utf8_next(v_s_2171_, v_i_2173_);
                        lean_dec(v_i_2173_);
                        v_i_2173_ = v___x_2179_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_p_2170_);
                        return v_i_2173_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(
    mut v_p_2181_: *mut LeanObject,
    mut v_s_2182_: *mut LeanObject,
    mut v_stopPos_2183_: *mut LeanObject,
    mut v_i_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2185_: *mut LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(
        v_p_2181_,
        v_s_2182_,
        v_stopPos_2183_,
        v_i_2184_,
    );
    lean_dec(v_stopPos_2183_);
    lean_dec_ref(v_s_2182_);
    return v_res_2185_;
}
pub unsafe fn l_String_nextUntil(
    mut v_s_2186_: *mut LeanObject,
    mut v_p_2187_: *mut LeanObject,
    mut v_i_2188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    v___x_2189_ = lean_string_utf8_byte_size(v_s_2186_);
    v___x_2190_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(
        v_p_2187_,
        v_s_2186_,
        v___x_2189_,
        v_i_2188_,
    );
    return v___x_2190_;
}
pub unsafe fn l_String_nextUntil___boxed(
    mut v_s_2191_: *mut LeanObject,
    mut v_p_2192_: *mut LeanObject,
    mut v_i_2193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2194_: *mut LeanObject = core::ptr::null_mut();
    v_res_2194_ = l_String_nextUntil(v_s_2191_, v_p_2192_, v_i_2193_);
    lean_dec_ref(v_s_2191_);
    return v_res_2194_;
}
pub unsafe fn l_String_dropPrefix_x3f___redArg(
    mut v_s_2195_: *mut LeanObject,
    mut v_inst_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipPrefix_x3f_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2200_: u8 = 0;
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2215_: u8 = 0;
    let mut v_reuseFailAlloc_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_unused_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_2197_ = lean_ctor_get(v_inst_2196_, 0);
                v_isSharedCheck_2217_ = (!lean_is_exclusive(v_inst_2196_)) as u8;
                if v_isSharedCheck_2217_ == 0 {
                    v_unused_2218_ = lean_ctor_get(v_inst_2196_, 2);
                    lean_dec(v_unused_2218_);
                    v_unused_2219_ = lean_ctor_get(v_inst_2196_, 1);
                    lean_dec(v_unused_2219_);
                    v___x_2199_ = v_inst_2196_;
                    v_isShared_2200_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipPrefix_x3f_2197_);
                    lean_dec(v_inst_2196_);
                    v___x_2199_ = lean_box(0);
                    v_isShared_2200_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2201_ = lean_string_utf8_byte_size(v_s_2195_);
                v___x_2202_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_s_2195_);
                if v_isShared_2200_ == 0 {
                    lean_ctor_set(v___x_2199_, 2, v___x_2201_);
                    lean_ctor_set(v___x_2199_, 1, v___x_2202_);
                    lean_ctor_set(v___x_2199_, 0, v_s_2195_);
                    v___x_2204_ = v___x_2199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_s_2195_);
                    lean_ctor_set(v_reuseFailAlloc_2216_, 1, v___x_2202_);
                    lean_ctor_set(v_reuseFailAlloc_2216_, 2, v___x_2201_);
                    v___x_2204_ = v_reuseFailAlloc_2216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2205_ = lean_apply_1(v_skipPrefix_x3f_2197_, v___x_2204_);
                if lean_obj_tag(v___x_2205_) == 0 {
                    lean_dec_ref(v_s_2195_);
                    v___x_2206_ = lean_box(0);
                    return v___x_2206_;
                } else {
                    v_val_2207_ = lean_ctor_get(v___x_2205_, 0);
                    v_isSharedCheck_2215_ = (!lean_is_exclusive(v___x_2205_)) as u8;
                    if v_isSharedCheck_2215_ == 0 {
                        v___x_2209_ = v___x_2205_;
                        v_isShared_2210_ = v_isSharedCheck_2215_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2207_);
                        lean_dec(v___x_2205_);
                        v___x_2209_ = lean_box(0);
                        v_isShared_2210_ = v_isSharedCheck_2215_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2211_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2211_, 0, v_s_2195_);
                lean_ctor_set(v___x_2211_, 1, v_val_2207_);
                lean_ctor_set(v___x_2211_, 2, v___x_2201_);
                if v_isShared_2210_ == 0 {
                    lean_ctor_set(v___x_2209_, 0, v___x_2211_);
                    v___x_2213_ = v___x_2209_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2214_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
                    v___x_2213_ = v_reuseFailAlloc_2214_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2213_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f(
    mut v_00_u03c1_2220_: *mut LeanObject,
    mut v_s_2221_: *mut LeanObject,
    mut v_pat_2222_: *mut LeanObject,
    mut v_inst_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    v___x_2224_ = l_String_dropPrefix_x3f___redArg(v_s_2221_, v_inst_2223_);
    return v___x_2224_;
}
pub unsafe fn l_String_dropPrefix_x3f___boxed(
    mut v_00_u03c1_2225_: *mut LeanObject,
    mut v_s_2226_: *mut LeanObject,
    mut v_pat_2227_: *mut LeanObject,
    mut v_inst_2228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2229_: *mut LeanObject = core::ptr::null_mut();
    v_res_2229_ = l_String_dropPrefix_x3f(v_00_u03c1_2225_, v_s_2226_, v_pat_2227_, v_inst_2228_);
    lean_dec(v_pat_2227_);
    return v_res_2229_;
}
pub unsafe fn l_String_dropSuffix_x3f___redArg(
    mut v_s_2230_: *mut LeanObject,
    mut v_inst_2231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_skipSuffix_x3f_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2235_: u8 = 0;
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut v_reuseFailAlloc_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2252_: u8 = 0;
    let mut v_unused_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_2232_ = lean_ctor_get(v_inst_2231_, 0);
                v_isSharedCheck_2252_ = (!lean_is_exclusive(v_inst_2231_)) as u8;
                if v_isSharedCheck_2252_ == 0 {
                    v_unused_2253_ = lean_ctor_get(v_inst_2231_, 2);
                    lean_dec(v_unused_2253_);
                    v_unused_2254_ = lean_ctor_get(v_inst_2231_, 1);
                    lean_dec(v_unused_2254_);
                    v___x_2234_ = v_inst_2231_;
                    v_isShared_2235_ = v_isSharedCheck_2252_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_skipSuffix_x3f_2232_);
                    lean_dec(v_inst_2231_);
                    v___x_2234_ = lean_box(0);
                    v_isShared_2235_ = v_isSharedCheck_2252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2236_ = lean_string_utf8_byte_size(v_s_2230_);
                v___x_2237_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_s_2230_);
                if v_isShared_2235_ == 0 {
                    lean_ctor_set(v___x_2234_, 2, v___x_2236_);
                    lean_ctor_set(v___x_2234_, 1, v___x_2237_);
                    lean_ctor_set(v___x_2234_, 0, v_s_2230_);
                    v___x_2239_ = v___x_2234_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_s_2230_);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2237_);
                    lean_ctor_set(v_reuseFailAlloc_2251_, 2, v___x_2236_);
                    v___x_2239_ = v_reuseFailAlloc_2251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2240_ = lean_apply_1(v_skipSuffix_x3f_2232_, v___x_2239_);
                if lean_obj_tag(v___x_2240_) == 0 {
                    lean_dec_ref(v_s_2230_);
                    v___x_2241_ = lean_box(0);
                    return v___x_2241_;
                } else {
                    v_val_2242_ = lean_ctor_get(v___x_2240_, 0);
                    v_isSharedCheck_2250_ = (!lean_is_exclusive(v___x_2240_)) as u8;
                    if v_isSharedCheck_2250_ == 0 {
                        v___x_2244_ = v___x_2240_;
                        v_isShared_2245_ = v_isSharedCheck_2250_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_2242_);
                        lean_dec(v___x_2240_);
                        v___x_2244_ = lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2250_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2246_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_2246_, 0, v_s_2230_);
                lean_ctor_set(v___x_2246_, 1, v___x_2237_);
                lean_ctor_set(v___x_2246_, 2, v_val_2242_);
                if v_isShared_2245_ == 0 {
                    lean_ctor_set(v___x_2244_, 0, v___x_2246_);
                    v___x_2248_ = v___x_2244_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2249_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
                    v___x_2248_ = v_reuseFailAlloc_2249_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2248_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_dropSuffix_x3f(
    mut v_00_u03c1_2255_: *mut LeanObject,
    mut v_s_2256_: *mut LeanObject,
    mut v_pat_2257_: *mut LeanObject,
    mut v_inst_2258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    v___x_2259_ = l_String_dropSuffix_x3f___redArg(v_s_2256_, v_inst_2258_);
    return v___x_2259_;
}
pub unsafe fn l_String_dropSuffix_x3f___boxed(
    mut v_00_u03c1_2260_: *mut LeanObject,
    mut v_s_2261_: *mut LeanObject,
    mut v_pat_2262_: *mut LeanObject,
    mut v_inst_2263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2264_: *mut LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_String_dropSuffix_x3f(v_00_u03c1_2260_, v_s_2261_, v_pat_2262_, v_inst_2263_);
    lean_dec(v_pat_2262_);
    return v_res_2264_;
}
pub unsafe fn l_String_dropPrefix___redArg(
    mut v_s_2265_: *mut LeanObject,
    mut v_inst_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    v___x_2267_ = lean_unsigned_to_nat(0);
    v___x_2268_ = lean_string_utf8_byte_size(v_s_2265_);
    v___x_2269_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2269_, 0, v_s_2265_);
    lean_ctor_set(v___x_2269_, 1, v___x_2267_);
    lean_ctor_set(v___x_2269_, 2, v___x_2268_);
    v___x_2270_ = l_String_Slice_dropPrefix___redArg(v___x_2269_, v_inst_2266_);
    return v___x_2270_;
}
pub unsafe fn l_String_dropPrefix(
    mut v_00_u03c1_2271_: *mut LeanObject,
    mut v_s_2272_: *mut LeanObject,
    mut v_pat_2273_: *mut LeanObject,
    mut v_inst_2274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_String_dropPrefix___redArg(v_s_2272_, v_inst_2274_);
    return v___x_2275_;
}
pub unsafe fn l_String_dropPrefix___boxed(
    mut v_00_u03c1_2276_: *mut LeanObject,
    mut v_s_2277_: *mut LeanObject,
    mut v_pat_2278_: *mut LeanObject,
    mut v_inst_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2280_: *mut LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_String_dropPrefix(v_00_u03c1_2276_, v_s_2277_, v_pat_2278_, v_inst_2279_);
    lean_dec(v_pat_2278_);
    return v_res_2280_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(
    mut v_pre_2281_: *mut LeanObject,
    mut v_s_2282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2283_ = lean_ctor_get(v_s_2282_, 0);
                v_startInclusive_2284_ = lean_ctor_get(v_s_2282_, 1);
                v_endExclusive_2285_ = lean_ctor_get(v_s_2282_, 2);
                v___x_2286_ = lean_string_utf8_byte_size(v_pre_2281_);
                v___x_2287_ = lean_nat_sub(v_endExclusive_2285_, v_startInclusive_2284_);
                v___x_2288_ = lean_nat_dec_le(v___x_2286_, v___x_2287_);
                lean_dec(v___x_2287_);
                if v___x_2288_ == 0 {
                    return v_s_2282_;
                } else {
                    v___x_2289_ = lean_unsigned_to_nat(0);
                    v___x_2290_ = lean_string_memcmp(
                        v_str_2283_,
                        v_pre_2281_,
                        v_startInclusive_2284_,
                        v___x_2289_,
                        v___x_2286_,
                    );
                    if v___x_2290_ == 0 {
                        return v_s_2282_;
                    } else {
                        lean_inc(v_endExclusive_2285_);
                        lean_inc(v_startInclusive_2284_);
                        lean_inc_ref(v_str_2283_);
                        v___x_2291_ = l_String_Slice_pos_x21(v_s_2282_, v___x_2286_);
                        v_isSharedCheck_2299_ = (!lean_is_exclusive(v_s_2282_)) as u8;
                        if v_isSharedCheck_2299_ == 0 {
                            v_unused_2300_ = lean_ctor_get(v_s_2282_, 2);
                            lean_dec(v_unused_2300_);
                            v_unused_2301_ = lean_ctor_get(v_s_2282_, 1);
                            lean_dec(v_unused_2301_);
                            v_unused_2302_ = lean_ctor_get(v_s_2282_, 0);
                            lean_dec(v_unused_2302_);
                            v___x_2293_ = v_s_2282_;
                            v_isShared_2294_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_2282_);
                            v___x_2293_ = lean_box(0);
                            v_isShared_2294_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2295_ = lean_nat_add(v_startInclusive_2284_, v___x_2291_);
                lean_dec(v___x_2291_);
                lean_dec(v_startInclusive_2284_);
                if v_isShared_2294_ == 0 {
                    lean_ctor_set(v___x_2293_, 1, v___x_2295_);
                    v___x_2297_ = v___x_2293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_str_2283_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 1, v___x_2295_);
                    lean_ctor_set(v_reuseFailAlloc_2298_, 2, v_endExclusive_2285_);
                    v___x_2297_ = v_reuseFailAlloc_2298_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg___boxed(
    mut v_pre_2303_: *mut LeanObject,
    mut v_s_2304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2305_: *mut LeanObject = core::ptr::null_mut();
    v_res_2305_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_2303_, v_s_2304_);
    lean_dec_ref(v_pre_2303_);
    return v_res_2305_;
}
pub unsafe fn l_String_dropPrefix___at___00String_stripPrefix_spec__0(
    mut v_pre_2306_: *mut LeanObject,
    mut v_s_2307_: *mut LeanObject,
    mut v_pat_2308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    v___x_2309_ = lean_unsigned_to_nat(0);
    v___x_2310_ = lean_string_utf8_byte_size(v_s_2307_);
    v___x_2311_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2311_, 0, v_s_2307_);
    lean_ctor_set(v___x_2311_, 1, v___x_2309_);
    lean_ctor_set(v___x_2311_, 2, v___x_2310_);
    v___x_2312_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_2306_, v___x_2311_);
    return v___x_2312_;
}
pub unsafe fn l_String_dropPrefix___at___00String_stripPrefix_spec__0___boxed(
    mut v_pre_2313_: *mut LeanObject,
    mut v_s_2314_: *mut LeanObject,
    mut v_pat_2315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2316_: *mut LeanObject = core::ptr::null_mut();
    v_res_2316_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(
        v_pre_2313_,
        v_s_2314_,
        v_pat_2315_,
    );
    lean_dec_ref(v_pat_2315_);
    lean_dec_ref(v_pre_2313_);
    return v_res_2316_;
}
pub unsafe fn l_String_stripPrefix(
    mut v_s_2317_: *mut LeanObject,
    mut v_pre_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut LeanObject = core::ptr::null_mut();
    v___x_2319_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(
        v_pre_2318_,
        v_s_2317_,
        v_pre_2318_,
    );
    v___x_2320_ = l_String_Slice_toString(v___x_2319_);
    lean_dec_ref(v___x_2319_);
    return v___x_2320_;
}
pub unsafe fn l_String_stripPrefix___boxed(
    mut v_s_2321_: *mut LeanObject,
    mut v_pre_2322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2323_: *mut LeanObject = core::ptr::null_mut();
    v_res_2323_ = l_String_stripPrefix(v_s_2321_, v_pre_2322_);
    lean_dec_ref(v_pre_2322_);
    return v_res_2323_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(
    mut v_pat_2324_: *mut LeanObject,
    mut v_pre_2325_: *mut LeanObject,
    mut v_s_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_2325_, v_s_2326_);
    return v___x_2327_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___boxed(
    mut v_pat_2328_: *mut LeanObject,
    mut v_pre_2329_: *mut LeanObject,
    mut v_s_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2331_: *mut LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(v_pat_2328_, v_pre_2329_, v_s_2330_);
    lean_dec_ref(v_pre_2329_);
    lean_dec_ref(v_pat_2328_);
    return v_res_2331_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(
    mut v_pre_2332_: *mut LeanObject,
    mut v_s_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: u8 = 0;
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2347_: u8 = 0;
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut v_unused_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2334_ = lean_ctor_get(v_pre_2332_, 0);
                v_startInclusive_2335_ = lean_ctor_get(v_pre_2332_, 1);
                v_endExclusive_2336_ = lean_ctor_get(v_pre_2332_, 2);
                v_str_2337_ = lean_ctor_get(v_s_2333_, 0);
                v_startInclusive_2338_ = lean_ctor_get(v_s_2333_, 1);
                v_endExclusive_2339_ = lean_ctor_get(v_s_2333_, 2);
                v___x_2340_ = lean_nat_sub(v_endExclusive_2336_, v_startInclusive_2335_);
                v___x_2341_ = lean_nat_sub(v_endExclusive_2339_, v_startInclusive_2338_);
                v___x_2342_ = lean_nat_dec_le(v___x_2340_, v___x_2341_);
                lean_dec(v___x_2341_);
                if v___x_2342_ == 0 {
                    lean_dec(v___x_2340_);
                    return v_s_2333_;
                } else {
                    v___x_2343_ = lean_string_memcmp(
                        v_str_2337_,
                        v_str_2334_,
                        v_startInclusive_2338_,
                        v_startInclusive_2335_,
                        v___x_2340_,
                    );
                    if v___x_2343_ == 0 {
                        lean_dec(v___x_2340_);
                        return v_s_2333_;
                    } else {
                        lean_inc(v_endExclusive_2339_);
                        lean_inc(v_startInclusive_2338_);
                        lean_inc_ref(v_str_2337_);
                        v___x_2344_ = l_String_Slice_pos_x21(v_s_2333_, v___x_2340_);
                        lean_dec(v___x_2340_);
                        v_isSharedCheck_2352_ = (!lean_is_exclusive(v_s_2333_)) as u8;
                        if v_isSharedCheck_2352_ == 0 {
                            v_unused_2353_ = lean_ctor_get(v_s_2333_, 2);
                            lean_dec(v_unused_2353_);
                            v_unused_2354_ = lean_ctor_get(v_s_2333_, 1);
                            lean_dec(v_unused_2354_);
                            v_unused_2355_ = lean_ctor_get(v_s_2333_, 0);
                            lean_dec(v_unused_2355_);
                            v___x_2346_ = v_s_2333_;
                            v_isShared_2347_ = v_isSharedCheck_2352_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_2333_);
                            v___x_2346_ = lean_box(0);
                            v_isShared_2347_ = v_isSharedCheck_2352_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2348_ = lean_nat_add(v_startInclusive_2338_, v___x_2344_);
                lean_dec(v___x_2344_);
                lean_dec(v_startInclusive_2338_);
                if v_isShared_2347_ == 0 {
                    lean_ctor_set(v___x_2346_, 1, v___x_2348_);
                    v___x_2350_ = v___x_2346_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_str_2337_);
                    lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___x_2348_);
                    lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_endExclusive_2339_);
                    v___x_2350_ = v_reuseFailAlloc_2351_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2350_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0___boxed(
    mut v_pre_2356_: *mut LeanObject,
    mut v_s_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2358_: *mut LeanObject = core::ptr::null_mut();
    v_res_2358_ =
        l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_2356_, v_s_2357_);
    lean_dec_ref(v_pre_2356_);
    return v_res_2358_;
}
pub unsafe fn l_String_Slice_stripPrefix(
    mut v_s_2359_: *mut LeanObject,
    mut v_pre_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    v___x_2361_ =
        l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_2360_, v_s_2359_);
    return v___x_2361_;
}
pub unsafe fn l_String_Slice_stripPrefix___boxed(
    mut v_s_2362_: *mut LeanObject,
    mut v_pre_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2364_: *mut LeanObject = core::ptr::null_mut();
    v_res_2364_ = l_String_Slice_stripPrefix(v_s_2362_, v_pre_2363_);
    lean_dec_ref(v_pre_2363_);
    return v_res_2364_;
}
pub unsafe fn l_String_dropSuffix___redArg(
    mut v_s_2365_: *mut LeanObject,
    mut v_inst_2366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    v___x_2367_ = lean_unsigned_to_nat(0);
    v___x_2368_ = lean_string_utf8_byte_size(v_s_2365_);
    v___x_2369_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2369_, 0, v_s_2365_);
    lean_ctor_set(v___x_2369_, 1, v___x_2367_);
    lean_ctor_set(v___x_2369_, 2, v___x_2368_);
    v___x_2370_ = l_String_Slice_dropSuffix___redArg(v___x_2369_, v_inst_2366_);
    return v___x_2370_;
}
pub unsafe fn l_String_dropSuffix(
    mut v_00_u03c1_2371_: *mut LeanObject,
    mut v_s_2372_: *mut LeanObject,
    mut v_pat_2373_: *mut LeanObject,
    mut v_inst_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    v___x_2375_ = l_String_dropSuffix___redArg(v_s_2372_, v_inst_2374_);
    return v___x_2375_;
}
pub unsafe fn l_String_dropSuffix___boxed(
    mut v_00_u03c1_2376_: *mut LeanObject,
    mut v_s_2377_: *mut LeanObject,
    mut v_pat_2378_: *mut LeanObject,
    mut v_inst_2379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2380_: *mut LeanObject = core::ptr::null_mut();
    v_res_2380_ = l_String_dropSuffix(v_00_u03c1_2376_, v_s_2377_, v_pat_2378_, v_inst_2379_);
    lean_dec(v_pat_2378_);
    return v_res_2380_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(
    mut v_suff_2381_: *mut LeanObject,
    mut v_s_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: u8 = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v_unused_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2383_ = lean_ctor_get(v_s_2382_, 0);
                v_startInclusive_2384_ = lean_ctor_get(v_s_2382_, 1);
                v_endExclusive_2385_ = lean_ctor_get(v_s_2382_, 2);
                v___x_2386_ = lean_string_utf8_byte_size(v_suff_2381_);
                v___x_2387_ = lean_nat_sub(v_endExclusive_2385_, v_startInclusive_2384_);
                v___x_2388_ = lean_nat_dec_le(v___x_2386_, v___x_2387_);
                if v___x_2388_ == 0 {
                    lean_dec(v___x_2387_);
                    return v_s_2382_;
                } else {
                    v___x_2389_ = lean_unsigned_to_nat(0);
                    v___x_2390_ = lean_nat_sub(v___x_2387_, v___x_2386_);
                    lean_dec(v___x_2387_);
                    v___x_2391_ = lean_nat_add(v_startInclusive_2384_, v___x_2390_);
                    v___x_2392_ = lean_string_memcmp(
                        v_str_2383_,
                        v_suff_2381_,
                        v___x_2391_,
                        v___x_2389_,
                        v___x_2386_,
                    );
                    lean_dec(v___x_2391_);
                    if v___x_2392_ == 0 {
                        lean_dec(v___x_2390_);
                        return v_s_2382_;
                    } else {
                        lean_inc(v_startInclusive_2384_);
                        lean_inc_ref(v_str_2383_);
                        v___x_2393_ = l_String_Slice_pos_x21(v_s_2382_, v___x_2390_);
                        lean_dec(v___x_2390_);
                        v_isSharedCheck_2401_ = (!lean_is_exclusive(v_s_2382_)) as u8;
                        if v_isSharedCheck_2401_ == 0 {
                            v_unused_2402_ = lean_ctor_get(v_s_2382_, 2);
                            lean_dec(v_unused_2402_);
                            v_unused_2403_ = lean_ctor_get(v_s_2382_, 1);
                            lean_dec(v_unused_2403_);
                            v_unused_2404_ = lean_ctor_get(v_s_2382_, 0);
                            lean_dec(v_unused_2404_);
                            v___x_2395_ = v_s_2382_;
                            v_isShared_2396_ = v_isSharedCheck_2401_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_2382_);
                            v___x_2395_ = lean_box(0);
                            v_isShared_2396_ = v_isSharedCheck_2401_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2397_ = lean_nat_add(v_startInclusive_2384_, v___x_2393_);
                lean_dec(v___x_2393_);
                if v_isShared_2396_ == 0 {
                    lean_ctor_set(v___x_2395_, 2, v___x_2397_);
                    v___x_2399_ = v___x_2395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_str_2383_);
                    lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_startInclusive_2384_);
                    lean_ctor_set(v_reuseFailAlloc_2400_, 2, v___x_2397_);
                    v___x_2399_ = v_reuseFailAlloc_2400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg___boxed(
    mut v_suff_2405_: *mut LeanObject,
    mut v_s_2406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2407_: *mut LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_2405_, v_s_2406_);
    lean_dec_ref(v_suff_2405_);
    return v_res_2407_;
}
pub unsafe fn l_String_dropSuffix___at___00String_stripSuffix_spec__0(
    mut v_suff_2408_: *mut LeanObject,
    mut v_s_2409_: *mut LeanObject,
    mut v_pat_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    v___x_2411_ = lean_unsigned_to_nat(0);
    v___x_2412_ = lean_string_utf8_byte_size(v_s_2409_);
    v___x_2413_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2413_, 0, v_s_2409_);
    lean_ctor_set(v___x_2413_, 1, v___x_2411_);
    lean_ctor_set(v___x_2413_, 2, v___x_2412_);
    v___x_2414_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_2408_, v___x_2413_);
    return v___x_2414_;
}
pub unsafe fn l_String_dropSuffix___at___00String_stripSuffix_spec__0___boxed(
    mut v_suff_2415_: *mut LeanObject,
    mut v_s_2416_: *mut LeanObject,
    mut v_pat_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2418_: *mut LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(
        v_suff_2415_,
        v_s_2416_,
        v_pat_2417_,
    );
    lean_dec_ref(v_pat_2417_);
    lean_dec_ref(v_suff_2415_);
    return v_res_2418_;
}
pub unsafe fn l_String_stripSuffix(
    mut v_s_2419_: *mut LeanObject,
    mut v_suff_2420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    v___x_2421_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(
        v_suff_2420_,
        v_s_2419_,
        v_suff_2420_,
    );
    v___x_2422_ = l_String_Slice_toString(v___x_2421_);
    lean_dec_ref(v___x_2421_);
    return v___x_2422_;
}
pub unsafe fn l_String_stripSuffix___boxed(
    mut v_s_2423_: *mut LeanObject,
    mut v_suff_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2425_: *mut LeanObject = core::ptr::null_mut();
    v_res_2425_ = l_String_stripSuffix(v_s_2423_, v_suff_2424_);
    lean_dec_ref(v_suff_2424_);
    return v_res_2425_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(
    mut v_pat_2426_: *mut LeanObject,
    mut v_suff_2427_: *mut LeanObject,
    mut v_s_2428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    v___x_2429_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_2427_, v_s_2428_);
    return v___x_2429_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___boxed(
    mut v_pat_2430_: *mut LeanObject,
    mut v_suff_2431_: *mut LeanObject,
    mut v_s_2432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2433_: *mut LeanObject = core::ptr::null_mut();
    v_res_2433_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(v_pat_2430_, v_suff_2431_, v_s_2432_);
    lean_dec_ref(v_suff_2431_);
    lean_dec_ref(v_pat_2430_);
    return v_res_2433_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(
    mut v_suff_2434_: *mut LeanObject,
    mut v_s_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2451_: u8 = 0;
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut v_unused_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2436_ = lean_ctor_get(v_suff_2434_, 0);
                v_startInclusive_2437_ = lean_ctor_get(v_suff_2434_, 1);
                v_endExclusive_2438_ = lean_ctor_get(v_suff_2434_, 2);
                v_str_2439_ = lean_ctor_get(v_s_2435_, 0);
                v_startInclusive_2440_ = lean_ctor_get(v_s_2435_, 1);
                v_endExclusive_2441_ = lean_ctor_get(v_s_2435_, 2);
                v___x_2442_ = lean_nat_sub(v_endExclusive_2438_, v_startInclusive_2437_);
                v___x_2443_ = lean_nat_sub(v_endExclusive_2441_, v_startInclusive_2440_);
                v___x_2444_ = lean_nat_dec_le(v___x_2442_, v___x_2443_);
                if v___x_2444_ == 0 {
                    lean_dec(v___x_2443_);
                    lean_dec(v___x_2442_);
                    return v_s_2435_;
                } else {
                    v___x_2445_ = lean_nat_sub(v___x_2443_, v___x_2442_);
                    lean_dec(v___x_2443_);
                    v___x_2446_ = lean_nat_add(v_startInclusive_2440_, v___x_2445_);
                    v___x_2447_ = lean_string_memcmp(
                        v_str_2439_,
                        v_str_2436_,
                        v___x_2446_,
                        v_startInclusive_2437_,
                        v___x_2442_,
                    );
                    lean_dec(v___x_2442_);
                    lean_dec(v___x_2446_);
                    if v___x_2447_ == 0 {
                        lean_dec(v___x_2445_);
                        return v_s_2435_;
                    } else {
                        lean_inc(v_startInclusive_2440_);
                        lean_inc_ref(v_str_2439_);
                        v___x_2448_ = l_String_Slice_pos_x21(v_s_2435_, v___x_2445_);
                        lean_dec(v___x_2445_);
                        v_isSharedCheck_2456_ = (!lean_is_exclusive(v_s_2435_)) as u8;
                        if v_isSharedCheck_2456_ == 0 {
                            v_unused_2457_ = lean_ctor_get(v_s_2435_, 2);
                            lean_dec(v_unused_2457_);
                            v_unused_2458_ = lean_ctor_get(v_s_2435_, 1);
                            lean_dec(v_unused_2458_);
                            v_unused_2459_ = lean_ctor_get(v_s_2435_, 0);
                            lean_dec(v_unused_2459_);
                            v___x_2450_ = v_s_2435_;
                            v_isShared_2451_ = v_isSharedCheck_2456_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_2435_);
                            v___x_2450_ = lean_box(0);
                            v_isShared_2451_ = v_isSharedCheck_2456_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2452_ = lean_nat_add(v_startInclusive_2440_, v___x_2448_);
                lean_dec(v___x_2448_);
                if v_isShared_2451_ == 0 {
                    lean_ctor_set(v___x_2450_, 2, v___x_2452_);
                    v___x_2454_ = v___x_2450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_str_2439_);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_startInclusive_2440_);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 2, v___x_2452_);
                    v___x_2454_ = v_reuseFailAlloc_2455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0___boxed(
    mut v_suff_2460_: *mut LeanObject,
    mut v_s_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2462_: *mut LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(
        v_suff_2460_,
        v_s_2461_,
    );
    lean_dec_ref(v_suff_2460_);
    return v_res_2462_;
}
pub unsafe fn l_String_Slice_stripSuffix(
    mut v_s_2463_: *mut LeanObject,
    mut v_suff_2464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    v___x_2465_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(
        v_suff_2464_,
        v_s_2463_,
    );
    return v___x_2465_;
}
pub unsafe fn l_String_Slice_stripSuffix___boxed(
    mut v_s_2466_: *mut LeanObject,
    mut v_suff_2467_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2468_: *mut LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_String_Slice_stripSuffix(v_s_2466_, v_suff_2467_);
    lean_dec_ref(v_suff_2467_);
    return v_res_2468_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_TakeDrop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Substring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_TakeDrop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_TakeDrop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Substring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_TakeDrop(builtin);
}
