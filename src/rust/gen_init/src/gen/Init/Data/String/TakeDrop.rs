// Lean compiler output
// Module: Init.Data.String.TakeDrop
// Imports: Init.Data.String.Substring
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_string_memcmp, lean_string_utf8_byte_size, lean_string_utf8_extract, lean_string_utf8_get,
    lean_string_utf8_get_fast, lean_string_utf8_next, lean_string_utf8_next_fast,
    lean_uint32_dec_eq,
};
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
pub static l_String_trimAsciiEnd___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Char_isWhitespace___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_String_trimAsciiEnd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_trimAsciiEnd___closed__0_value) as *mut leanh::LeanObject;
static mut l_String_trimAsciiEnd___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_trimAsciiEnd___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_trimAsciiStart___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_trimAsciiStart___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_String_drop(
    mut v_s_1235_: *mut leanh::LeanObject,
    mut v_n_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1237_ = leanh::lean_unsigned_to_nat(0);
    v___x_1238_ = lean_string_utf8_byte_size(v_s_1235_);
    leanh::lean_inc_ref(v_s_1235_);
    v___x_1239_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1239_, 0, v_s_1235_);
    leanh::lean_ctor_set(v___x_1239_, 1, v___x_1237_);
    leanh::lean_ctor_set(v___x_1239_, 2, v___x_1238_);
    v___x_1240_ = l_String_Slice_Pos_nextn(v___x_1239_, v___x_1237_, v_n_1236_);
    leanh::lean_dec_ref_known(v___x_1239_, 3);
    v___x_1241_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1241_, 0, v_s_1235_);
    leanh::lean_ctor_set(v___x_1241_, 1, v___x_1240_);
    leanh::lean_ctor_set(v___x_1241_, 2, v___x_1238_);
    return v___x_1241_;
}
pub unsafe fn lean_string_drop(
    mut v_s_1242_: *mut leanh::LeanObject,
    mut v_n_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1244_ = leanh::lean_unsigned_to_nat(0);
    v___x_1245_ = lean_string_utf8_byte_size(v_s_1242_);
    leanh::lean_inc_ref(v_s_1242_);
    v___x_1246_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1246_, 0, v_s_1242_);
    leanh::lean_ctor_set(v___x_1246_, 1, v___x_1244_);
    leanh::lean_ctor_set(v___x_1246_, 2, v___x_1245_);
    v___x_1247_ = l_String_Slice_Pos_nextn(v___x_1246_, v___x_1244_, v_n_1243_);
    leanh::lean_dec_ref_known(v___x_1246_, 3);
    v___x_1248_ = lean_string_utf8_extract(v_s_1242_, v___x_1247_, v___x_1245_);
    leanh::lean_dec(v___x_1247_);
    leanh::lean_dec_ref(v_s_1242_);
    return v___x_1248_;
}
pub unsafe fn l_String_dropEnd(
    mut v_s_1249_: *mut leanh::LeanObject,
    mut v_n_1250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1251_ = leanh::lean_unsigned_to_nat(0);
    v___x_1252_ = lean_string_utf8_byte_size(v_s_1249_);
    leanh::lean_inc_ref(v_s_1249_);
    v___x_1253_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1253_, 0, v_s_1249_);
    leanh::lean_ctor_set(v___x_1253_, 1, v___x_1251_);
    leanh::lean_ctor_set(v___x_1253_, 2, v___x_1252_);
    v___x_1254_ = l_String_Slice_Pos_prevn(v___x_1253_, v___x_1252_, v_n_1250_);
    leanh::lean_dec_ref_known(v___x_1253_, 3);
    v___x_1255_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1255_, 0, v_s_1249_);
    leanh::lean_ctor_set(v___x_1255_, 1, v___x_1251_);
    leanh::lean_ctor_set(v___x_1255_, 2, v___x_1254_);
    return v___x_1255_;
}
pub unsafe fn l_String_dropRight(
    mut v_s_1256_: *mut leanh::LeanObject,
    mut v_n_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1258_ = leanh::lean_unsigned_to_nat(0);
    v___x_1259_ = lean_string_utf8_byte_size(v_s_1256_);
    leanh::lean_inc_ref(v_s_1256_);
    v___x_1260_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1260_, 0, v_s_1256_);
    leanh::lean_ctor_set(v___x_1260_, 1, v___x_1258_);
    leanh::lean_ctor_set(v___x_1260_, 2, v___x_1259_);
    v___x_1261_ = l_String_Slice_Pos_prevn(v___x_1260_, v___x_1259_, v_n_1257_);
    leanh::lean_dec_ref_known(v___x_1260_, 3);
    v___x_1262_ = lean_string_utf8_extract(v_s_1256_, v___x_1258_, v___x_1261_);
    leanh::lean_dec(v___x_1261_);
    leanh::lean_dec_ref(v_s_1256_);
    return v___x_1262_;
}
pub unsafe fn l_String_Slice_dropRight(
    mut v_s_1263_: *mut leanh::LeanObject,
    mut v_n_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1272_: u8 = 0;
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1277_: u8 = 0;
    let mut v_unused_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1265_ = leanh::lean_ctor_get(v_s_1263_, 0);
                leanh::lean_inc_ref(v_str_1265_);
                v_startInclusive_1266_ = leanh::lean_ctor_get(v_s_1263_, 1);
                leanh::lean_inc(v_startInclusive_1266_);
                v_endExclusive_1267_ = leanh::lean_ctor_get(v_s_1263_, 2);
                v___x_1268_ = lean_nat_sub(v_endExclusive_1267_, v_startInclusive_1266_);
                v___x_1269_ = l_String_Slice_Pos_prevn(v_s_1263_, v___x_1268_, v_n_1264_);
                v_isSharedCheck_1277_ = (!leanh::lean_is_exclusive(v_s_1263_)) as u8;
                if v_isSharedCheck_1277_ == 0 {
                    v_unused_1278_ = leanh::lean_ctor_get(v_s_1263_, 2);
                    leanh::lean_dec(v_unused_1278_);
                    v_unused_1279_ = leanh::lean_ctor_get(v_s_1263_, 1);
                    leanh::lean_dec(v_unused_1279_);
                    v_unused_1280_ = leanh::lean_ctor_get(v_s_1263_, 0);
                    leanh::lean_dec(v_unused_1280_);
                    v___x_1271_ = v_s_1263_;
                    v_isShared_1272_ = v_isSharedCheck_1277_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_s_1263_);
                    v___x_1271_ = leanh::lean_box(0);
                    v_isShared_1272_ = v_isSharedCheck_1277_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1273_ = lean_nat_add(v_startInclusive_1266_, v___x_1269_);
                leanh::lean_dec(v___x_1269_);
                if v_isShared_1272_ == 0 {
                    leanh::lean_ctor_set(v___x_1271_, 2, v___x_1273_);
                    v___x_1275_ = v___x_1271_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1276_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_str_1265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 1, v_startInclusive_1266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1276_, 2, v___x_1273_);
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
    mut v_s_1281_: *mut leanh::LeanObject,
    mut v_n_1282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1283_ = leanh::lean_unsigned_to_nat(0);
    v___x_1284_ = lean_string_utf8_byte_size(v_s_1281_);
    leanh::lean_inc_ref(v_s_1281_);
    v___x_1285_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1285_, 0, v_s_1281_);
    leanh::lean_ctor_set(v___x_1285_, 1, v___x_1283_);
    leanh::lean_ctor_set(v___x_1285_, 2, v___x_1284_);
    v___x_1286_ = l_String_Slice_Pos_prevn(v___x_1285_, v___x_1284_, v_n_1282_);
    leanh::lean_dec_ref_known(v___x_1285_, 3);
    v___x_1287_ = lean_string_utf8_extract(v_s_1281_, v___x_1283_, v___x_1286_);
    leanh::lean_dec(v___x_1286_);
    leanh::lean_dec_ref(v_s_1281_);
    return v___x_1287_;
}
pub unsafe fn l_String_take(
    mut v_s_1288_: *mut leanh::LeanObject,
    mut v_n_1289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1290_ = leanh::lean_unsigned_to_nat(0);
    v___x_1291_ = lean_string_utf8_byte_size(v_s_1288_);
    leanh::lean_inc_ref(v_s_1288_);
    v___x_1292_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1292_, 0, v_s_1288_);
    leanh::lean_ctor_set(v___x_1292_, 1, v___x_1290_);
    leanh::lean_ctor_set(v___x_1292_, 2, v___x_1291_);
    v___x_1293_ = l_String_Slice_Pos_nextn(v___x_1292_, v___x_1290_, v_n_1289_);
    leanh::lean_dec_ref_known(v___x_1292_, 3);
    v___x_1294_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1294_, 0, v_s_1288_);
    leanh::lean_ctor_set(v___x_1294_, 1, v___x_1290_);
    leanh::lean_ctor_set(v___x_1294_, 2, v___x_1293_);
    return v___x_1294_;
}
pub unsafe fn l_String_takeEnd(
    mut v_s_1295_: *mut leanh::LeanObject,
    mut v_n_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1297_ = leanh::lean_unsigned_to_nat(0);
    v___x_1298_ = lean_string_utf8_byte_size(v_s_1295_);
    leanh::lean_inc_ref(v_s_1295_);
    v___x_1299_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1299_, 0, v_s_1295_);
    leanh::lean_ctor_set(v___x_1299_, 1, v___x_1297_);
    leanh::lean_ctor_set(v___x_1299_, 2, v___x_1298_);
    v___x_1300_ = l_String_Slice_Pos_prevn(v___x_1299_, v___x_1298_, v_n_1296_);
    leanh::lean_dec_ref_known(v___x_1299_, 3);
    v___x_1301_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1301_, 0, v_s_1295_);
    leanh::lean_ctor_set(v___x_1301_, 1, v___x_1300_);
    leanh::lean_ctor_set(v___x_1301_, 2, v___x_1298_);
    return v___x_1301_;
}
pub unsafe fn l_String_takeRight(
    mut v_s_1302_: *mut leanh::LeanObject,
    mut v_n_1303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = leanh::lean_unsigned_to_nat(0);
    v___x_1305_ = lean_string_utf8_byte_size(v_s_1302_);
    leanh::lean_inc_ref(v_s_1302_);
    v___x_1306_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1306_, 0, v_s_1302_);
    leanh::lean_ctor_set(v___x_1306_, 1, v___x_1304_);
    leanh::lean_ctor_set(v___x_1306_, 2, v___x_1305_);
    v___x_1307_ = l_String_Slice_Pos_prevn(v___x_1306_, v___x_1305_, v_n_1303_);
    leanh::lean_dec_ref_known(v___x_1306_, 3);
    v___x_1308_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1308_, 0, v_s_1302_);
    leanh::lean_ctor_set(v___x_1308_, 1, v___x_1307_);
    leanh::lean_ctor_set(v___x_1308_, 2, v___x_1305_);
    v___x_1309_ = l_String_Slice_toString(v___x_1308_);
    leanh::lean_dec_ref_known(v___x_1308_, 3);
    return v___x_1309_;
}
pub unsafe fn l_String_Slice_takeRight(
    mut v_s_1310_: *mut leanh::LeanObject,
    mut v_n_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1319_: u8 = 0;
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1324_: u8 = 0;
    let mut v_unused_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1312_ = leanh::lean_ctor_get(v_s_1310_, 0);
                leanh::lean_inc_ref(v_str_1312_);
                v_startInclusive_1313_ = leanh::lean_ctor_get(v_s_1310_, 1);
                leanh::lean_inc(v_startInclusive_1313_);
                v_endExclusive_1314_ = leanh::lean_ctor_get(v_s_1310_, 2);
                leanh::lean_inc(v_endExclusive_1314_);
                v___x_1315_ = lean_nat_sub(v_endExclusive_1314_, v_startInclusive_1313_);
                v___x_1316_ = l_String_Slice_Pos_prevn(v_s_1310_, v___x_1315_, v_n_1311_);
                v_isSharedCheck_1324_ = (!leanh::lean_is_exclusive(v_s_1310_)) as u8;
                if v_isSharedCheck_1324_ == 0 {
                    v_unused_1325_ = leanh::lean_ctor_get(v_s_1310_, 2);
                    leanh::lean_dec(v_unused_1325_);
                    v_unused_1326_ = leanh::lean_ctor_get(v_s_1310_, 1);
                    leanh::lean_dec(v_unused_1326_);
                    v_unused_1327_ = leanh::lean_ctor_get(v_s_1310_, 0);
                    leanh::lean_dec(v_unused_1327_);
                    v___x_1318_ = v_s_1310_;
                    v_isShared_1319_ = v_isSharedCheck_1324_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_s_1310_);
                    v___x_1318_ = leanh::lean_box(0);
                    v_isShared_1319_ = v_isSharedCheck_1324_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1320_ = lean_nat_add(v_startInclusive_1313_, v___x_1316_);
                leanh::lean_dec(v___x_1316_);
                leanh::lean_dec(v_startInclusive_1313_);
                if v_isShared_1319_ == 0 {
                    leanh::lean_ctor_set(v___x_1318_, 1, v___x_1320_);
                    v___x_1322_ = v___x_1318_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_str_1312_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1320_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_endExclusive_1314_);
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
    mut v_s_1328_: *mut leanh::LeanObject,
    mut v_inst_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1330_ = leanh::lean_unsigned_to_nat(0);
    v___x_1331_ = lean_string_utf8_byte_size(v_s_1328_);
    leanh::lean_inc_ref(v_s_1328_);
    v___x_1332_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1332_, 0, v_s_1328_);
    leanh::lean_ctor_set(v___x_1332_, 1, v___x_1330_);
    leanh::lean_ctor_set(v___x_1332_, 2, v___x_1331_);
    v___x_1333_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1332_, v___x_1330_, v_inst_1329_);
    leanh::lean_dec_ref_known(v___x_1332_, 3);
    v___x_1334_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1334_, 0, v_s_1328_);
    leanh::lean_ctor_set(v___x_1334_, 1, v___x_1330_);
    leanh::lean_ctor_set(v___x_1334_, 2, v___x_1333_);
    return v___x_1334_;
}
pub unsafe fn l_String_takeWhile(
    mut v_00_u03c1_1335_: *mut leanh::LeanObject,
    mut v_s_1336_: *mut leanh::LeanObject,
    mut v_pat_1337_: *mut leanh::LeanObject,
    mut v_inst_1338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = leanh::lean_unsigned_to_nat(0);
    v___x_1340_ = lean_string_utf8_byte_size(v_s_1336_);
    leanh::lean_inc_ref(v_s_1336_);
    v___x_1341_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1341_, 0, v_s_1336_);
    leanh::lean_ctor_set(v___x_1341_, 1, v___x_1339_);
    leanh::lean_ctor_set(v___x_1341_, 2, v___x_1340_);
    v___x_1342_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1341_, v___x_1339_, v_inst_1338_);
    leanh::lean_dec_ref_known(v___x_1341_, 3);
    v___x_1343_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1343_, 0, v_s_1336_);
    leanh::lean_ctor_set(v___x_1343_, 1, v___x_1339_);
    leanh::lean_ctor_set(v___x_1343_, 2, v___x_1342_);
    return v___x_1343_;
}
pub unsafe fn l_String_takeWhile___boxed(
    mut v_00_u03c1_1344_: *mut leanh::LeanObject,
    mut v_s_1345_: *mut leanh::LeanObject,
    mut v_pat_1346_: *mut leanh::LeanObject,
    mut v_inst_1347_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1348_ = l_String_takeWhile(v_00_u03c1_1344_, v_s_1345_, v_pat_1346_, v_inst_1347_);
    leanh::lean_dec(v_pat_1346_);
    return v_res_1348_;
}
pub unsafe fn l_String_dropWhile___redArg(
    mut v_s_1349_: *mut leanh::LeanObject,
    mut v_inst_1350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1351_ = leanh::lean_unsigned_to_nat(0);
    v___x_1352_ = lean_string_utf8_byte_size(v_s_1349_);
    leanh::lean_inc_ref(v_s_1349_);
    v___x_1353_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1353_, 0, v_s_1349_);
    leanh::lean_ctor_set(v___x_1353_, 1, v___x_1351_);
    leanh::lean_ctor_set(v___x_1353_, 2, v___x_1352_);
    v___x_1354_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1353_, v___x_1351_, v_inst_1350_);
    leanh::lean_dec_ref_known(v___x_1353_, 3);
    v___x_1355_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1355_, 0, v_s_1349_);
    leanh::lean_ctor_set(v___x_1355_, 1, v___x_1354_);
    leanh::lean_ctor_set(v___x_1355_, 2, v___x_1352_);
    return v___x_1355_;
}
pub unsafe fn l_String_dropWhile(
    mut v_00_u03c1_1356_: *mut leanh::LeanObject,
    mut v_s_1357_: *mut leanh::LeanObject,
    mut v_pat_1358_: *mut leanh::LeanObject,
    mut v_inst_1359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = leanh::lean_unsigned_to_nat(0);
    v___x_1361_ = lean_string_utf8_byte_size(v_s_1357_);
    leanh::lean_inc_ref(v_s_1357_);
    v___x_1362_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1362_, 0, v_s_1357_);
    leanh::lean_ctor_set(v___x_1362_, 1, v___x_1360_);
    leanh::lean_ctor_set(v___x_1362_, 2, v___x_1361_);
    v___x_1363_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1362_, v___x_1360_, v_inst_1359_);
    leanh::lean_dec_ref_known(v___x_1362_, 3);
    v___x_1364_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1364_, 0, v_s_1357_);
    leanh::lean_ctor_set(v___x_1364_, 1, v___x_1363_);
    leanh::lean_ctor_set(v___x_1364_, 2, v___x_1361_);
    return v___x_1364_;
}
pub unsafe fn l_String_dropWhile___boxed(
    mut v_00_u03c1_1365_: *mut leanh::LeanObject,
    mut v_s_1366_: *mut leanh::LeanObject,
    mut v_pat_1367_: *mut leanh::LeanObject,
    mut v_inst_1368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1369_ = l_String_dropWhile(v_00_u03c1_1365_, v_s_1366_, v_pat_1367_, v_inst_1368_);
    leanh::lean_dec(v_pat_1367_);
    return v_res_1369_;
}
pub unsafe fn l_String_takeEndWhile___redArg(
    mut v_s_1370_: *mut leanh::LeanObject,
    mut v_inst_1371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = leanh::lean_unsigned_to_nat(0);
    v___x_1373_ = lean_string_utf8_byte_size(v_s_1370_);
    leanh::lean_inc_ref(v_s_1370_);
    v___x_1374_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1374_, 0, v_s_1370_);
    leanh::lean_ctor_set(v___x_1374_, 1, v___x_1372_);
    leanh::lean_ctor_set(v___x_1374_, 2, v___x_1373_);
    v___x_1375_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1374_, v___x_1373_, v_inst_1371_);
    leanh::lean_dec_ref_known(v___x_1374_, 3);
    v___x_1376_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1376_, 0, v_s_1370_);
    leanh::lean_ctor_set(v___x_1376_, 1, v___x_1375_);
    leanh::lean_ctor_set(v___x_1376_, 2, v___x_1373_);
    return v___x_1376_;
}
pub unsafe fn l_String_takeEndWhile(
    mut v_00_u03c1_1377_: *mut leanh::LeanObject,
    mut v_s_1378_: *mut leanh::LeanObject,
    mut v_pat_1379_: *mut leanh::LeanObject,
    mut v_inst_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1381_ = leanh::lean_unsigned_to_nat(0);
    v___x_1382_ = lean_string_utf8_byte_size(v_s_1378_);
    leanh::lean_inc_ref(v_s_1378_);
    v___x_1383_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1383_, 0, v_s_1378_);
    leanh::lean_ctor_set(v___x_1383_, 1, v___x_1381_);
    leanh::lean_ctor_set(v___x_1383_, 2, v___x_1382_);
    v___x_1384_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1383_, v___x_1382_, v_inst_1380_);
    leanh::lean_dec_ref_known(v___x_1383_, 3);
    v___x_1385_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1385_, 0, v_s_1378_);
    leanh::lean_ctor_set(v___x_1385_, 1, v___x_1384_);
    leanh::lean_ctor_set(v___x_1385_, 2, v___x_1382_);
    return v___x_1385_;
}
pub unsafe fn l_String_takeEndWhile___boxed(
    mut v_00_u03c1_1386_: *mut leanh::LeanObject,
    mut v_s_1387_: *mut leanh::LeanObject,
    mut v_pat_1388_: *mut leanh::LeanObject,
    mut v_inst_1389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1390_ = l_String_takeEndWhile(v_00_u03c1_1386_, v_s_1387_, v_pat_1388_, v_inst_1389_);
    leanh::lean_dec(v_pat_1388_);
    return v_res_1390_;
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
    mut v_p_1391_: *mut leanh::LeanObject,
    mut v_s_1392_: *mut leanh::LeanObject,
    mut v_pos_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1405_: u32 = 0;
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1394_ = leanh::lean_ctor_get(v_s_1392_, 0);
                v_startInclusive_1395_ = leanh::lean_ctor_get(v_s_1392_, 1);
                v___x_1396_ = lean_nat_add(v_startInclusive_1395_, v_pos_1393_);
                v___x_1397_ = lean_nat_sub(v___x_1396_, v_startInclusive_1395_);
                v___x_1398_ = leanh::lean_unsigned_to_nat(0);
                v___x_1399_ = lean_nat_dec_eq(v___x_1397_, v___x_1398_);
                if v___x_1399_ == 0 {
                    leanh::lean_inc(v_startInclusive_1395_);
                    leanh::lean_inc_ref(v_str_1394_);
                    v___x_1400_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1400_, 0, v_str_1394_);
                    leanh::lean_ctor_set(v___x_1400_, 1, v_startInclusive_1395_);
                    leanh::lean_ctor_set(v___x_1400_, 2, v___x_1396_);
                    v___x_1401_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1402_ = lean_nat_sub(v___x_1397_, v___x_1401_);
                    leanh::lean_dec(v___x_1397_);
                    v___x_1403_ = l_String_Slice_posLE(v___x_1400_, v___x_1402_);
                    leanh::lean_dec_ref_known(v___x_1400_, 3);
                    v___x_1404_ = lean_nat_add(v_startInclusive_1395_, v___x_1403_);
                    v___x_1405_ = lean_string_utf8_get_fast(v_str_1394_, v___x_1404_);
                    leanh::lean_dec(v___x_1404_);
                    v___x_1406_ = leanh::lean_box_uint32(v___x_1405_);
                    leanh::lean_inc_ref(v_p_1391_);
                    v___x_1407_ = leanh::lean_apply_1(v_p_1391_, v___x_1406_);
                    v___x_1408_ = (leanh::lean_unbox(v___x_1407_) as u8);
                    if v___x_1408_ == 0 {
                        leanh::lean_dec(v___x_1403_);
                        leanh::lean_dec_ref(v_p_1391_);
                        return v_pos_1393_;
                    } else {
                        v___x_1409_ = lean_nat_dec_lt(v___x_1403_, v_pos_1393_);
                        if v___x_1409_ == 0 {
                            leanh::lean_dec(v___x_1403_);
                            leanh::lean_dec_ref(v_p_1391_);
                            return v_pos_1393_;
                        } else {
                            leanh::lean_dec(v_pos_1393_);
                            v_pos_1393_ = v___x_1403_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1397_);
                    leanh::lean_dec(v___x_1396_);
                    leanh::lean_dec_ref(v_p_1391_);
                    return v_pos_1393_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0___boxed(
    mut v_p_1411_: *mut leanh::LeanObject,
    mut v_s_1412_: *mut leanh::LeanObject,
    mut v_pos_1413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1414_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
        v_p_1411_,
        v_s_1412_,
        v_pos_1413_,
    );
    leanh::lean_dec_ref(v_s_1412_);
    return v_res_1414_;
}
pub unsafe fn l_String_takeRightWhile(
    mut v_s_1415_: *mut leanh::LeanObject,
    mut v_p_1416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1417_ = leanh::lean_unsigned_to_nat(0);
    v___x_1418_ = lean_string_utf8_byte_size(v_s_1415_);
    leanh::lean_inc_ref(v_s_1415_);
    v___x_1419_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1419_, 0, v_s_1415_);
    leanh::lean_ctor_set(v___x_1419_, 1, v___x_1417_);
    leanh::lean_ctor_set(v___x_1419_, 2, v___x_1418_);
    v___x_1420_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
        v_p_1416_,
        v___x_1419_,
        v___x_1418_,
    );
    leanh::lean_dec_ref_known(v___x_1419_, 3);
    v___x_1421_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1421_, 0, v_s_1415_);
    leanh::lean_ctor_set(v___x_1421_, 1, v___x_1420_);
    leanh::lean_ctor_set(v___x_1421_, 2, v___x_1418_);
    v___x_1422_ = l_String_Slice_toString(v___x_1421_);
    leanh::lean_dec_ref_known(v___x_1421_, 3);
    return v___x_1422_;
}
pub unsafe fn l_String_Slice_takeRightWhile(
    mut v_s_1423_: *mut leanh::LeanObject,
    mut v_p_1424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1432_: u8 = 0;
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1437_: u8 = 0;
    let mut v_unused_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1425_ = leanh::lean_ctor_get(v_s_1423_, 0);
                leanh::lean_inc_ref(v_str_1425_);
                v_startInclusive_1426_ = leanh::lean_ctor_get(v_s_1423_, 1);
                leanh::lean_inc(v_startInclusive_1426_);
                v_endExclusive_1427_ = leanh::lean_ctor_get(v_s_1423_, 2);
                leanh::lean_inc(v_endExclusive_1427_);
                v___x_1428_ = lean_nat_sub(v_endExclusive_1427_, v_startInclusive_1426_);
                v___x_1429_ =
                    l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
                        v_p_1424_,
                        v_s_1423_,
                        v___x_1428_,
                    );
                v_isSharedCheck_1437_ = (!leanh::lean_is_exclusive(v_s_1423_)) as u8;
                if v_isSharedCheck_1437_ == 0 {
                    v_unused_1438_ = leanh::lean_ctor_get(v_s_1423_, 2);
                    leanh::lean_dec(v_unused_1438_);
                    v_unused_1439_ = leanh::lean_ctor_get(v_s_1423_, 1);
                    leanh::lean_dec(v_unused_1439_);
                    v_unused_1440_ = leanh::lean_ctor_get(v_s_1423_, 0);
                    leanh::lean_dec(v_unused_1440_);
                    v___x_1431_ = v_s_1423_;
                    v_isShared_1432_ = v_isSharedCheck_1437_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_s_1423_);
                    v___x_1431_ = leanh::lean_box(0);
                    v_isShared_1432_ = v_isSharedCheck_1437_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1433_ = lean_nat_add(v_startInclusive_1426_, v___x_1429_);
                leanh::lean_dec(v___x_1429_);
                leanh::lean_dec(v_startInclusive_1426_);
                if v_isShared_1432_ == 0 {
                    leanh::lean_ctor_set(v___x_1431_, 1, v___x_1433_);
                    v___x_1435_ = v___x_1431_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1436_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_str_1425_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1436_, 1, v___x_1433_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1436_, 2, v_endExclusive_1427_);
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
    mut v_s_1441_: *mut leanh::LeanObject,
    mut v_inst_1442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1443_ = leanh::lean_unsigned_to_nat(0);
    v___x_1444_ = lean_string_utf8_byte_size(v_s_1441_);
    leanh::lean_inc_ref(v_s_1441_);
    v___x_1445_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1445_, 0, v_s_1441_);
    leanh::lean_ctor_set(v___x_1445_, 1, v___x_1443_);
    leanh::lean_ctor_set(v___x_1445_, 2, v___x_1444_);
    v___x_1446_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1445_, v___x_1444_, v_inst_1442_);
    leanh::lean_dec_ref_known(v___x_1445_, 3);
    v___x_1447_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1447_, 0, v_s_1441_);
    leanh::lean_ctor_set(v___x_1447_, 1, v___x_1443_);
    leanh::lean_ctor_set(v___x_1447_, 2, v___x_1446_);
    return v___x_1447_;
}
pub unsafe fn l_String_dropEndWhile(
    mut v_00_u03c1_1448_: *mut leanh::LeanObject,
    mut v_s_1449_: *mut leanh::LeanObject,
    mut v_pat_1450_: *mut leanh::LeanObject,
    mut v_inst_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = leanh::lean_unsigned_to_nat(0);
    v___x_1453_ = lean_string_utf8_byte_size(v_s_1449_);
    leanh::lean_inc_ref(v_s_1449_);
    v___x_1454_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1454_, 0, v_s_1449_);
    leanh::lean_ctor_set(v___x_1454_, 1, v___x_1452_);
    leanh::lean_ctor_set(v___x_1454_, 2, v___x_1453_);
    v___x_1455_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1454_, v___x_1453_, v_inst_1451_);
    leanh::lean_dec_ref_known(v___x_1454_, 3);
    v___x_1456_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1456_, 0, v_s_1449_);
    leanh::lean_ctor_set(v___x_1456_, 1, v___x_1452_);
    leanh::lean_ctor_set(v___x_1456_, 2, v___x_1455_);
    return v___x_1456_;
}
pub unsafe fn l_String_dropEndWhile___boxed(
    mut v_00_u03c1_1457_: *mut leanh::LeanObject,
    mut v_s_1458_: *mut leanh::LeanObject,
    mut v_pat_1459_: *mut leanh::LeanObject,
    mut v_inst_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1461_ = l_String_dropEndWhile(v_00_u03c1_1457_, v_s_1458_, v_pat_1459_, v_inst_1460_);
    leanh::lean_dec(v_pat_1459_);
    return v_res_1461_;
}
pub unsafe fn l_String_dropRightWhile(
    mut v_s_1462_: *mut leanh::LeanObject,
    mut v_p_1463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1464_ = leanh::lean_unsigned_to_nat(0);
    v___x_1465_ = lean_string_utf8_byte_size(v_s_1462_);
    leanh::lean_inc_ref(v_s_1462_);
    v___x_1466_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1466_, 0, v_s_1462_);
    leanh::lean_ctor_set(v___x_1466_, 1, v___x_1464_);
    leanh::lean_ctor_set(v___x_1466_, 2, v___x_1465_);
    v___x_1467_ = l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
        v_p_1463_,
        v___x_1466_,
        v___x_1465_,
    );
    leanh::lean_dec_ref_known(v___x_1466_, 3);
    v___x_1468_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1468_, 0, v_s_1462_);
    leanh::lean_ctor_set(v___x_1468_, 1, v___x_1464_);
    leanh::lean_ctor_set(v___x_1468_, 2, v___x_1467_);
    v___x_1469_ = l_String_Slice_toString(v___x_1468_);
    leanh::lean_dec_ref_known(v___x_1468_, 3);
    return v___x_1469_;
}
pub unsafe fn l_String_Slice_dropRightWhile(
    mut v_s_1470_: *mut leanh::LeanObject,
    mut v_p_1471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut v_unused_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1472_ = leanh::lean_ctor_get(v_s_1470_, 0);
                leanh::lean_inc_ref(v_str_1472_);
                v_startInclusive_1473_ = leanh::lean_ctor_get(v_s_1470_, 1);
                leanh::lean_inc(v_startInclusive_1473_);
                v_endExclusive_1474_ = leanh::lean_ctor_get(v_s_1470_, 2);
                v___x_1475_ = lean_nat_sub(v_endExclusive_1474_, v_startInclusive_1473_);
                v___x_1476_ =
                    l_String_Slice_Pos_revSkipWhile___at___00String_takeRightWhile_spec__0(
                        v_p_1471_,
                        v_s_1470_,
                        v___x_1475_,
                    );
                v_isSharedCheck_1484_ = (!leanh::lean_is_exclusive(v_s_1470_)) as u8;
                if v_isSharedCheck_1484_ == 0 {
                    v_unused_1485_ = leanh::lean_ctor_get(v_s_1470_, 2);
                    leanh::lean_dec(v_unused_1485_);
                    v_unused_1486_ = leanh::lean_ctor_get(v_s_1470_, 1);
                    leanh::lean_dec(v_unused_1486_);
                    v_unused_1487_ = leanh::lean_ctor_get(v_s_1470_, 0);
                    leanh::lean_dec(v_unused_1487_);
                    v___x_1478_ = v_s_1470_;
                    v_isShared_1479_ = v_isSharedCheck_1484_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_s_1470_);
                    v___x_1478_ = leanh::lean_box(0);
                    v_isShared_1479_ = v_isSharedCheck_1484_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1480_ = lean_nat_add(v_startInclusive_1473_, v___x_1476_);
                leanh::lean_dec(v___x_1476_);
                if v_isShared_1479_ == 0 {
                    leanh::lean_ctor_set(v___x_1478_, 2, v___x_1480_);
                    v___x_1482_ = v___x_1478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_str_1472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_startInclusive_1473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 2, v___x_1480_);
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
    mut v_s_1488_: *mut leanh::LeanObject,
    mut v_inst_1489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipPrefix_x3f_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1493_: u8 = 0;
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1503_: u8 = 0;
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1507_: u8 = 0;
    let mut v_reuseFailAlloc_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1509_: u8 = 0;
    let mut v_unused_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_1490_ = leanh::lean_ctor_get(v_inst_1489_, 0);
                v_isSharedCheck_1509_ = (!leanh::lean_is_exclusive(v_inst_1489_)) as u8;
                if v_isSharedCheck_1509_ == 0 {
                    v_unused_1510_ = leanh::lean_ctor_get(v_inst_1489_, 2);
                    leanh::lean_dec(v_unused_1510_);
                    v_unused_1511_ = leanh::lean_ctor_get(v_inst_1489_, 1);
                    leanh::lean_dec(v_unused_1511_);
                    v___x_1492_ = v_inst_1489_;
                    v_isShared_1493_ = v_isSharedCheck_1509_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipPrefix_x3f_1490_);
                    leanh::lean_dec(v_inst_1489_);
                    v___x_1492_ = leanh::lean_box(0);
                    v_isShared_1493_ = v_isSharedCheck_1509_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1494_ = lean_string_utf8_byte_size(v_s_1488_);
                v___x_1495_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1493_ == 0 {
                    leanh::lean_ctor_set(v___x_1492_, 2, v___x_1494_);
                    leanh::lean_ctor_set(v___x_1492_, 1, v___x_1495_);
                    leanh::lean_ctor_set(v___x_1492_, 0, v_s_1488_);
                    v___x_1497_ = v___x_1492_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 0, v_s_1488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 1, v___x_1495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 2, v___x_1494_);
                    v___x_1497_ = v_reuseFailAlloc_1508_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1498_ = leanh::lean_apply_1(v_skipPrefix_x3f_1490_, v___x_1497_);
                if leanh::lean_obj_tag(v___x_1498_) == 0 {
                    v___x_1499_ = leanh::lean_box(0);
                    return v___x_1499_;
                } else {
                    v_val_1500_ = leanh::lean_ctor_get(v___x_1498_, 0);
                    v_isSharedCheck_1507_ = (!leanh::lean_is_exclusive(v___x_1498_)) as u8;
                    if v_isSharedCheck_1507_ == 0 {
                        v___x_1502_ = v___x_1498_;
                        v_isShared_1503_ = v_isSharedCheck_1507_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1500_);
                        leanh::lean_dec(v___x_1498_);
                        v___x_1502_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1506_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_val_1500_);
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
    mut v_00_u03c1_1512_: *mut leanh::LeanObject,
    mut v_s_1513_: *mut leanh::LeanObject,
    mut v_pat_1514_: *mut leanh::LeanObject,
    mut v_inst_1515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipPrefix_x3f_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1519_: u8 = 0;
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1529_: u8 = 0;
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1533_: u8 = 0;
    let mut v_reuseFailAlloc_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1535_: u8 = 0;
    let mut v_unused_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_1516_ = leanh::lean_ctor_get(v_inst_1515_, 0);
                v_isSharedCheck_1535_ = (!leanh::lean_is_exclusive(v_inst_1515_)) as u8;
                if v_isSharedCheck_1535_ == 0 {
                    v_unused_1536_ = leanh::lean_ctor_get(v_inst_1515_, 2);
                    leanh::lean_dec(v_unused_1536_);
                    v_unused_1537_ = leanh::lean_ctor_get(v_inst_1515_, 1);
                    leanh::lean_dec(v_unused_1537_);
                    v___x_1518_ = v_inst_1515_;
                    v_isShared_1519_ = v_isSharedCheck_1535_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipPrefix_x3f_1516_);
                    leanh::lean_dec(v_inst_1515_);
                    v___x_1518_ = leanh::lean_box(0);
                    v_isShared_1519_ = v_isSharedCheck_1535_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1520_ = lean_string_utf8_byte_size(v_s_1513_);
                v___x_1521_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1519_ == 0 {
                    leanh::lean_ctor_set(v___x_1518_, 2, v___x_1520_);
                    leanh::lean_ctor_set(v___x_1518_, 1, v___x_1521_);
                    leanh::lean_ctor_set(v___x_1518_, 0, v_s_1513_);
                    v___x_1523_ = v___x_1518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1534_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 0, v_s_1513_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1534_, 2, v___x_1520_);
                    v___x_1523_ = v_reuseFailAlloc_1534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1524_ = leanh::lean_apply_1(v_skipPrefix_x3f_1516_, v___x_1523_);
                if leanh::lean_obj_tag(v___x_1524_) == 0 {
                    v___x_1525_ = leanh::lean_box(0);
                    return v___x_1525_;
                } else {
                    v_val_1526_ = leanh::lean_ctor_get(v___x_1524_, 0);
                    v_isSharedCheck_1533_ = (!leanh::lean_is_exclusive(v___x_1524_)) as u8;
                    if v_isSharedCheck_1533_ == 0 {
                        v___x_1528_ = v___x_1524_;
                        v_isShared_1529_ = v_isSharedCheck_1533_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1526_);
                        leanh::lean_dec(v___x_1524_);
                        v___x_1528_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_val_1526_);
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
    mut v_00_u03c1_1538_: *mut leanh::LeanObject,
    mut v_s_1539_: *mut leanh::LeanObject,
    mut v_pat_1540_: *mut leanh::LeanObject,
    mut v_inst_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1542_ = l_String_skipPrefix_x3f(v_00_u03c1_1538_, v_s_1539_, v_pat_1540_, v_inst_1541_);
    leanh::lean_dec(v_pat_1540_);
    return v_res_1542_;
}
pub unsafe fn l_String_skipPrefixWhile___redArg(
    mut v_s_1543_: *mut leanh::LeanObject,
    mut v_inst_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1545_ = leanh::lean_unsigned_to_nat(0);
    v___x_1546_ = lean_string_utf8_byte_size(v_s_1543_);
    v___x_1547_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1547_, 0, v_s_1543_);
    leanh::lean_ctor_set(v___x_1547_, 1, v___x_1545_);
    leanh::lean_ctor_set(v___x_1547_, 2, v___x_1546_);
    v___x_1548_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1547_, v___x_1545_, v_inst_1544_);
    leanh::lean_dec_ref_known(v___x_1547_, 3);
    return v___x_1548_;
}
pub unsafe fn l_String_skipPrefixWhile(
    mut v_00_u03c1_1549_: *mut leanh::LeanObject,
    mut v_s_1550_: *mut leanh::LeanObject,
    mut v_pat_1551_: *mut leanh::LeanObject,
    mut v_inst_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1553_ = leanh::lean_unsigned_to_nat(0);
    v___x_1554_ = lean_string_utf8_byte_size(v_s_1550_);
    v___x_1555_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1555_, 0, v_s_1550_);
    leanh::lean_ctor_set(v___x_1555_, 1, v___x_1553_);
    leanh::lean_ctor_set(v___x_1555_, 2, v___x_1554_);
    v___x_1556_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1555_, v___x_1553_, v_inst_1552_);
    leanh::lean_dec_ref_known(v___x_1555_, 3);
    return v___x_1556_;
}
pub unsafe fn l_String_skipPrefixWhile___boxed(
    mut v_00_u03c1_1557_: *mut leanh::LeanObject,
    mut v_s_1558_: *mut leanh::LeanObject,
    mut v_pat_1559_: *mut leanh::LeanObject,
    mut v_inst_1560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_String_skipPrefixWhile(v_00_u03c1_1557_, v_s_1558_, v_pat_1559_, v_inst_1560_);
    leanh::lean_dec(v_pat_1559_);
    return v_res_1561_;
}
pub unsafe fn l_String_all___redArg(
    mut v_s_1562_: *mut leanh::LeanObject,
    mut v_inst_1563_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: u8 = 0;
    v___x_1564_ = leanh::lean_unsigned_to_nat(0);
    v___x_1565_ = lean_string_utf8_byte_size(v_s_1562_);
    v___x_1566_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1566_, 0, v_s_1562_);
    leanh::lean_ctor_set(v___x_1566_, 1, v___x_1564_);
    leanh::lean_ctor_set(v___x_1566_, 2, v___x_1565_);
    v___x_1567_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1566_, v___x_1564_, v_inst_1563_);
    leanh::lean_dec_ref_known(v___x_1566_, 3);
    v___x_1568_ = lean_nat_dec_eq(v___x_1567_, v___x_1565_);
    leanh::lean_dec(v___x_1567_);
    return v___x_1568_;
}
pub unsafe fn l_String_all___redArg___boxed(
    mut v_s_1569_: *mut leanh::LeanObject,
    mut v_inst_1570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1571_: u8 = 0;
    let mut v_r_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_String_all___redArg(v_s_1569_, v_inst_1570_);
    v_r_1572_ = leanh::lean_box((v_res_1571_) as usize);
    return v_r_1572_;
}
pub unsafe fn l_String_all(
    mut v_00_u03c1_1573_: *mut leanh::LeanObject,
    mut v_s_1574_: *mut leanh::LeanObject,
    mut v_pat_1575_: *mut leanh::LeanObject,
    mut v_inst_1576_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: u8 = 0;
    v___x_1577_ = leanh::lean_unsigned_to_nat(0);
    v___x_1578_ = lean_string_utf8_byte_size(v_s_1574_);
    v___x_1579_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1579_, 0, v_s_1574_);
    leanh::lean_ctor_set(v___x_1579_, 1, v___x_1577_);
    leanh::lean_ctor_set(v___x_1579_, 2, v___x_1578_);
    v___x_1580_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1579_, v___x_1577_, v_inst_1576_);
    leanh::lean_dec_ref_known(v___x_1579_, 3);
    v___x_1581_ = lean_nat_dec_eq(v___x_1580_, v___x_1578_);
    leanh::lean_dec(v___x_1580_);
    return v___x_1581_;
}
pub unsafe fn l_String_all___boxed(
    mut v_00_u03c1_1582_: *mut leanh::LeanObject,
    mut v_s_1583_: *mut leanh::LeanObject,
    mut v_pat_1584_: *mut leanh::LeanObject,
    mut v_inst_1585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1586_: u8 = 0;
    let mut v_r_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1586_ = l_String_all(v_00_u03c1_1582_, v_s_1583_, v_pat_1584_, v_inst_1585_);
    leanh::lean_dec(v_pat_1584_);
    v_r_1587_ = leanh::lean_box((v_res_1586_) as usize);
    return v_r_1587_;
}
pub unsafe fn l_String_revAll___redArg(
    mut v_s_1588_: *mut leanh::LeanObject,
    mut v_inst_1589_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: u8 = 0;
    v___x_1590_ = leanh::lean_unsigned_to_nat(0);
    v___x_1591_ = lean_string_utf8_byte_size(v_s_1588_);
    v___x_1592_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1592_, 0, v_s_1588_);
    leanh::lean_ctor_set(v___x_1592_, 1, v___x_1590_);
    leanh::lean_ctor_set(v___x_1592_, 2, v___x_1591_);
    v___x_1593_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1592_, v___x_1591_, v_inst_1589_);
    leanh::lean_dec_ref_known(v___x_1592_, 3);
    v___x_1594_ = lean_nat_dec_eq(v___x_1593_, v___x_1590_);
    leanh::lean_dec(v___x_1593_);
    return v___x_1594_;
}
pub unsafe fn l_String_revAll___redArg___boxed(
    mut v_s_1595_: *mut leanh::LeanObject,
    mut v_inst_1596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1597_: u8 = 0;
    let mut v_r_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1597_ = l_String_revAll___redArg(v_s_1595_, v_inst_1596_);
    v_r_1598_ = leanh::lean_box((v_res_1597_) as usize);
    return v_r_1598_;
}
pub unsafe fn l_String_revAll(
    mut v_00_u03c1_1599_: *mut leanh::LeanObject,
    mut v_s_1600_: *mut leanh::LeanObject,
    mut v_pat_1601_: *mut leanh::LeanObject,
    mut v_inst_1602_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: u8 = 0;
    v___x_1603_ = leanh::lean_unsigned_to_nat(0);
    v___x_1604_ = lean_string_utf8_byte_size(v_s_1600_);
    v___x_1605_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1605_, 0, v_s_1600_);
    leanh::lean_ctor_set(v___x_1605_, 1, v___x_1603_);
    leanh::lean_ctor_set(v___x_1605_, 2, v___x_1604_);
    v___x_1606_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1605_, v___x_1604_, v_inst_1602_);
    leanh::lean_dec_ref_known(v___x_1605_, 3);
    v___x_1607_ = lean_nat_dec_eq(v___x_1606_, v___x_1603_);
    leanh::lean_dec(v___x_1606_);
    return v___x_1607_;
}
pub unsafe fn l_String_revAll___boxed(
    mut v_00_u03c1_1608_: *mut leanh::LeanObject,
    mut v_s_1609_: *mut leanh::LeanObject,
    mut v_pat_1610_: *mut leanh::LeanObject,
    mut v_inst_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1612_: u8 = 0;
    let mut v_r_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1612_ = l_String_revAll(v_00_u03c1_1608_, v_s_1609_, v_pat_1610_, v_inst_1611_);
    leanh::lean_dec(v_pat_1610_);
    v_r_1613_ = leanh::lean_box((v_res_1612_) as usize);
    return v_r_1613_;
}
pub unsafe fn l_String_Pos_skip_x3f___redArg(
    mut v_s_1614_: *mut leanh::LeanObject,
    mut v_pos_1615_: *mut leanh::LeanObject,
    mut v_inst_1616_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipPrefix_x3f_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1620_: u8 = 0;
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1629_: u8 = 0;
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1634_: u8 = 0;
    let mut v_reuseFailAlloc_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1636_: u8 = 0;
    let mut v_unused_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_1617_ = leanh::lean_ctor_get(v_inst_1616_, 0);
                v_isSharedCheck_1636_ = (!leanh::lean_is_exclusive(v_inst_1616_)) as u8;
                if v_isSharedCheck_1636_ == 0 {
                    v_unused_1637_ = leanh::lean_ctor_get(v_inst_1616_, 2);
                    leanh::lean_dec(v_unused_1637_);
                    v_unused_1638_ = leanh::lean_ctor_get(v_inst_1616_, 1);
                    leanh::lean_dec(v_unused_1638_);
                    v___x_1619_ = v_inst_1616_;
                    v_isShared_1620_ = v_isSharedCheck_1636_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipPrefix_x3f_1617_);
                    leanh::lean_dec(v_inst_1616_);
                    v___x_1619_ = leanh::lean_box(0);
                    v_isShared_1620_ = v_isSharedCheck_1636_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1621_ = lean_string_utf8_byte_size(v_s_1614_);
                leanh::lean_inc(v_pos_1615_);
                if v_isShared_1620_ == 0 {
                    leanh::lean_ctor_set(v___x_1619_, 2, v___x_1621_);
                    leanh::lean_ctor_set(v___x_1619_, 1, v_pos_1615_);
                    leanh::lean_ctor_set(v___x_1619_, 0, v_s_1614_);
                    v___x_1623_ = v___x_1619_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1635_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_s_1614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 1, v_pos_1615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1635_, 2, v___x_1621_);
                    v___x_1623_ = v_reuseFailAlloc_1635_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1624_ = leanh::lean_apply_1(v_skipPrefix_x3f_1617_, v___x_1623_);
                if leanh::lean_obj_tag(v___x_1624_) == 0 {
                    leanh::lean_dec(v_pos_1615_);
                    v___x_1625_ = leanh::lean_box(0);
                    return v___x_1625_;
                } else {
                    v_val_1626_ = leanh::lean_ctor_get(v___x_1624_, 0);
                    v_isSharedCheck_1634_ = (!leanh::lean_is_exclusive(v___x_1624_)) as u8;
                    if v_isSharedCheck_1634_ == 0 {
                        v___x_1628_ = v___x_1624_;
                        v_isShared_1629_ = v_isSharedCheck_1634_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1626_);
                        leanh::lean_dec(v___x_1624_);
                        v___x_1628_ = leanh::lean_box(0);
                        v_isShared_1629_ = v_isSharedCheck_1634_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1630_ = lean_nat_add(v_pos_1615_, v_val_1626_);
                leanh::lean_dec(v_val_1626_);
                leanh::lean_dec(v_pos_1615_);
                if v_isShared_1629_ == 0 {
                    leanh::lean_ctor_set(v___x_1628_, 0, v___x_1630_);
                    v___x_1632_ = v___x_1628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1633_, 0, v___x_1630_);
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
    mut v_00_u03c1_1639_: *mut leanh::LeanObject,
    mut v_s_1640_: *mut leanh::LeanObject,
    mut v_pos_1641_: *mut leanh::LeanObject,
    mut v_pat_1642_: *mut leanh::LeanObject,
    mut v_inst_1643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipPrefix_x3f_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1661_: u8 = 0;
    let mut v_reuseFailAlloc_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut v_unused_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_1644_ = leanh::lean_ctor_get(v_inst_1643_, 0);
                v_isSharedCheck_1663_ = (!leanh::lean_is_exclusive(v_inst_1643_)) as u8;
                if v_isSharedCheck_1663_ == 0 {
                    v_unused_1664_ = leanh::lean_ctor_get(v_inst_1643_, 2);
                    leanh::lean_dec(v_unused_1664_);
                    v_unused_1665_ = leanh::lean_ctor_get(v_inst_1643_, 1);
                    leanh::lean_dec(v_unused_1665_);
                    v___x_1646_ = v_inst_1643_;
                    v_isShared_1647_ = v_isSharedCheck_1663_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipPrefix_x3f_1644_);
                    leanh::lean_dec(v_inst_1643_);
                    v___x_1646_ = leanh::lean_box(0);
                    v_isShared_1647_ = v_isSharedCheck_1663_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1648_ = lean_string_utf8_byte_size(v_s_1640_);
                leanh::lean_inc(v_pos_1641_);
                if v_isShared_1647_ == 0 {
                    leanh::lean_ctor_set(v___x_1646_, 2, v___x_1648_);
                    leanh::lean_ctor_set(v___x_1646_, 1, v_pos_1641_);
                    leanh::lean_ctor_set(v___x_1646_, 0, v_s_1640_);
                    v___x_1650_ = v___x_1646_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1662_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_s_1640_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_pos_1641_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 2, v___x_1648_);
                    v___x_1650_ = v_reuseFailAlloc_1662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1651_ = leanh::lean_apply_1(v_skipPrefix_x3f_1644_, v___x_1650_);
                if leanh::lean_obj_tag(v___x_1651_) == 0 {
                    leanh::lean_dec(v_pos_1641_);
                    v___x_1652_ = leanh::lean_box(0);
                    return v___x_1652_;
                } else {
                    v_val_1653_ = leanh::lean_ctor_get(v___x_1651_, 0);
                    v_isSharedCheck_1661_ = (!leanh::lean_is_exclusive(v___x_1651_)) as u8;
                    if v_isSharedCheck_1661_ == 0 {
                        v___x_1655_ = v___x_1651_;
                        v_isShared_1656_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1653_);
                        leanh::lean_dec(v___x_1651_);
                        v___x_1655_ = leanh::lean_box(0);
                        v_isShared_1656_ = v_isSharedCheck_1661_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1657_ = lean_nat_add(v_pos_1641_, v_val_1653_);
                leanh::lean_dec(v_val_1653_);
                leanh::lean_dec(v_pos_1641_);
                if v_isShared_1656_ == 0 {
                    leanh::lean_ctor_set(v___x_1655_, 0, v___x_1657_);
                    v___x_1659_ = v___x_1655_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1660_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
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
    mut v_00_u03c1_1666_: *mut leanh::LeanObject,
    mut v_s_1667_: *mut leanh::LeanObject,
    mut v_pos_1668_: *mut leanh::LeanObject,
    mut v_pat_1669_: *mut leanh::LeanObject,
    mut v_inst_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1671_ = l_String_Pos_skip_x3f(
        v_00_u03c1_1666_,
        v_s_1667_,
        v_pos_1668_,
        v_pat_1669_,
        v_inst_1670_,
    );
    leanh::lean_dec(v_pat_1669_);
    return v_res_1671_;
}
pub unsafe fn l_String_Pos_skipWhile___redArg(
    mut v_s_1672_: *mut leanh::LeanObject,
    mut v_pos_1673_: *mut leanh::LeanObject,
    mut v_inst_1674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1675_ = leanh::lean_unsigned_to_nat(0);
    v___x_1676_ = lean_string_utf8_byte_size(v_s_1672_);
    v___x_1677_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1677_, 0, v_s_1672_);
    leanh::lean_ctor_set(v___x_1677_, 1, v___x_1675_);
    leanh::lean_ctor_set(v___x_1677_, 2, v___x_1676_);
    v___x_1678_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1677_, v_pos_1673_, v_inst_1674_);
    leanh::lean_dec_ref_known(v___x_1677_, 3);
    return v___x_1678_;
}
pub unsafe fn l_String_Pos_skipWhile(
    mut v_00_u03c1_1679_: *mut leanh::LeanObject,
    mut v_s_1680_: *mut leanh::LeanObject,
    mut v_pos_1681_: *mut leanh::LeanObject,
    mut v_pat_1682_: *mut leanh::LeanObject,
    mut v_inst_1683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1684_ = leanh::lean_unsigned_to_nat(0);
    v___x_1685_ = lean_string_utf8_byte_size(v_s_1680_);
    v___x_1686_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1686_, 0, v_s_1680_);
    leanh::lean_ctor_set(v___x_1686_, 1, v___x_1684_);
    leanh::lean_ctor_set(v___x_1686_, 2, v___x_1685_);
    v___x_1687_ = l_String_Slice_Pos_skipWhile___redArg(v___x_1686_, v_pos_1681_, v_inst_1683_);
    leanh::lean_dec_ref_known(v___x_1686_, 3);
    return v___x_1687_;
}
pub unsafe fn l_String_Pos_skipWhile___boxed(
    mut v_00_u03c1_1688_: *mut leanh::LeanObject,
    mut v_s_1689_: *mut leanh::LeanObject,
    mut v_pos_1690_: *mut leanh::LeanObject,
    mut v_pat_1691_: *mut leanh::LeanObject,
    mut v_inst_1692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_String_Pos_skipWhile(
        v_00_u03c1_1688_,
        v_s_1689_,
        v_pos_1690_,
        v_pat_1691_,
        v_inst_1692_,
    );
    leanh::lean_dec(v_pat_1691_);
    return v_res_1693_;
}
pub unsafe fn l_String_startsWith___redArg(
    mut v_s_1694_: *mut leanh::LeanObject,
    mut v_inst_1695_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_startsWith_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: u8 = 0;
    let mut v_reuseFailAlloc_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1707_: u8 = 0;
    let mut v_unused_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startsWith_1696_ = leanh::lean_ctor_get(v_inst_1695_, 2);
                v_isSharedCheck_1707_ = (!leanh::lean_is_exclusive(v_inst_1695_)) as u8;
                if v_isSharedCheck_1707_ == 0 {
                    v_unused_1708_ = leanh::lean_ctor_get(v_inst_1695_, 1);
                    leanh::lean_dec(v_unused_1708_);
                    v_unused_1709_ = leanh::lean_ctor_get(v_inst_1695_, 0);
                    leanh::lean_dec(v_unused_1709_);
                    v___x_1698_ = v_inst_1695_;
                    v_isShared_1699_ = v_isSharedCheck_1707_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_startsWith_1696_);
                    leanh::lean_dec(v_inst_1695_);
                    v___x_1698_ = leanh::lean_box(0);
                    v_isShared_1699_ = v_isSharedCheck_1707_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1700_ = lean_string_utf8_byte_size(v_s_1694_);
                v___x_1701_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1699_ == 0 {
                    leanh::lean_ctor_set(v___x_1698_, 2, v___x_1700_);
                    leanh::lean_ctor_set(v___x_1698_, 1, v___x_1701_);
                    leanh::lean_ctor_set(v___x_1698_, 0, v_s_1694_);
                    v___x_1703_ = v___x_1698_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1706_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 0, v_s_1694_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1706_, 2, v___x_1700_);
                    v___x_1703_ = v_reuseFailAlloc_1706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1704_ = leanh::lean_apply_1(v_startsWith_1696_, v___x_1703_);
                v___x_1705_ = (leanh::lean_unbox(v___x_1704_) as u8);
                return v___x_1705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_startsWith___redArg___boxed(
    mut v_s_1710_: *mut leanh::LeanObject,
    mut v_inst_1711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1712_: u8 = 0;
    let mut v_r_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_String_startsWith___redArg(v_s_1710_, v_inst_1711_);
    v_r_1713_ = leanh::lean_box((v_res_1712_) as usize);
    return v_r_1713_;
}
pub unsafe fn l_String_startsWith(
    mut v_00_u03c1_1714_: *mut leanh::LeanObject,
    mut v_s_1715_: *mut leanh::LeanObject,
    mut v_pat_1716_: *mut leanh::LeanObject,
    mut v_inst_1717_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_startsWith_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1721_: u8 = 0;
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: u8 = 0;
    let mut v_reuseFailAlloc_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut v_unused_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startsWith_1718_ = leanh::lean_ctor_get(v_inst_1717_, 2);
                v_isSharedCheck_1729_ = (!leanh::lean_is_exclusive(v_inst_1717_)) as u8;
                if v_isSharedCheck_1729_ == 0 {
                    v_unused_1730_ = leanh::lean_ctor_get(v_inst_1717_, 1);
                    leanh::lean_dec(v_unused_1730_);
                    v_unused_1731_ = leanh::lean_ctor_get(v_inst_1717_, 0);
                    leanh::lean_dec(v_unused_1731_);
                    v___x_1720_ = v_inst_1717_;
                    v_isShared_1721_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_startsWith_1718_);
                    leanh::lean_dec(v_inst_1717_);
                    v___x_1720_ = leanh::lean_box(0);
                    v_isShared_1721_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1722_ = lean_string_utf8_byte_size(v_s_1715_);
                v___x_1723_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1721_ == 0 {
                    leanh::lean_ctor_set(v___x_1720_, 2, v___x_1722_);
                    leanh::lean_ctor_set(v___x_1720_, 1, v___x_1723_);
                    leanh::lean_ctor_set(v___x_1720_, 0, v_s_1715_);
                    v___x_1725_ = v___x_1720_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_s_1715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 1, v___x_1723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 2, v___x_1722_);
                    v___x_1725_ = v_reuseFailAlloc_1728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1726_ = leanh::lean_apply_1(v_startsWith_1718_, v___x_1725_);
                v___x_1727_ = (leanh::lean_unbox(v___x_1726_) as u8);
                return v___x_1727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_startsWith___boxed(
    mut v_00_u03c1_1732_: *mut leanh::LeanObject,
    mut v_s_1733_: *mut leanh::LeanObject,
    mut v_pat_1734_: *mut leanh::LeanObject,
    mut v_inst_1735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1736_: u8 = 0;
    let mut v_r_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1736_ = l_String_startsWith(v_00_u03c1_1732_, v_s_1733_, v_pat_1734_, v_inst_1735_);
    leanh::lean_dec(v_pat_1734_);
    v_r_1737_ = leanh::lean_box((v_res_1736_) as usize);
    return v_r_1737_;
}
pub unsafe fn l_String_isPrefixOf(
    mut v_p_1738_: *mut leanh::LeanObject,
    mut v_s_1739_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: u8 = 0;
    v___x_1740_ = lean_string_utf8_byte_size(v_s_1739_);
    v___x_1741_ = lean_string_utf8_byte_size(v_p_1738_);
    v___x_1742_ = lean_nat_dec_le(v___x_1741_, v___x_1740_);
    if v___x_1742_ == 0 {
        return v___x_1742_;
    } else {
        let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: u8 = 0;
        v___x_1743_ = leanh::lean_unsigned_to_nat(0);
        v___x_1744_ =
            lean_string_memcmp(v_s_1739_, v_p_1738_, v___x_1743_, v___x_1743_, v___x_1741_);
        return v___x_1744_;
    }
}
pub unsafe fn l_String_isPrefixOf___boxed(
    mut v_p_1745_: *mut leanh::LeanObject,
    mut v_s_1746_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1747_: u8 = 0;
    let mut v_r_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_String_isPrefixOf(v_p_1745_, v_s_1746_);
    leanh::lean_dec_ref(v_s_1746_);
    leanh::lean_dec_ref(v_p_1745_);
    v_r_1748_ = leanh::lean_box((v_res_1747_) as usize);
    return v_r_1748_;
}
pub unsafe fn lean_string_isprefixof(
    mut v_p_1749_: *mut leanh::LeanObject,
    mut v_s_1750_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: u8 = 0;
    v___x_1751_ = lean_string_utf8_byte_size(v_s_1750_);
    v___x_1752_ = lean_string_utf8_byte_size(v_p_1749_);
    v___x_1753_ = lean_nat_dec_le(v___x_1752_, v___x_1751_);
    if v___x_1753_ == 0 {
        leanh::lean_dec_ref(v_s_1750_);
        leanh::lean_dec_ref(v_p_1749_);
        return v___x_1753_;
    } else {
        let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1755_: u8 = 0;
        v___x_1754_ = leanh::lean_unsigned_to_nat(0);
        v___x_1755_ =
            lean_string_memcmp(v_s_1750_, v_p_1749_, v___x_1754_, v___x_1754_, v___x_1752_);
        leanh::lean_dec_ref(v_p_1749_);
        leanh::lean_dec_ref(v_s_1750_);
        return v___x_1755_;
    }
}
pub unsafe fn l_String_Internal_isPrefixOfImpl___boxed(
    mut v_p_1756_: *mut leanh::LeanObject,
    mut v_s_1757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1758_: u8 = 0;
    let mut v_r_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1758_ = lean_string_isprefixof(v_p_1756_, v_s_1757_);
    v_r_1759_ = leanh::lean_box((v_res_1758_) as usize);
    return v_r_1759_;
}
pub unsafe fn l_String_endsWith___redArg(
    mut v_s_1760_: *mut leanh::LeanObject,
    mut v_inst_1761_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_endsWith_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1765_: u8 = 0;
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v_reuseFailAlloc_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1773_: u8 = 0;
    let mut v_unused_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_endsWith_1762_ = leanh::lean_ctor_get(v_inst_1761_, 2);
                v_isSharedCheck_1773_ = (!leanh::lean_is_exclusive(v_inst_1761_)) as u8;
                if v_isSharedCheck_1773_ == 0 {
                    v_unused_1774_ = leanh::lean_ctor_get(v_inst_1761_, 1);
                    leanh::lean_dec(v_unused_1774_);
                    v_unused_1775_ = leanh::lean_ctor_get(v_inst_1761_, 0);
                    leanh::lean_dec(v_unused_1775_);
                    v___x_1764_ = v_inst_1761_;
                    v_isShared_1765_ = v_isSharedCheck_1773_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_endsWith_1762_);
                    leanh::lean_dec(v_inst_1761_);
                    v___x_1764_ = leanh::lean_box(0);
                    v_isShared_1765_ = v_isSharedCheck_1773_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1766_ = lean_string_utf8_byte_size(v_s_1760_);
                v___x_1767_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1765_ == 0 {
                    leanh::lean_ctor_set(v___x_1764_, 2, v___x_1766_);
                    leanh::lean_ctor_set(v___x_1764_, 1, v___x_1767_);
                    leanh::lean_ctor_set(v___x_1764_, 0, v_s_1760_);
                    v___x_1769_ = v___x_1764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1772_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_s_1760_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 1, v___x_1767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1772_, 2, v___x_1766_);
                    v___x_1769_ = v_reuseFailAlloc_1772_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1770_ = leanh::lean_apply_1(v_endsWith_1762_, v___x_1769_);
                v___x_1771_ = (leanh::lean_unbox(v___x_1770_) as u8);
                return v___x_1771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_endsWith___redArg___boxed(
    mut v_s_1776_: *mut leanh::LeanObject,
    mut v_inst_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1778_: u8 = 0;
    let mut v_r_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1778_ = l_String_endsWith___redArg(v_s_1776_, v_inst_1777_);
    v_r_1779_ = leanh::lean_box((v_res_1778_) as usize);
    return v_r_1779_;
}
pub unsafe fn l_String_endsWith(
    mut v_00_u03c1_1780_: *mut leanh::LeanObject,
    mut v_s_1781_: *mut leanh::LeanObject,
    mut v_pat_1782_: *mut leanh::LeanObject,
    mut v_inst_1783_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_endsWith_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: u8 = 0;
    let mut v_reuseFailAlloc_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_unused_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_endsWith_1784_ = leanh::lean_ctor_get(v_inst_1783_, 2);
                v_isSharedCheck_1795_ = (!leanh::lean_is_exclusive(v_inst_1783_)) as u8;
                if v_isSharedCheck_1795_ == 0 {
                    v_unused_1796_ = leanh::lean_ctor_get(v_inst_1783_, 1);
                    leanh::lean_dec(v_unused_1796_);
                    v_unused_1797_ = leanh::lean_ctor_get(v_inst_1783_, 0);
                    leanh::lean_dec(v_unused_1797_);
                    v___x_1786_ = v_inst_1783_;
                    v_isShared_1787_ = v_isSharedCheck_1795_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_endsWith_1784_);
                    leanh::lean_dec(v_inst_1783_);
                    v___x_1786_ = leanh::lean_box(0);
                    v_isShared_1787_ = v_isSharedCheck_1795_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1788_ = lean_string_utf8_byte_size(v_s_1781_);
                v___x_1789_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1787_ == 0 {
                    leanh::lean_ctor_set(v___x_1786_, 2, v___x_1788_);
                    leanh::lean_ctor_set(v___x_1786_, 1, v___x_1789_);
                    leanh::lean_ctor_set(v___x_1786_, 0, v_s_1781_);
                    v___x_1791_ = v___x_1786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_s_1781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___x_1789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 2, v___x_1788_);
                    v___x_1791_ = v_reuseFailAlloc_1794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1792_ = leanh::lean_apply_1(v_endsWith_1784_, v___x_1791_);
                v___x_1793_ = (leanh::lean_unbox(v___x_1792_) as u8);
                return v___x_1793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_endsWith___boxed(
    mut v_00_u03c1_1798_: *mut leanh::LeanObject,
    mut v_s_1799_: *mut leanh::LeanObject,
    mut v_pat_1800_: *mut leanh::LeanObject,
    mut v_inst_1801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1802_: u8 = 0;
    let mut v_r_1803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1802_ = l_String_endsWith(v_00_u03c1_1798_, v_s_1799_, v_pat_1800_, v_inst_1801_);
    leanh::lean_dec(v_pat_1800_);
    v_r_1803_ = leanh::lean_box((v_res_1802_) as usize);
    return v_r_1803_;
}
pub unsafe fn l_String_skipSuffix_x3f___redArg(
    mut v_s_1804_: *mut leanh::LeanObject,
    mut v_inst_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipSuffix_x3f_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1819_: u8 = 0;
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1823_: u8 = 0;
    let mut v_reuseFailAlloc_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1825_: u8 = 0;
    let mut v_unused_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_1806_ = leanh::lean_ctor_get(v_inst_1805_, 0);
                v_isSharedCheck_1825_ = (!leanh::lean_is_exclusive(v_inst_1805_)) as u8;
                if v_isSharedCheck_1825_ == 0 {
                    v_unused_1826_ = leanh::lean_ctor_get(v_inst_1805_, 2);
                    leanh::lean_dec(v_unused_1826_);
                    v_unused_1827_ = leanh::lean_ctor_get(v_inst_1805_, 1);
                    leanh::lean_dec(v_unused_1827_);
                    v___x_1808_ = v_inst_1805_;
                    v_isShared_1809_ = v_isSharedCheck_1825_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipSuffix_x3f_1806_);
                    leanh::lean_dec(v_inst_1805_);
                    v___x_1808_ = leanh::lean_box(0);
                    v_isShared_1809_ = v_isSharedCheck_1825_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1810_ = lean_string_utf8_byte_size(v_s_1804_);
                v___x_1811_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1809_ == 0 {
                    leanh::lean_ctor_set(v___x_1808_, 2, v___x_1810_);
                    leanh::lean_ctor_set(v___x_1808_, 1, v___x_1811_);
                    leanh::lean_ctor_set(v___x_1808_, 0, v_s_1804_);
                    v___x_1813_ = v___x_1808_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1824_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_s_1804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 1, v___x_1811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1824_, 2, v___x_1810_);
                    v___x_1813_ = v_reuseFailAlloc_1824_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1814_ = leanh::lean_apply_1(v_skipSuffix_x3f_1806_, v___x_1813_);
                if leanh::lean_obj_tag(v___x_1814_) == 0 {
                    v___x_1815_ = leanh::lean_box(0);
                    return v___x_1815_;
                } else {
                    v_val_1816_ = leanh::lean_ctor_get(v___x_1814_, 0);
                    v_isSharedCheck_1823_ = (!leanh::lean_is_exclusive(v___x_1814_)) as u8;
                    if v_isSharedCheck_1823_ == 0 {
                        v___x_1818_ = v___x_1814_;
                        v_isShared_1819_ = v_isSharedCheck_1823_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1816_);
                        leanh::lean_dec(v___x_1814_);
                        v___x_1818_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1822_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1822_, 0, v_val_1816_);
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
    mut v_00_u03c1_1828_: *mut leanh::LeanObject,
    mut v_s_1829_: *mut leanh::LeanObject,
    mut v_pat_1830_: *mut leanh::LeanObject,
    mut v_inst_1831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipSuffix_x3f_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1845_: u8 = 0;
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1849_: u8 = 0;
    let mut v_reuseFailAlloc_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1851_: u8 = 0;
    let mut v_unused_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_1832_ = leanh::lean_ctor_get(v_inst_1831_, 0);
                v_isSharedCheck_1851_ = (!leanh::lean_is_exclusive(v_inst_1831_)) as u8;
                if v_isSharedCheck_1851_ == 0 {
                    v_unused_1852_ = leanh::lean_ctor_get(v_inst_1831_, 2);
                    leanh::lean_dec(v_unused_1852_);
                    v_unused_1853_ = leanh::lean_ctor_get(v_inst_1831_, 1);
                    leanh::lean_dec(v_unused_1853_);
                    v___x_1834_ = v_inst_1831_;
                    v_isShared_1835_ = v_isSharedCheck_1851_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipSuffix_x3f_1832_);
                    leanh::lean_dec(v_inst_1831_);
                    v___x_1834_ = leanh::lean_box(0);
                    v_isShared_1835_ = v_isSharedCheck_1851_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1836_ = lean_string_utf8_byte_size(v_s_1829_);
                v___x_1837_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1835_ == 0 {
                    leanh::lean_ctor_set(v___x_1834_, 2, v___x_1836_);
                    leanh::lean_ctor_set(v___x_1834_, 1, v___x_1837_);
                    leanh::lean_ctor_set(v___x_1834_, 0, v_s_1829_);
                    v___x_1839_ = v___x_1834_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1850_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_s_1829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1850_, 1, v___x_1837_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1850_, 2, v___x_1836_);
                    v___x_1839_ = v_reuseFailAlloc_1850_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1840_ = leanh::lean_apply_1(v_skipSuffix_x3f_1832_, v___x_1839_);
                if leanh::lean_obj_tag(v___x_1840_) == 0 {
                    v___x_1841_ = leanh::lean_box(0);
                    return v___x_1841_;
                } else {
                    v_val_1842_ = leanh::lean_ctor_get(v___x_1840_, 0);
                    v_isSharedCheck_1849_ = (!leanh::lean_is_exclusive(v___x_1840_)) as u8;
                    if v_isSharedCheck_1849_ == 0 {
                        v___x_1844_ = v___x_1840_;
                        v_isShared_1845_ = v_isSharedCheck_1849_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1842_);
                        leanh::lean_dec(v___x_1840_);
                        v___x_1844_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1848_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_val_1842_);
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
    mut v_00_u03c1_1854_: *mut leanh::LeanObject,
    mut v_s_1855_: *mut leanh::LeanObject,
    mut v_pat_1856_: *mut leanh::LeanObject,
    mut v_inst_1857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1858_ = l_String_skipSuffix_x3f(v_00_u03c1_1854_, v_s_1855_, v_pat_1856_, v_inst_1857_);
    leanh::lean_dec(v_pat_1856_);
    return v_res_1858_;
}
pub unsafe fn l_String_skipSuffixWhile___redArg(
    mut v_s_1859_: *mut leanh::LeanObject,
    mut v_inst_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = leanh::lean_unsigned_to_nat(0);
    v___x_1862_ = lean_string_utf8_byte_size(v_s_1859_);
    v___x_1863_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1863_, 0, v_s_1859_);
    leanh::lean_ctor_set(v___x_1863_, 1, v___x_1861_);
    leanh::lean_ctor_set(v___x_1863_, 2, v___x_1862_);
    v___x_1864_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1863_, v___x_1862_, v_inst_1860_);
    leanh::lean_dec_ref_known(v___x_1863_, 3);
    return v___x_1864_;
}
pub unsafe fn l_String_skipSuffixWhile(
    mut v_00_u03c1_1865_: *mut leanh::LeanObject,
    mut v_s_1866_: *mut leanh::LeanObject,
    mut v_pat_1867_: *mut leanh::LeanObject,
    mut v_inst_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1869_ = leanh::lean_unsigned_to_nat(0);
    v___x_1870_ = lean_string_utf8_byte_size(v_s_1866_);
    v___x_1871_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1871_, 0, v_s_1866_);
    leanh::lean_ctor_set(v___x_1871_, 1, v___x_1869_);
    leanh::lean_ctor_set(v___x_1871_, 2, v___x_1870_);
    v___x_1872_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1871_, v___x_1870_, v_inst_1868_);
    leanh::lean_dec_ref_known(v___x_1871_, 3);
    return v___x_1872_;
}
pub unsafe fn l_String_skipSuffixWhile___boxed(
    mut v_00_u03c1_1873_: *mut leanh::LeanObject,
    mut v_s_1874_: *mut leanh::LeanObject,
    mut v_pat_1875_: *mut leanh::LeanObject,
    mut v_inst_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_String_skipSuffixWhile(v_00_u03c1_1873_, v_s_1874_, v_pat_1875_, v_inst_1876_);
    leanh::lean_dec(v_pat_1875_);
    return v_res_1877_;
}
pub unsafe fn l_String_Pos_revSkip_x3f___redArg(
    mut v_s_1878_: *mut leanh::LeanObject,
    mut v_pos_1879_: *mut leanh::LeanObject,
    mut v_inst_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipSuffix_x3f_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1893_: u8 = 0;
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1897_: u8 = 0;
    let mut v_reuseFailAlloc_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_unused_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_1881_ = leanh::lean_ctor_get(v_inst_1880_, 0);
                v_isSharedCheck_1899_ = (!leanh::lean_is_exclusive(v_inst_1880_)) as u8;
                if v_isSharedCheck_1899_ == 0 {
                    v_unused_1900_ = leanh::lean_ctor_get(v_inst_1880_, 2);
                    leanh::lean_dec(v_unused_1900_);
                    v_unused_1901_ = leanh::lean_ctor_get(v_inst_1880_, 1);
                    leanh::lean_dec(v_unused_1901_);
                    v___x_1883_ = v_inst_1880_;
                    v_isShared_1884_ = v_isSharedCheck_1899_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipSuffix_x3f_1881_);
                    leanh::lean_dec(v_inst_1880_);
                    v___x_1883_ = leanh::lean_box(0);
                    v_isShared_1884_ = v_isSharedCheck_1899_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1885_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1884_ == 0 {
                    leanh::lean_ctor_set(v___x_1883_, 2, v_pos_1879_);
                    leanh::lean_ctor_set(v___x_1883_, 1, v___x_1885_);
                    leanh::lean_ctor_set(v___x_1883_, 0, v_s_1878_);
                    v___x_1887_ = v___x_1883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1898_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_s_1878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 1, v___x_1885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1898_, 2, v_pos_1879_);
                    v___x_1887_ = v_reuseFailAlloc_1898_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1888_ = leanh::lean_apply_1(v_skipSuffix_x3f_1881_, v___x_1887_);
                if leanh::lean_obj_tag(v___x_1888_) == 0 {
                    v___x_1889_ = leanh::lean_box(0);
                    return v___x_1889_;
                } else {
                    v_val_1890_ = leanh::lean_ctor_get(v___x_1888_, 0);
                    v_isSharedCheck_1897_ = (!leanh::lean_is_exclusive(v___x_1888_)) as u8;
                    if v_isSharedCheck_1897_ == 0 {
                        v___x_1892_ = v___x_1888_;
                        v_isShared_1893_ = v_isSharedCheck_1897_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1890_);
                        leanh::lean_dec(v___x_1888_);
                        v___x_1892_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1896_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_val_1890_);
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
    mut v_00_u03c1_1902_: *mut leanh::LeanObject,
    mut v_s_1903_: *mut leanh::LeanObject,
    mut v_pos_1904_: *mut leanh::LeanObject,
    mut v_pat_1905_: *mut leanh::LeanObject,
    mut v_inst_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipSuffix_x3f_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1910_: u8 = 0;
    let mut v___x_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1919_: u8 = 0;
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut v_reuseFailAlloc_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1925_: u8 = 0;
    let mut v_unused_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_1907_ = leanh::lean_ctor_get(v_inst_1906_, 0);
                v_isSharedCheck_1925_ = (!leanh::lean_is_exclusive(v_inst_1906_)) as u8;
                if v_isSharedCheck_1925_ == 0 {
                    v_unused_1926_ = leanh::lean_ctor_get(v_inst_1906_, 2);
                    leanh::lean_dec(v_unused_1926_);
                    v_unused_1927_ = leanh::lean_ctor_get(v_inst_1906_, 1);
                    leanh::lean_dec(v_unused_1927_);
                    v___x_1909_ = v_inst_1906_;
                    v_isShared_1910_ = v_isSharedCheck_1925_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipSuffix_x3f_1907_);
                    leanh::lean_dec(v_inst_1906_);
                    v___x_1909_ = leanh::lean_box(0);
                    v_isShared_1910_ = v_isSharedCheck_1925_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1911_ = leanh::lean_unsigned_to_nat(0);
                if v_isShared_1910_ == 0 {
                    leanh::lean_ctor_set(v___x_1909_, 2, v_pos_1904_);
                    leanh::lean_ctor_set(v___x_1909_, 1, v___x_1911_);
                    leanh::lean_ctor_set(v___x_1909_, 0, v_s_1903_);
                    v___x_1913_ = v___x_1909_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1924_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_s_1903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 1, v___x_1911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_pos_1904_);
                    v___x_1913_ = v_reuseFailAlloc_1924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1914_ = leanh::lean_apply_1(v_skipSuffix_x3f_1907_, v___x_1913_);
                if leanh::lean_obj_tag(v___x_1914_) == 0 {
                    v___x_1915_ = leanh::lean_box(0);
                    return v___x_1915_;
                } else {
                    v_val_1916_ = leanh::lean_ctor_get(v___x_1914_, 0);
                    v_isSharedCheck_1923_ = (!leanh::lean_is_exclusive(v___x_1914_)) as u8;
                    if v_isSharedCheck_1923_ == 0 {
                        v___x_1918_ = v___x_1914_;
                        v_isShared_1919_ = v_isSharedCheck_1923_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1916_);
                        leanh::lean_dec(v___x_1914_);
                        v___x_1918_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_val_1916_);
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
    mut v_00_u03c1_1928_: *mut leanh::LeanObject,
    mut v_s_1929_: *mut leanh::LeanObject,
    mut v_pos_1930_: *mut leanh::LeanObject,
    mut v_pat_1931_: *mut leanh::LeanObject,
    mut v_inst_1932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_String_Pos_revSkip_x3f(
        v_00_u03c1_1928_,
        v_s_1929_,
        v_pos_1930_,
        v_pat_1931_,
        v_inst_1932_,
    );
    leanh::lean_dec(v_pat_1931_);
    return v_res_1933_;
}
pub unsafe fn l_String_Pos_revSkipWhile___redArg(
    mut v_s_1934_: *mut leanh::LeanObject,
    mut v_pos_1935_: *mut leanh::LeanObject,
    mut v_inst_1936_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1937_ = leanh::lean_unsigned_to_nat(0);
    v___x_1938_ = lean_string_utf8_byte_size(v_s_1934_);
    v___x_1939_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1939_, 0, v_s_1934_);
    leanh::lean_ctor_set(v___x_1939_, 1, v___x_1937_);
    leanh::lean_ctor_set(v___x_1939_, 2, v___x_1938_);
    v___x_1940_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1939_, v_pos_1935_, v_inst_1936_);
    leanh::lean_dec_ref_known(v___x_1939_, 3);
    return v___x_1940_;
}
pub unsafe fn l_String_Pos_revSkipWhile(
    mut v_00_u03c1_1941_: *mut leanh::LeanObject,
    mut v_s_1942_: *mut leanh::LeanObject,
    mut v_pos_1943_: *mut leanh::LeanObject,
    mut v_pat_1944_: *mut leanh::LeanObject,
    mut v_inst_1945_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1946_ = leanh::lean_unsigned_to_nat(0);
    v___x_1947_ = lean_string_utf8_byte_size(v_s_1942_);
    v___x_1948_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1948_, 0, v_s_1942_);
    leanh::lean_ctor_set(v___x_1948_, 1, v___x_1946_);
    leanh::lean_ctor_set(v___x_1948_, 2, v___x_1947_);
    v___x_1949_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1948_, v_pos_1943_, v_inst_1945_);
    leanh::lean_dec_ref_known(v___x_1948_, 3);
    return v___x_1949_;
}
pub unsafe fn l_String_Pos_revSkipWhile___boxed(
    mut v_00_u03c1_1950_: *mut leanh::LeanObject,
    mut v_s_1951_: *mut leanh::LeanObject,
    mut v_pos_1952_: *mut leanh::LeanObject,
    mut v_pat_1953_: *mut leanh::LeanObject,
    mut v_inst_1954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_String_Pos_revSkipWhile(
        v_00_u03c1_1950_,
        v_s_1951_,
        v_pos_1952_,
        v_pat_1953_,
        v_inst_1954_,
    );
    leanh::lean_dec(v_pat_1953_);
    return v_res_1955_;
}
pub unsafe fn _init_l_String_trimAsciiEnd___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1957_ = l_String_trimAsciiEnd___closed__0;
    v___x_1958_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_1957_);
    return v___x_1958_;
}
pub unsafe fn l_String_trimAsciiEnd(
    mut v_s_1959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1960_ = leanh::lean_unsigned_to_nat(0);
    v___x_1961_ = lean_string_utf8_byte_size(v_s_1959_);
    leanh::lean_inc_ref(v_s_1959_);
    v___x_1962_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1962_, 0, v_s_1959_);
    leanh::lean_ctor_set(v___x_1962_, 1, v___x_1960_);
    leanh::lean_ctor_set(v___x_1962_, 2, v___x_1961_);
    v___x_1963_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_String_trimAsciiEnd___closed__1),
        core::ptr::addr_of_mut!(l_String_trimAsciiEnd___closed__1_once),
        _init_l_String_trimAsciiEnd___closed__1,
    );
    v___x_1964_ = l_String_Slice_Pos_revSkipWhile___redArg(v___x_1962_, v___x_1961_, v___x_1963_);
    leanh::lean_dec_ref_known(v___x_1962_, 3);
    v___x_1965_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1965_, 0, v_s_1959_);
    leanh::lean_ctor_set(v___x_1965_, 1, v___x_1960_);
    leanh::lean_ctor_set(v___x_1965_, 2, v___x_1964_);
    return v___x_1965_;
}
pub unsafe fn l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(
    mut v_s_1966_: *mut leanh::LeanObject,
    mut v_pos_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: u8 = 0;
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: u8 = 0;
    let mut v___y_1982_: u8 = 0;
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v_str_1968_ = leanh::lean_ctor_get(v_s_1966_, 0);
                v_startInclusive_1969_ = leanh::lean_ctor_get(v_s_1966_, 1);
                v___x_1970_ = lean_nat_add(v_startInclusive_1969_, v_pos_1967_);
                v___x_1971_ = lean_nat_sub(v___x_1970_, v_startInclusive_1969_);
                v___x_1972_ = leanh::lean_unsigned_to_nat(0);
                v___x_1973_ = lean_nat_dec_eq(v___x_1971_, v___x_1972_);
                if v___x_1973_ == 0 {
                    leanh::lean_inc(v_startInclusive_1969_);
                    leanh::lean_inc_ref(v_str_1968_);
                    v___x_1974_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1974_, 0, v_str_1968_);
                    leanh::lean_ctor_set(v___x_1974_, 1, v_startInclusive_1969_);
                    leanh::lean_ctor_set(v___x_1974_, 2, v___x_1970_);
                    v___x_1975_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1976_ = lean_nat_sub(v___x_1971_, v___x_1975_);
                    leanh::lean_dec(v___x_1971_);
                    v___x_1977_ = l_String_Slice_posLE(v___x_1974_, v___x_1976_);
                    leanh::lean_dec_ref_known(v___x_1974_, 3);
                    v___x_1983_ = lean_nat_add(v_startInclusive_1969_, v___x_1977_);
                    v___x_1984_ = lean_string_utf8_get_fast(v_str_1968_, v___x_1983_);
                    leanh::lean_dec(v___x_1983_);
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
                    leanh::lean_dec(v___x_1971_);
                    leanh::lean_dec(v___x_1970_);
                    return v_pos_1967_;
                }
            }
            1 => {
                v___x_1979_ = lean_nat_dec_lt(v___x_1977_, v_pos_1967_);
                if v___x_1979_ == 0 {
                    leanh::lean_dec(v___x_1977_);
                    return v_pos_1967_;
                } else {
                    leanh::lean_dec(v_pos_1967_);
                    v_pos_1967_ = v___x_1977_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_1982_ == 0 {
                    leanh::lean_dec(v___x_1977_);
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
    mut v_s_1995_: *mut leanh::LeanObject,
    mut v_pos_1996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1997_ =
        l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v_s_1995_, v_pos_1996_);
    leanh::lean_dec_ref(v_s_1995_);
    return v_res_1997_;
}
pub unsafe fn l_String_trimRight(
    mut v_s_1998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1999_ = leanh::lean_unsigned_to_nat(0);
    v___x_2000_ = lean_string_utf8_byte_size(v_s_1998_);
    leanh::lean_inc_ref(v_s_1998_);
    v___x_2001_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2001_, 0, v_s_1998_);
    leanh::lean_ctor_set(v___x_2001_, 1, v___x_1999_);
    leanh::lean_ctor_set(v___x_2001_, 2, v___x_2000_);
    v___x_2002_ =
        l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(v___x_2001_, v___x_2000_);
    leanh::lean_dec_ref_known(v___x_2001_, 3);
    v___x_2003_ = lean_string_utf8_extract(v_s_1998_, v___x_1999_, v___x_2002_);
    leanh::lean_dec(v___x_2002_);
    leanh::lean_dec_ref(v_s_1998_);
    return v___x_2003_;
}
pub unsafe fn l_String_Slice_trimRight(
    mut v_s_2004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_unused_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2005_ = leanh::lean_ctor_get(v_s_2004_, 0);
                leanh::lean_inc_ref(v_str_2005_);
                v_startInclusive_2006_ = leanh::lean_ctor_get(v_s_2004_, 1);
                leanh::lean_inc(v_startInclusive_2006_);
                v_endExclusive_2007_ = leanh::lean_ctor_get(v_s_2004_, 2);
                v___x_2008_ = lean_nat_sub(v_endExclusive_2007_, v_startInclusive_2006_);
                v___x_2009_ = l_String_Slice_Pos_revSkipWhile___at___00String_trimRight_spec__0(
                    v_s_2004_,
                    v___x_2008_,
                );
                v_isSharedCheck_2017_ = (!leanh::lean_is_exclusive(v_s_2004_)) as u8;
                if v_isSharedCheck_2017_ == 0 {
                    v_unused_2018_ = leanh::lean_ctor_get(v_s_2004_, 2);
                    leanh::lean_dec(v_unused_2018_);
                    v_unused_2019_ = leanh::lean_ctor_get(v_s_2004_, 1);
                    leanh::lean_dec(v_unused_2019_);
                    v_unused_2020_ = leanh::lean_ctor_get(v_s_2004_, 0);
                    leanh::lean_dec(v_unused_2020_);
                    v___x_2011_ = v_s_2004_;
                    v_isShared_2012_ = v_isSharedCheck_2017_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_s_2004_);
                    v___x_2011_ = leanh::lean_box(0);
                    v_isShared_2012_ = v_isSharedCheck_2017_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2013_ = lean_nat_add(v_startInclusive_2006_, v___x_2009_);
                leanh::lean_dec(v___x_2009_);
                if v_isShared_2012_ == 0 {
                    leanh::lean_ctor_set(v___x_2011_, 2, v___x_2013_);
                    v___x_2015_ = v___x_2011_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2016_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_str_2005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 1, v_startInclusive_2006_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2016_, 2, v___x_2013_);
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
pub unsafe fn _init_l_String_trimAsciiStart___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2021_ = l_String_trimAsciiEnd___closed__0;
    v___x_2022_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_2021_);
    return v___x_2022_;
}
pub unsafe fn l_String_trimAsciiStart(
    mut v_s_2023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2024_ = leanh::lean_unsigned_to_nat(0);
    v___x_2025_ = lean_string_utf8_byte_size(v_s_2023_);
    leanh::lean_inc_ref(v_s_2023_);
    v___x_2026_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2026_, 0, v_s_2023_);
    leanh::lean_ctor_set(v___x_2026_, 1, v___x_2024_);
    leanh::lean_ctor_set(v___x_2026_, 2, v___x_2025_);
    v___x_2027_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_String_trimAsciiStart___closed__0),
        core::ptr::addr_of_mut!(l_String_trimAsciiStart___closed__0_once),
        _init_l_String_trimAsciiStart___closed__0,
    );
    v___x_2028_ = l_String_Slice_Pos_skipWhile___redArg(v___x_2026_, v___x_2024_, v___x_2027_);
    leanh::lean_dec_ref_known(v___x_2026_, 3);
    v___x_2029_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2029_, 0, v_s_2023_);
    leanh::lean_ctor_set(v___x_2029_, 1, v___x_2028_);
    leanh::lean_ctor_set(v___x_2029_, 2, v___x_2025_);
    return v___x_2029_;
}
pub unsafe fn l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(
    mut v_s_2030_: *mut leanh::LeanObject,
    mut v_pos_2031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: u8 = 0;
    let mut v___y_2043_: u8 = 0;
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                v_str_2032_ = leanh::lean_ctor_get(v_s_2030_, 0);
                v_startInclusive_2033_ = leanh::lean_ctor_get(v_s_2030_, 1);
                v_endExclusive_2034_ = leanh::lean_ctor_get(v_s_2030_, 2);
                v___x_2035_ = lean_nat_add(v_startInclusive_2033_, v_pos_2031_);
                v___x_2044_ = leanh::lean_unsigned_to_nat(0);
                v___x_2045_ = lean_nat_sub(v_endExclusive_2034_, v___x_2035_);
                v___x_2046_ = lean_nat_dec_eq(v___x_2044_, v___x_2045_);
                leanh::lean_dec(v___x_2045_);
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
                    leanh::lean_dec(v___x_2035_);
                    return v_pos_2031_;
                }
            }
            1 => {
                v___x_2037_ = lean_string_utf8_next_fast(v_str_2032_, v___x_2035_);
                v___x_2038_ = lean_nat_sub(v___x_2037_, v___x_2035_);
                leanh::lean_dec(v___x_2035_);
                v___x_2039_ = lean_nat_add(v_pos_2031_, v___x_2038_);
                leanh::lean_dec(v___x_2038_);
                v___x_2040_ = lean_nat_dec_lt(v_pos_2031_, v___x_2039_);
                if v___x_2040_ == 0 {
                    leanh::lean_dec(v___x_2039_);
                    return v_pos_2031_;
                } else {
                    leanh::lean_dec(v_pos_2031_);
                    v_pos_2031_ = v___x_2039_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v___y_2043_ == 0 {
                    leanh::lean_dec(v___x_2035_);
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
    mut v_s_2058_: *mut leanh::LeanObject,
    mut v_pos_2059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2060_ =
        l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v_s_2058_, v_pos_2059_);
    leanh::lean_dec_ref(v_s_2058_);
    return v_res_2060_;
}
pub unsafe fn l_String_trimLeft(
    mut v_s_2061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2062_ = leanh::lean_unsigned_to_nat(0);
    v___x_2063_ = lean_string_utf8_byte_size(v_s_2061_);
    leanh::lean_inc_ref(v_s_2061_);
    v___x_2064_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2064_, 0, v_s_2061_);
    leanh::lean_ctor_set(v___x_2064_, 1, v___x_2062_);
    leanh::lean_ctor_set(v___x_2064_, 2, v___x_2063_);
    v___x_2065_ =
        l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(v___x_2064_, v___x_2062_);
    leanh::lean_dec_ref_known(v___x_2064_, 3);
    v___x_2066_ = lean_string_utf8_extract(v_s_2061_, v___x_2065_, v___x_2063_);
    leanh::lean_dec(v___x_2065_);
    leanh::lean_dec_ref(v_s_2061_);
    return v___x_2066_;
}
pub unsafe fn l_String_Slice_trimLeft(
    mut v_s_2067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_unused_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2068_ = leanh::lean_ctor_get(v_s_2067_, 0);
                leanh::lean_inc_ref(v_str_2068_);
                v_startInclusive_2069_ = leanh::lean_ctor_get(v_s_2067_, 1);
                leanh::lean_inc(v_startInclusive_2069_);
                v_endExclusive_2070_ = leanh::lean_ctor_get(v_s_2067_, 2);
                leanh::lean_inc(v_endExclusive_2070_);
                v___x_2071_ = leanh::lean_unsigned_to_nat(0);
                v___x_2072_ = l_String_Slice_Pos_skipWhile___at___00String_trimLeft_spec__0(
                    v_s_2067_,
                    v___x_2071_,
                );
                v_isSharedCheck_2080_ = (!leanh::lean_is_exclusive(v_s_2067_)) as u8;
                if v_isSharedCheck_2080_ == 0 {
                    v_unused_2081_ = leanh::lean_ctor_get(v_s_2067_, 2);
                    leanh::lean_dec(v_unused_2081_);
                    v_unused_2082_ = leanh::lean_ctor_get(v_s_2067_, 1);
                    leanh::lean_dec(v_unused_2082_);
                    v_unused_2083_ = leanh::lean_ctor_get(v_s_2067_, 0);
                    leanh::lean_dec(v_unused_2083_);
                    v___x_2074_ = v_s_2067_;
                    v_isShared_2075_ = v_isSharedCheck_2080_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_s_2067_);
                    v___x_2074_ = leanh::lean_box(0);
                    v_isShared_2075_ = v_isSharedCheck_2080_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2076_ = lean_nat_add(v_startInclusive_2069_, v___x_2072_);
                leanh::lean_dec(v___x_2072_);
                leanh::lean_dec(v_startInclusive_2069_);
                if v_isShared_2075_ == 0 {
                    leanh::lean_ctor_set(v___x_2074_, 1, v___x_2076_);
                    v___x_2078_ = v___x_2074_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2079_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_str_2068_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 1, v___x_2076_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_endExclusive_2070_);
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
pub unsafe fn l_String_trimAscii(
    mut v_s_2084_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2085_ = leanh::lean_unsigned_to_nat(0);
    v___x_2086_ = lean_string_utf8_byte_size(v_s_2084_);
    v___x_2087_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2087_, 0, v_s_2084_);
    leanh::lean_ctor_set(v___x_2087_, 1, v___x_2085_);
    leanh::lean_ctor_set(v___x_2087_, 2, v___x_2086_);
    v___x_2088_ = l_String_Slice_trimAscii(v___x_2087_);
    return v___x_2088_;
}
pub unsafe fn l_String_trim(
    mut v_s_2089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2090_ = leanh::lean_unsigned_to_nat(0);
    v___x_2091_ = lean_string_utf8_byte_size(v_s_2089_);
    v___x_2092_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2092_, 0, v_s_2089_);
    leanh::lean_ctor_set(v___x_2092_, 1, v___x_2090_);
    leanh::lean_ctor_set(v___x_2092_, 2, v___x_2091_);
    v___x_2093_ = l_String_Slice_trimAscii(v___x_2092_);
    v_str_2094_ = leanh::lean_ctor_get(v___x_2093_, 0);
    leanh::lean_inc_ref(v_str_2094_);
    v_startInclusive_2095_ = leanh::lean_ctor_get(v___x_2093_, 1);
    leanh::lean_inc(v_startInclusive_2095_);
    v_endExclusive_2096_ = leanh::lean_ctor_get(v___x_2093_, 2);
    leanh::lean_inc(v_endExclusive_2096_);
    leanh::lean_dec_ref(v___x_2093_);
    v___x_2097_ =
        lean_string_utf8_extract(v_str_2094_, v_startInclusive_2095_, v_endExclusive_2096_);
    leanh::lean_dec(v_endExclusive_2096_);
    leanh::lean_dec(v_startInclusive_2095_);
    leanh::lean_dec_ref(v_str_2094_);
    return v___x_2097_;
}
pub unsafe fn l_String_Slice_trim(
    mut v_s_2098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2099_ = l_String_Slice_trimAscii(v_s_2098_);
    return v___x_2099_;
}
pub unsafe fn lean_string_trim(
    mut v_s_2100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2101_ = leanh::lean_unsigned_to_nat(0);
    v___x_2102_ = lean_string_utf8_byte_size(v_s_2100_);
    v___x_2103_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2103_, 0, v_s_2100_);
    leanh::lean_ctor_set(v___x_2103_, 1, v___x_2101_);
    leanh::lean_ctor_set(v___x_2103_, 2, v___x_2102_);
    v___x_2104_ = l_String_Slice_trimAscii(v___x_2103_);
    v_str_2105_ = leanh::lean_ctor_get(v___x_2104_, 0);
    leanh::lean_inc_ref(v_str_2105_);
    v_startInclusive_2106_ = leanh::lean_ctor_get(v___x_2104_, 1);
    leanh::lean_inc(v_startInclusive_2106_);
    v_endExclusive_2107_ = leanh::lean_ctor_get(v___x_2104_, 2);
    leanh::lean_inc(v_endExclusive_2107_);
    leanh::lean_dec_ref(v___x_2104_);
    v___x_2108_ =
        lean_string_utf8_extract(v_str_2105_, v_startInclusive_2106_, v_endExclusive_2107_);
    leanh::lean_dec(v_endExclusive_2107_);
    leanh::lean_dec(v_startInclusive_2106_);
    leanh::lean_dec_ref(v_str_2105_);
    return v___x_2108_;
}
pub unsafe fn l_String_Pos_Raw_nextWhile(
    mut v_s_2109_: *mut leanh::LeanObject,
    mut v_p_2110_: *mut leanh::LeanObject,
    mut v_i_2111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2112_ = lean_string_utf8_byte_size(v_s_2109_);
    v___x_2113_ = l_Substring_Raw_takeWhileAux(v_s_2109_, v___x_2112_, v_p_2110_, v_i_2111_);
    return v___x_2113_;
}
pub unsafe fn l_String_Pos_Raw_nextWhile___boxed(
    mut v_s_2114_: *mut leanh::LeanObject,
    mut v_p_2115_: *mut leanh::LeanObject,
    mut v_i_2116_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2117_ = l_String_Pos_Raw_nextWhile(v_s_2114_, v_p_2115_, v_i_2116_);
    leanh::lean_dec_ref(v_s_2114_);
    return v_res_2117_;
}
pub unsafe fn l_String_nextWhile(
    mut v_s_2118_: *mut leanh::LeanObject,
    mut v_p_2119_: *mut leanh::LeanObject,
    mut v_i_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = lean_string_utf8_byte_size(v_s_2118_);
    v___x_2122_ = l_Substring_Raw_takeWhileAux(v_s_2118_, v___x_2121_, v_p_2119_, v_i_2120_);
    return v___x_2122_;
}
pub unsafe fn l_String_nextWhile___boxed(
    mut v_s_2123_: *mut leanh::LeanObject,
    mut v_p_2124_: *mut leanh::LeanObject,
    mut v_i_2125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2126_ = l_String_nextWhile(v_s_2123_, v_p_2124_, v_i_2125_);
    leanh::lean_dec_ref(v_s_2123_);
    return v_res_2126_;
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(
    mut v_p_2127_: *mut leanh::LeanObject,
    mut v_s_2128_: *mut leanh::LeanObject,
    mut v_stopPos_2129_: *mut leanh::LeanObject,
    mut v_i_2130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: u32 = 0;
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2131_ = lean_nat_dec_lt(v_i_2130_, v_stopPos_2129_);
                if v___x_2131_ == 0 {
                    leanh::lean_dec_ref(v_p_2127_);
                    return v_i_2130_;
                } else {
                    v___x_2132_ = lean_string_utf8_get(v_s_2128_, v_i_2130_);
                    v___x_2133_ = leanh::lean_box_uint32(v___x_2132_);
                    leanh::lean_inc_ref(v_p_2127_);
                    v___x_2134_ = leanh::lean_apply_1(v_p_2127_, v___x_2133_);
                    v___x_2135_ = (leanh::lean_unbox(v___x_2134_) as u8);
                    if v___x_2135_ == 0 {
                        leanh::lean_dec_ref(v_p_2127_);
                        return v_i_2130_;
                    } else {
                        v___x_2136_ = lean_string_utf8_next(v_s_2128_, v_i_2130_);
                        leanh::lean_dec(v_i_2130_);
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
    mut v_p_2138_: *mut leanh::LeanObject,
    mut v_s_2139_: *mut leanh::LeanObject,
    mut v_stopPos_2140_: *mut leanh::LeanObject,
    mut v_i_2141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2142_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(
        v_p_2138_,
        v_s_2139_,
        v_stopPos_2140_,
        v_i_2141_,
    );
    leanh::lean_dec(v_stopPos_2140_);
    leanh::lean_dec_ref(v_s_2139_);
    return v_res_2142_;
}
pub unsafe fn lean_string_nextwhile(
    mut v_s_2143_: *mut leanh::LeanObject,
    mut v_p_2144_: *mut leanh::LeanObject,
    mut v_i_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2146_ = lean_string_utf8_byte_size(v_s_2143_);
    v___x_2147_ = l_Substring_Raw_takeWhileAux___at___00String_Internal_nextWhileImpl_spec__0(
        v_p_2144_,
        v_s_2143_,
        v___x_2146_,
        v_i_2145_,
    );
    leanh::lean_dec_ref(v_s_2143_);
    return v___x_2147_;
}
pub unsafe fn l_String_Pos_Raw_nextUntil___lam__0(
    mut v_p_2148_: *mut leanh::LeanObject,
    mut v_c_2149_: u32,
) -> u8 {
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: u8 = 0;
    v___x_2150_ = leanh::lean_box_uint32(v_c_2149_);
    v___x_2151_ = leanh::lean_apply_1(v_p_2148_, v___x_2150_);
    v___x_2152_ = (leanh::lean_unbox(v___x_2151_) as u8);
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
    mut v_p_2155_: *mut leanh::LeanObject,
    mut v_c_2156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_2157_: u32 = 0;
    let mut v_res_2158_: u8 = 0;
    let mut v_r_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_2157_ = leanh::lean_unbox_uint32(v_c_2156_);
    leanh::lean_dec(v_c_2156_);
    v_res_2158_ = l_String_Pos_Raw_nextUntil___lam__0(v_p_2155_, v_c_boxed_2157_);
    v_r_2159_ = leanh::lean_box((v_res_2158_) as usize);
    return v_r_2159_;
}
pub unsafe fn l_String_Pos_Raw_nextUntil(
    mut v_s_2160_: *mut leanh::LeanObject,
    mut v_p_2161_: *mut leanh::LeanObject,
    mut v_i_2162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2163_ = leanh::lean_alloc_closure(
        l_String_Pos_Raw_nextUntil___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2163_, 0, v_p_2161_);
    v___x_2164_ = lean_string_utf8_byte_size(v_s_2160_);
    v___x_2165_ = l_Substring_Raw_takeWhileAux(v_s_2160_, v___x_2164_, v___f_2163_, v_i_2162_);
    return v___x_2165_;
}
pub unsafe fn l_String_Pos_Raw_nextUntil___boxed(
    mut v_s_2166_: *mut leanh::LeanObject,
    mut v_p_2167_: *mut leanh::LeanObject,
    mut v_i_2168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2169_ = l_String_Pos_Raw_nextUntil(v_s_2166_, v_p_2167_, v_i_2168_);
    leanh::lean_dec_ref(v_s_2166_);
    return v_res_2169_;
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(
    mut v_p_2170_: *mut leanh::LeanObject,
    mut v_s_2171_: *mut leanh::LeanObject,
    mut v_stopPos_2172_: *mut leanh::LeanObject,
    mut v_i_2173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2174_: u8 = 0;
    let mut v___x_2175_: u32 = 0;
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: u8 = 0;
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2174_ = lean_nat_dec_lt(v_i_2173_, v_stopPos_2172_);
                if v___x_2174_ == 0 {
                    leanh::lean_dec_ref(v_p_2170_);
                    return v_i_2173_;
                } else {
                    v___x_2175_ = lean_string_utf8_get(v_s_2171_, v_i_2173_);
                    v___x_2176_ = leanh::lean_box_uint32(v___x_2175_);
                    leanh::lean_inc_ref(v_p_2170_);
                    v___x_2177_ = leanh::lean_apply_1(v_p_2170_, v___x_2176_);
                    v___x_2178_ = (leanh::lean_unbox(v___x_2177_) as u8);
                    if v___x_2178_ == 0 {
                        v___x_2179_ = lean_string_utf8_next(v_s_2171_, v_i_2173_);
                        leanh::lean_dec(v_i_2173_);
                        v_i_2173_ = v___x_2179_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_p_2170_);
                        return v_i_2173_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0___boxed(
    mut v_p_2181_: *mut leanh::LeanObject,
    mut v_s_2182_: *mut leanh::LeanObject,
    mut v_stopPos_2183_: *mut leanh::LeanObject,
    mut v_i_2184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2185_ = l_Substring_Raw_takeWhileAux___at___00String_nextUntil_spec__0(
        v_p_2181_,
        v_s_2182_,
        v_stopPos_2183_,
        v_i_2184_,
    );
    leanh::lean_dec(v_stopPos_2183_);
    leanh::lean_dec_ref(v_s_2182_);
    return v_res_2185_;
}
pub unsafe fn l_String_nextUntil(
    mut v_s_2186_: *mut leanh::LeanObject,
    mut v_p_2187_: *mut leanh::LeanObject,
    mut v_i_2188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_s_2191_: *mut leanh::LeanObject,
    mut v_p_2192_: *mut leanh::LeanObject,
    mut v_i_2193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2194_ = l_String_nextUntil(v_s_2191_, v_p_2192_, v_i_2193_);
    leanh::lean_dec_ref(v_s_2191_);
    return v_res_2194_;
}
pub unsafe fn l_String_dropPrefix_x3f___redArg(
    mut v_s_2195_: *mut leanh::LeanObject,
    mut v_inst_2196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipPrefix_x3f_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2200_: u8 = 0;
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2210_: u8 = 0;
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2215_: u8 = 0;
    let mut v_reuseFailAlloc_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_unused_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipPrefix_x3f_2197_ = leanh::lean_ctor_get(v_inst_2196_, 0);
                v_isSharedCheck_2217_ = (!leanh::lean_is_exclusive(v_inst_2196_)) as u8;
                if v_isSharedCheck_2217_ == 0 {
                    v_unused_2218_ = leanh::lean_ctor_get(v_inst_2196_, 2);
                    leanh::lean_dec(v_unused_2218_);
                    v_unused_2219_ = leanh::lean_ctor_get(v_inst_2196_, 1);
                    leanh::lean_dec(v_unused_2219_);
                    v___x_2199_ = v_inst_2196_;
                    v_isShared_2200_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipPrefix_x3f_2197_);
                    leanh::lean_dec(v_inst_2196_);
                    v___x_2199_ = leanh::lean_box(0);
                    v_isShared_2200_ = v_isSharedCheck_2217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2201_ = lean_string_utf8_byte_size(v_s_2195_);
                v___x_2202_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_s_2195_);
                if v_isShared_2200_ == 0 {
                    leanh::lean_ctor_set(v___x_2199_, 2, v___x_2201_);
                    leanh::lean_ctor_set(v___x_2199_, 1, v___x_2202_);
                    leanh::lean_ctor_set(v___x_2199_, 0, v_s_2195_);
                    v___x_2204_ = v___x_2199_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_s_2195_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 1, v___x_2202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 2, v___x_2201_);
                    v___x_2204_ = v_reuseFailAlloc_2216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2205_ = leanh::lean_apply_1(v_skipPrefix_x3f_2197_, v___x_2204_);
                if leanh::lean_obj_tag(v___x_2205_) == 0 {
                    leanh::lean_dec_ref(v_s_2195_);
                    v___x_2206_ = leanh::lean_box(0);
                    return v___x_2206_;
                } else {
                    v_val_2207_ = leanh::lean_ctor_get(v___x_2205_, 0);
                    v_isSharedCheck_2215_ = (!leanh::lean_is_exclusive(v___x_2205_)) as u8;
                    if v_isSharedCheck_2215_ == 0 {
                        v___x_2209_ = v___x_2205_;
                        v_isShared_2210_ = v_isSharedCheck_2215_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2207_);
                        leanh::lean_dec(v___x_2205_);
                        v___x_2209_ = leanh::lean_box(0);
                        v_isShared_2210_ = v_isSharedCheck_2215_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2211_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2211_, 0, v_s_2195_);
                leanh::lean_ctor_set(v___x_2211_, 1, v_val_2207_);
                leanh::lean_ctor_set(v___x_2211_, 2, v___x_2201_);
                if v_isShared_2210_ == 0 {
                    leanh::lean_ctor_set(v___x_2209_, 0, v___x_2211_);
                    v___x_2213_ = v___x_2209_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2214_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
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
    mut v_00_u03c1_2220_: *mut leanh::LeanObject,
    mut v_s_2221_: *mut leanh::LeanObject,
    mut v_pat_2222_: *mut leanh::LeanObject,
    mut v_inst_2223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2224_ = l_String_dropPrefix_x3f___redArg(v_s_2221_, v_inst_2223_);
    return v___x_2224_;
}
pub unsafe fn l_String_dropPrefix_x3f___boxed(
    mut v_00_u03c1_2225_: *mut leanh::LeanObject,
    mut v_s_2226_: *mut leanh::LeanObject,
    mut v_pat_2227_: *mut leanh::LeanObject,
    mut v_inst_2228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2229_ = l_String_dropPrefix_x3f(v_00_u03c1_2225_, v_s_2226_, v_pat_2227_, v_inst_2228_);
    leanh::lean_dec(v_pat_2227_);
    return v_res_2229_;
}
pub unsafe fn l_String_dropSuffix_x3f___redArg(
    mut v_s_2230_: *mut leanh::LeanObject,
    mut v_inst_2231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipSuffix_x3f_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2235_: u8 = 0;
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2245_: u8 = 0;
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut v_reuseFailAlloc_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2252_: u8 = 0;
    let mut v_unused_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_skipSuffix_x3f_2232_ = leanh::lean_ctor_get(v_inst_2231_, 0);
                v_isSharedCheck_2252_ = (!leanh::lean_is_exclusive(v_inst_2231_)) as u8;
                if v_isSharedCheck_2252_ == 0 {
                    v_unused_2253_ = leanh::lean_ctor_get(v_inst_2231_, 2);
                    leanh::lean_dec(v_unused_2253_);
                    v_unused_2254_ = leanh::lean_ctor_get(v_inst_2231_, 1);
                    leanh::lean_dec(v_unused_2254_);
                    v___x_2234_ = v_inst_2231_;
                    v_isShared_2235_ = v_isSharedCheck_2252_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_skipSuffix_x3f_2232_);
                    leanh::lean_dec(v_inst_2231_);
                    v___x_2234_ = leanh::lean_box(0);
                    v_isShared_2235_ = v_isSharedCheck_2252_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2236_ = lean_string_utf8_byte_size(v_s_2230_);
                v___x_2237_ = leanh::lean_unsigned_to_nat(0);
                leanh::lean_inc_ref(v_s_2230_);
                if v_isShared_2235_ == 0 {
                    leanh::lean_ctor_set(v___x_2234_, 2, v___x_2236_);
                    leanh::lean_ctor_set(v___x_2234_, 1, v___x_2237_);
                    leanh::lean_ctor_set(v___x_2234_, 0, v_s_2230_);
                    v___x_2239_ = v___x_2234_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2251_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 0, v_s_2230_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 1, v___x_2237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2251_, 2, v___x_2236_);
                    v___x_2239_ = v_reuseFailAlloc_2251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2240_ = leanh::lean_apply_1(v_skipSuffix_x3f_2232_, v___x_2239_);
                if leanh::lean_obj_tag(v___x_2240_) == 0 {
                    leanh::lean_dec_ref(v_s_2230_);
                    v___x_2241_ = leanh::lean_box(0);
                    return v___x_2241_;
                } else {
                    v_val_2242_ = leanh::lean_ctor_get(v___x_2240_, 0);
                    v_isSharedCheck_2250_ = (!leanh::lean_is_exclusive(v___x_2240_)) as u8;
                    if v_isSharedCheck_2250_ == 0 {
                        v___x_2244_ = v___x_2240_;
                        v_isShared_2245_ = v_isSharedCheck_2250_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2242_);
                        leanh::lean_dec(v___x_2240_);
                        v___x_2244_ = leanh::lean_box(0);
                        v_isShared_2245_ = v_isSharedCheck_2250_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2246_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_2246_, 0, v_s_2230_);
                leanh::lean_ctor_set(v___x_2246_, 1, v___x_2237_);
                leanh::lean_ctor_set(v___x_2246_, 2, v_val_2242_);
                if v_isShared_2245_ == 0 {
                    leanh::lean_ctor_set(v___x_2244_, 0, v___x_2246_);
                    v___x_2248_ = v___x_2244_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2249_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2249_, 0, v___x_2246_);
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
    mut v_00_u03c1_2255_: *mut leanh::LeanObject,
    mut v_s_2256_: *mut leanh::LeanObject,
    mut v_pat_2257_: *mut leanh::LeanObject,
    mut v_inst_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2259_ = l_String_dropSuffix_x3f___redArg(v_s_2256_, v_inst_2258_);
    return v___x_2259_;
}
pub unsafe fn l_String_dropSuffix_x3f___boxed(
    mut v_00_u03c1_2260_: *mut leanh::LeanObject,
    mut v_s_2261_: *mut leanh::LeanObject,
    mut v_pat_2262_: *mut leanh::LeanObject,
    mut v_inst_2263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_String_dropSuffix_x3f(v_00_u03c1_2260_, v_s_2261_, v_pat_2262_, v_inst_2263_);
    leanh::lean_dec(v_pat_2262_);
    return v_res_2264_;
}
pub unsafe fn l_String_dropPrefix___redArg(
    mut v_s_2265_: *mut leanh::LeanObject,
    mut v_inst_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2267_ = leanh::lean_unsigned_to_nat(0);
    v___x_2268_ = lean_string_utf8_byte_size(v_s_2265_);
    v___x_2269_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2269_, 0, v_s_2265_);
    leanh::lean_ctor_set(v___x_2269_, 1, v___x_2267_);
    leanh::lean_ctor_set(v___x_2269_, 2, v___x_2268_);
    v___x_2270_ = l_String_Slice_dropPrefix___redArg(v___x_2269_, v_inst_2266_);
    return v___x_2270_;
}
pub unsafe fn l_String_dropPrefix(
    mut v_00_u03c1_2271_: *mut leanh::LeanObject,
    mut v_s_2272_: *mut leanh::LeanObject,
    mut v_pat_2273_: *mut leanh::LeanObject,
    mut v_inst_2274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_String_dropPrefix___redArg(v_s_2272_, v_inst_2274_);
    return v___x_2275_;
}
pub unsafe fn l_String_dropPrefix___boxed(
    mut v_00_u03c1_2276_: *mut leanh::LeanObject,
    mut v_s_2277_: *mut leanh::LeanObject,
    mut v_pat_2278_: *mut leanh::LeanObject,
    mut v_inst_2279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_String_dropPrefix(v_00_u03c1_2276_, v_s_2277_, v_pat_2278_, v_inst_2279_);
    leanh::lean_dec(v_pat_2278_);
    return v_res_2280_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(
    mut v_pre_2281_: *mut leanh::LeanObject,
    mut v_s_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: u8 = 0;
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2294_: u8 = 0;
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2283_ = leanh::lean_ctor_get(v_s_2282_, 0);
                v_startInclusive_2284_ = leanh::lean_ctor_get(v_s_2282_, 1);
                v_endExclusive_2285_ = leanh::lean_ctor_get(v_s_2282_, 2);
                v___x_2286_ = lean_string_utf8_byte_size(v_pre_2281_);
                v___x_2287_ = lean_nat_sub(v_endExclusive_2285_, v_startInclusive_2284_);
                v___x_2288_ = lean_nat_dec_le(v___x_2286_, v___x_2287_);
                leanh::lean_dec(v___x_2287_);
                if v___x_2288_ == 0 {
                    return v_s_2282_;
                } else {
                    v___x_2289_ = leanh::lean_unsigned_to_nat(0);
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
                        leanh::lean_inc(v_endExclusive_2285_);
                        leanh::lean_inc(v_startInclusive_2284_);
                        leanh::lean_inc_ref(v_str_2283_);
                        v___x_2291_ = l_String_Slice_pos_x21(v_s_2282_, v___x_2286_);
                        v_isSharedCheck_2299_ = (!leanh::lean_is_exclusive(v_s_2282_)) as u8;
                        if v_isSharedCheck_2299_ == 0 {
                            v_unused_2300_ = leanh::lean_ctor_get(v_s_2282_, 2);
                            leanh::lean_dec(v_unused_2300_);
                            v_unused_2301_ = leanh::lean_ctor_get(v_s_2282_, 1);
                            leanh::lean_dec(v_unused_2301_);
                            v_unused_2302_ = leanh::lean_ctor_get(v_s_2282_, 0);
                            leanh::lean_dec(v_unused_2302_);
                            v___x_2293_ = v_s_2282_;
                            v_isShared_2294_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_s_2282_);
                            v___x_2293_ = leanh::lean_box(0);
                            v_isShared_2294_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2295_ = lean_nat_add(v_startInclusive_2284_, v___x_2291_);
                leanh::lean_dec(v___x_2291_);
                leanh::lean_dec(v_startInclusive_2284_);
                if v_isShared_2294_ == 0 {
                    leanh::lean_ctor_set(v___x_2293_, 1, v___x_2295_);
                    v___x_2297_ = v___x_2293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2298_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_str_2283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 1, v___x_2295_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 2, v_endExclusive_2285_);
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
    mut v_pre_2303_: *mut leanh::LeanObject,
    mut v_s_2304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2305_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_2303_, v_s_2304_);
    leanh::lean_dec_ref(v_pre_2303_);
    return v_res_2305_;
}
pub unsafe fn l_String_dropPrefix___at___00String_stripPrefix_spec__0(
    mut v_pre_2306_: *mut leanh::LeanObject,
    mut v_s_2307_: *mut leanh::LeanObject,
    mut v_pat_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2309_ = leanh::lean_unsigned_to_nat(0);
    v___x_2310_ = lean_string_utf8_byte_size(v_s_2307_);
    v___x_2311_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2311_, 0, v_s_2307_);
    leanh::lean_ctor_set(v___x_2311_, 1, v___x_2309_);
    leanh::lean_ctor_set(v___x_2311_, 2, v___x_2310_);
    v___x_2312_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_2306_, v___x_2311_);
    return v___x_2312_;
}
pub unsafe fn l_String_dropPrefix___at___00String_stripPrefix_spec__0___boxed(
    mut v_pre_2313_: *mut leanh::LeanObject,
    mut v_s_2314_: *mut leanh::LeanObject,
    mut v_pat_2315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2316_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(
        v_pre_2313_,
        v_s_2314_,
        v_pat_2315_,
    );
    leanh::lean_dec_ref(v_pat_2315_);
    leanh::lean_dec_ref(v_pre_2313_);
    return v_res_2316_;
}
pub unsafe fn l_String_stripPrefix(
    mut v_s_2317_: *mut leanh::LeanObject,
    mut v_pre_2318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2319_ = l_String_dropPrefix___at___00String_stripPrefix_spec__0(
        v_pre_2318_,
        v_s_2317_,
        v_pre_2318_,
    );
    v___x_2320_ = l_String_Slice_toString(v___x_2319_);
    leanh::lean_dec_ref(v___x_2319_);
    return v___x_2320_;
}
pub unsafe fn l_String_stripPrefix___boxed(
    mut v_s_2321_: *mut leanh::LeanObject,
    mut v_pre_2322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2323_ = l_String_stripPrefix(v_s_2321_, v_pre_2322_);
    leanh::lean_dec_ref(v_pre_2322_);
    return v_res_2323_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(
    mut v_pat_2324_: *mut leanh::LeanObject,
    mut v_pre_2325_: *mut leanh::LeanObject,
    mut v_s_2326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___redArg(v_pre_2325_, v_s_2326_);
    return v___x_2327_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0___boxed(
    mut v_pat_2328_: *mut leanh::LeanObject,
    mut v_pre_2329_: *mut leanh::LeanObject,
    mut v_s_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00String_stripPrefix_spec__0_spec__0(v_pat_2328_, v_pre_2329_, v_s_2330_);
    leanh::lean_dec_ref(v_pre_2329_);
    leanh::lean_dec_ref(v_pat_2328_);
    return v_res_2331_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(
    mut v_pre_2332_: *mut leanh::LeanObject,
    mut v_s_2333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: u8 = 0;
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2347_: u8 = 0;
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2352_: u8 = 0;
    let mut v_unused_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2334_ = leanh::lean_ctor_get(v_pre_2332_, 0);
                v_startInclusive_2335_ = leanh::lean_ctor_get(v_pre_2332_, 1);
                v_endExclusive_2336_ = leanh::lean_ctor_get(v_pre_2332_, 2);
                v_str_2337_ = leanh::lean_ctor_get(v_s_2333_, 0);
                v_startInclusive_2338_ = leanh::lean_ctor_get(v_s_2333_, 1);
                v_endExclusive_2339_ = leanh::lean_ctor_get(v_s_2333_, 2);
                v___x_2340_ = lean_nat_sub(v_endExclusive_2336_, v_startInclusive_2335_);
                v___x_2341_ = lean_nat_sub(v_endExclusive_2339_, v_startInclusive_2338_);
                v___x_2342_ = lean_nat_dec_le(v___x_2340_, v___x_2341_);
                leanh::lean_dec(v___x_2341_);
                if v___x_2342_ == 0 {
                    leanh::lean_dec(v___x_2340_);
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
                        leanh::lean_dec(v___x_2340_);
                        return v_s_2333_;
                    } else {
                        leanh::lean_inc(v_endExclusive_2339_);
                        leanh::lean_inc(v_startInclusive_2338_);
                        leanh::lean_inc_ref(v_str_2337_);
                        v___x_2344_ = l_String_Slice_pos_x21(v_s_2333_, v___x_2340_);
                        leanh::lean_dec(v___x_2340_);
                        v_isSharedCheck_2352_ = (!leanh::lean_is_exclusive(v_s_2333_)) as u8;
                        if v_isSharedCheck_2352_ == 0 {
                            v_unused_2353_ = leanh::lean_ctor_get(v_s_2333_, 2);
                            leanh::lean_dec(v_unused_2353_);
                            v_unused_2354_ = leanh::lean_ctor_get(v_s_2333_, 1);
                            leanh::lean_dec(v_unused_2354_);
                            v_unused_2355_ = leanh::lean_ctor_get(v_s_2333_, 0);
                            leanh::lean_dec(v_unused_2355_);
                            v___x_2346_ = v_s_2333_;
                            v_isShared_2347_ = v_isSharedCheck_2352_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_s_2333_);
                            v___x_2346_ = leanh::lean_box(0);
                            v_isShared_2347_ = v_isSharedCheck_2352_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2348_ = lean_nat_add(v_startInclusive_2338_, v___x_2344_);
                leanh::lean_dec(v___x_2344_);
                leanh::lean_dec(v_startInclusive_2338_);
                if v_isShared_2347_ == 0 {
                    leanh::lean_ctor_set(v___x_2346_, 1, v___x_2348_);
                    v___x_2350_ = v___x_2346_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2351_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_str_2337_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___x_2348_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2351_, 2, v_endExclusive_2339_);
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
    mut v_pre_2356_: *mut leanh::LeanObject,
    mut v_s_2357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2358_ =
        l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_2356_, v_s_2357_);
    leanh::lean_dec_ref(v_pre_2356_);
    return v_res_2358_;
}
pub unsafe fn l_String_Slice_stripPrefix(
    mut v_s_2359_: *mut leanh::LeanObject,
    mut v_pre_2360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2361_ =
        l_String_Slice_dropPrefix___at___00String_Slice_stripPrefix_spec__0(v_pre_2360_, v_s_2359_);
    return v___x_2361_;
}
pub unsafe fn l_String_Slice_stripPrefix___boxed(
    mut v_s_2362_: *mut leanh::LeanObject,
    mut v_pre_2363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2364_ = l_String_Slice_stripPrefix(v_s_2362_, v_pre_2363_);
    leanh::lean_dec_ref(v_pre_2363_);
    return v_res_2364_;
}
pub unsafe fn l_String_dropSuffix___redArg(
    mut v_s_2365_: *mut leanh::LeanObject,
    mut v_inst_2366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2367_ = leanh::lean_unsigned_to_nat(0);
    v___x_2368_ = lean_string_utf8_byte_size(v_s_2365_);
    v___x_2369_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2369_, 0, v_s_2365_);
    leanh::lean_ctor_set(v___x_2369_, 1, v___x_2367_);
    leanh::lean_ctor_set(v___x_2369_, 2, v___x_2368_);
    v___x_2370_ = l_String_Slice_dropSuffix___redArg(v___x_2369_, v_inst_2366_);
    return v___x_2370_;
}
pub unsafe fn l_String_dropSuffix(
    mut v_00_u03c1_2371_: *mut leanh::LeanObject,
    mut v_s_2372_: *mut leanh::LeanObject,
    mut v_pat_2373_: *mut leanh::LeanObject,
    mut v_inst_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2375_ = l_String_dropSuffix___redArg(v_s_2372_, v_inst_2374_);
    return v___x_2375_;
}
pub unsafe fn l_String_dropSuffix___boxed(
    mut v_00_u03c1_2376_: *mut leanh::LeanObject,
    mut v_s_2377_: *mut leanh::LeanObject,
    mut v_pat_2378_: *mut leanh::LeanObject,
    mut v_inst_2379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2380_ = l_String_dropSuffix(v_00_u03c1_2376_, v_s_2377_, v_pat_2378_, v_inst_2379_);
    leanh::lean_dec(v_pat_2378_);
    return v_res_2380_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(
    mut v_suff_2381_: *mut leanh::LeanObject,
    mut v_s_2382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: u8 = 0;
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v_unused_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2383_ = leanh::lean_ctor_get(v_s_2382_, 0);
                v_startInclusive_2384_ = leanh::lean_ctor_get(v_s_2382_, 1);
                v_endExclusive_2385_ = leanh::lean_ctor_get(v_s_2382_, 2);
                v___x_2386_ = lean_string_utf8_byte_size(v_suff_2381_);
                v___x_2387_ = lean_nat_sub(v_endExclusive_2385_, v_startInclusive_2384_);
                v___x_2388_ = lean_nat_dec_le(v___x_2386_, v___x_2387_);
                if v___x_2388_ == 0 {
                    leanh::lean_dec(v___x_2387_);
                    return v_s_2382_;
                } else {
                    v___x_2389_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2390_ = lean_nat_sub(v___x_2387_, v___x_2386_);
                    leanh::lean_dec(v___x_2387_);
                    v___x_2391_ = lean_nat_add(v_startInclusive_2384_, v___x_2390_);
                    v___x_2392_ = lean_string_memcmp(
                        v_str_2383_,
                        v_suff_2381_,
                        v___x_2391_,
                        v___x_2389_,
                        v___x_2386_,
                    );
                    leanh::lean_dec(v___x_2391_);
                    if v___x_2392_ == 0 {
                        leanh::lean_dec(v___x_2390_);
                        return v_s_2382_;
                    } else {
                        leanh::lean_inc(v_startInclusive_2384_);
                        leanh::lean_inc_ref(v_str_2383_);
                        v___x_2393_ = l_String_Slice_pos_x21(v_s_2382_, v___x_2390_);
                        leanh::lean_dec(v___x_2390_);
                        v_isSharedCheck_2401_ = (!leanh::lean_is_exclusive(v_s_2382_)) as u8;
                        if v_isSharedCheck_2401_ == 0 {
                            v_unused_2402_ = leanh::lean_ctor_get(v_s_2382_, 2);
                            leanh::lean_dec(v_unused_2402_);
                            v_unused_2403_ = leanh::lean_ctor_get(v_s_2382_, 1);
                            leanh::lean_dec(v_unused_2403_);
                            v_unused_2404_ = leanh::lean_ctor_get(v_s_2382_, 0);
                            leanh::lean_dec(v_unused_2404_);
                            v___x_2395_ = v_s_2382_;
                            v_isShared_2396_ = v_isSharedCheck_2401_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_s_2382_);
                            v___x_2395_ = leanh::lean_box(0);
                            v_isShared_2396_ = v_isSharedCheck_2401_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2397_ = lean_nat_add(v_startInclusive_2384_, v___x_2393_);
                leanh::lean_dec(v___x_2393_);
                if v_isShared_2396_ == 0 {
                    leanh::lean_ctor_set(v___x_2395_, 2, v___x_2397_);
                    v___x_2399_ = v___x_2395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2400_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_str_2383_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 1, v_startInclusive_2384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2400_, 2, v___x_2397_);
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
    mut v_suff_2405_: *mut leanh::LeanObject,
    mut v_s_2406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2407_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_2405_, v_s_2406_);
    leanh::lean_dec_ref(v_suff_2405_);
    return v_res_2407_;
}
pub unsafe fn l_String_dropSuffix___at___00String_stripSuffix_spec__0(
    mut v_suff_2408_: *mut leanh::LeanObject,
    mut v_s_2409_: *mut leanh::LeanObject,
    mut v_pat_2410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = leanh::lean_unsigned_to_nat(0);
    v___x_2412_ = lean_string_utf8_byte_size(v_s_2409_);
    v___x_2413_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2413_, 0, v_s_2409_);
    leanh::lean_ctor_set(v___x_2413_, 1, v___x_2411_);
    leanh::lean_ctor_set(v___x_2413_, 2, v___x_2412_);
    v___x_2414_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_2408_, v___x_2413_);
    return v___x_2414_;
}
pub unsafe fn l_String_dropSuffix___at___00String_stripSuffix_spec__0___boxed(
    mut v_suff_2415_: *mut leanh::LeanObject,
    mut v_s_2416_: *mut leanh::LeanObject,
    mut v_pat_2417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2418_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(
        v_suff_2415_,
        v_s_2416_,
        v_pat_2417_,
    );
    leanh::lean_dec_ref(v_pat_2417_);
    leanh::lean_dec_ref(v_suff_2415_);
    return v_res_2418_;
}
pub unsafe fn l_String_stripSuffix(
    mut v_s_2419_: *mut leanh::LeanObject,
    mut v_suff_2420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2421_ = l_String_dropSuffix___at___00String_stripSuffix_spec__0(
        v_suff_2420_,
        v_s_2419_,
        v_suff_2420_,
    );
    v___x_2422_ = l_String_Slice_toString(v___x_2421_);
    leanh::lean_dec_ref(v___x_2421_);
    return v___x_2422_;
}
pub unsafe fn l_String_stripSuffix___boxed(
    mut v_s_2423_: *mut leanh::LeanObject,
    mut v_suff_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2425_ = l_String_stripSuffix(v_s_2423_, v_suff_2424_);
    leanh::lean_dec_ref(v_suff_2424_);
    return v_res_2425_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(
    mut v_pat_2426_: *mut leanh::LeanObject,
    mut v_suff_2427_: *mut leanh::LeanObject,
    mut v_s_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2429_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___redArg(v_suff_2427_, v_s_2428_);
    return v___x_2429_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0___boxed(
    mut v_pat_2430_: *mut leanh::LeanObject,
    mut v_suff_2431_: *mut leanh::LeanObject,
    mut v_s_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2433_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00String_stripSuffix_spec__0_spec__0(v_pat_2430_, v_suff_2431_, v_s_2432_);
    leanh::lean_dec_ref(v_suff_2431_);
    leanh::lean_dec_ref(v_pat_2430_);
    return v_res_2433_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(
    mut v_suff_2434_: *mut leanh::LeanObject,
    mut v_s_2435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: u8 = 0;
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2451_: u8 = 0;
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut v_unused_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_2436_ = leanh::lean_ctor_get(v_suff_2434_, 0);
                v_startInclusive_2437_ = leanh::lean_ctor_get(v_suff_2434_, 1);
                v_endExclusive_2438_ = leanh::lean_ctor_get(v_suff_2434_, 2);
                v_str_2439_ = leanh::lean_ctor_get(v_s_2435_, 0);
                v_startInclusive_2440_ = leanh::lean_ctor_get(v_s_2435_, 1);
                v_endExclusive_2441_ = leanh::lean_ctor_get(v_s_2435_, 2);
                v___x_2442_ = lean_nat_sub(v_endExclusive_2438_, v_startInclusive_2437_);
                v___x_2443_ = lean_nat_sub(v_endExclusive_2441_, v_startInclusive_2440_);
                v___x_2444_ = lean_nat_dec_le(v___x_2442_, v___x_2443_);
                if v___x_2444_ == 0 {
                    leanh::lean_dec(v___x_2443_);
                    leanh::lean_dec(v___x_2442_);
                    return v_s_2435_;
                } else {
                    v___x_2445_ = lean_nat_sub(v___x_2443_, v___x_2442_);
                    leanh::lean_dec(v___x_2443_);
                    v___x_2446_ = lean_nat_add(v_startInclusive_2440_, v___x_2445_);
                    v___x_2447_ = lean_string_memcmp(
                        v_str_2439_,
                        v_str_2436_,
                        v___x_2446_,
                        v_startInclusive_2437_,
                        v___x_2442_,
                    );
                    leanh::lean_dec(v___x_2442_);
                    leanh::lean_dec(v___x_2446_);
                    if v___x_2447_ == 0 {
                        leanh::lean_dec(v___x_2445_);
                        return v_s_2435_;
                    } else {
                        leanh::lean_inc(v_startInclusive_2440_);
                        leanh::lean_inc_ref(v_str_2439_);
                        v___x_2448_ = l_String_Slice_pos_x21(v_s_2435_, v___x_2445_);
                        leanh::lean_dec(v___x_2445_);
                        v_isSharedCheck_2456_ = (!leanh::lean_is_exclusive(v_s_2435_)) as u8;
                        if v_isSharedCheck_2456_ == 0 {
                            v_unused_2457_ = leanh::lean_ctor_get(v_s_2435_, 2);
                            leanh::lean_dec(v_unused_2457_);
                            v_unused_2458_ = leanh::lean_ctor_get(v_s_2435_, 1);
                            leanh::lean_dec(v_unused_2458_);
                            v_unused_2459_ = leanh::lean_ctor_get(v_s_2435_, 0);
                            leanh::lean_dec(v_unused_2459_);
                            v___x_2450_ = v_s_2435_;
                            v_isShared_2451_ = v_isSharedCheck_2456_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_s_2435_);
                            v___x_2450_ = leanh::lean_box(0);
                            v_isShared_2451_ = v_isSharedCheck_2456_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2452_ = lean_nat_add(v_startInclusive_2440_, v___x_2448_);
                leanh::lean_dec(v___x_2448_);
                if v_isShared_2451_ == 0 {
                    leanh::lean_ctor_set(v___x_2450_, 2, v___x_2452_);
                    v___x_2454_ = v___x_2450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2455_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_str_2439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_startInclusive_2440_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2455_, 2, v___x_2452_);
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
    mut v_suff_2460_: *mut leanh::LeanObject,
    mut v_s_2461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2462_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(
        v_suff_2460_,
        v_s_2461_,
    );
    leanh::lean_dec_ref(v_suff_2460_);
    return v_res_2462_;
}
pub unsafe fn l_String_Slice_stripSuffix(
    mut v_s_2463_: *mut leanh::LeanObject,
    mut v_suff_2464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2465_ = l_String_Slice_dropSuffix___at___00String_Slice_stripSuffix_spec__0(
        v_suff_2464_,
        v_s_2463_,
    );
    return v___x_2465_;
}
pub unsafe fn l_String_Slice_stripSuffix___boxed(
    mut v_s_2466_: *mut leanh::LeanObject,
    mut v_suff_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2468_ = l_String_Slice_stripSuffix(v_s_2466_, v_suff_2467_);
    leanh::lean_dec_ref(v_suff_2467_);
    return v_res_2468_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_TakeDrop(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Substring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_TakeDrop(
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
pub unsafe fn initialize_Init_Data_String_TakeDrop(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Substring(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_TakeDrop(builtin);
}