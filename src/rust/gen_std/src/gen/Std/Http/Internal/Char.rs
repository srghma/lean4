// Lean compiler output
// Module: Std.Http.Internal.Char
// Imports: Init.Data.Char Init.Data.String.Basic Init.Data.Int Init.Grind
use crate::ffi::{
    lean_nat_dec_le, lean_nat_dec_lt, lean_uint8_dec_eq, lean_uint8_dec_le, lean_uint8_dec_lt,
    lean_uint32_dec_eq, lean_uint32_dec_le, lean_uint32_to_nat, lean_uint32_to_uint8,
};
use crate::r#gen::Init::Data::Char::{
    initialize_Init_Data_Char, runtime_initialize_Init_Data_Char,
};
use crate::r#gen::Init::Data::Int::{initialize_Init_Data_Int, runtime_initialize_Init_Data_Int};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
static mut l_Std_Http_Internal_Char_isDigitByte___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isDigitByte___closed__0: u8 = 0;
static mut l_Std_Http_Internal_Char_isDigitByte___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isDigitByte___closed__1: u8 = 0;
static mut l_Std_Http_Internal_Char_isAlphaByte___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isAlphaByte___closed__0: u8 = 0;
static mut l_Std_Http_Internal_Char_isAlphaByte___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isAlphaByte___closed__1: u8 = 0;
static mut l_Std_Http_Internal_Char_isAlphaByte___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isAlphaByte___closed__2: u8 = 0;
static mut l_Std_Http_Internal_Char_isAlphaByte___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isAlphaByte___closed__3: u8 = 0;
static mut l_Std_Http_Internal_Char_isHexDigitByte___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isHexDigitByte___closed__0: u8 = 0;
static mut l_Std_Http_Internal_Char_isHexDigitByte___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isHexDigitByte___closed__1: u8 = 0;
static mut l_Std_Http_Internal_Char_isUnreserved___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isUnreserved___closed__0: u8 = 0;
static mut l_Std_Http_Internal_Char_isUnreserved___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isUnreserved___closed__1: u8 = 0;
static mut l_Std_Http_Internal_Char_isUnreserved___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isUnreserved___closed__2: u8 = 0;
static mut l_Std_Http_Internal_Char_isUnreserved___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isUnreserved___closed__3: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__0: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__1: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__2: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__3: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__4: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__5: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__6: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__7: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__8: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__9: u8 = 0;
static mut l_Std_Http_Internal_Char_isSubDelims___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isSubDelims___closed__10: u8 = 0;
static mut l_Std_Http_Internal_Char_isPChar___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isPChar___closed__0: u8 = 0;
static mut l_Std_Http_Internal_Char_isPChar___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isPChar___closed__1: u8 = 0;
static mut l_Std_Http_Internal_Char_isQueryChar___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isQueryChar___closed__0: u8 = 0;
static mut l_Std_Http_Internal_Char_isQueryChar___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Std_Http_Internal_Char_isQueryChar___closed__1: u8 = 0;
pub unsafe fn l_Std_Http_Internal_Char_isAscii(mut v_c_986_: u32) -> u8 {
    let mut v___x_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u8 = 0;
    v___x_987_ = lean_uint32_to_nat(v_c_986_);
    v___x_988_ = leanh::lean_unsigned_to_nat(128);
    v___x_989_ = lean_nat_dec_lt(v___x_987_, v___x_988_);
    leanh::lean_dec(v___x_987_);
    return v___x_989_;
}
pub unsafe fn l_Std_Http_Internal_Char_isAscii___boxed(
    mut v_c_990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_991_: u32 = 0;
    let mut v_res_992_: u8 = 0;
    let mut v_r_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_991_ = leanh::lean_unbox_uint32(v_c_990_);
    leanh::lean_dec(v_c_990_);
    v_res_992_ = l_Std_Http_Internal_Char_isAscii(v_c_boxed_991_);
    v_r_993_ = leanh::lean_box((v_res_992_) as usize);
    return v_r_993_;
}
pub unsafe fn l_Std_Http_Internal_Char_isAsciiByte(mut v_c_994_: u8) -> u8 {
    let mut v___x_995_: u8 = 0;
    let mut v___x_996_: u8 = 0;
    v___x_995_ = 128;
    v___x_996_ = lean_uint8_dec_lt(v_c_994_, v___x_995_);
    return v___x_996_;
}
pub unsafe fn l_Std_Http_Internal_Char_isAsciiByte___boxed(
    mut v_c_997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_998_: u8 = 0;
    let mut v_res_999_: u8 = 0;
    let mut v_r_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_998_ = (leanh::lean_unbox(v_c_997_) as u8);
    v_res_999_ = l_Std_Http_Internal_Char_isAsciiByte(v_c_boxed_998_);
    v_r_1000_ = leanh::lean_box((v_res_999_) as usize);
    return v_r_1000_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isDigitByte___closed__0() -> u8 {
    let mut v___x_1001_: u32 = 0;
    let mut v___x_1002_: u8 = 0;
    v___x_1001_ = 48;
    v___x_1002_ = lean_uint32_to_uint8(v___x_1001_);
    return v___x_1002_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isDigitByte___closed__1() -> u8 {
    let mut v___x_1003_: u32 = 0;
    let mut v___x_1004_: u8 = 0;
    v___x_1003_ = 57;
    v___x_1004_ = lean_uint32_to_uint8(v___x_1003_);
    return v___x_1004_;
}
pub unsafe fn l_Std_Http_Internal_Char_isDigitByte(mut v_c_1005_: u8) -> u8 {
    let mut v___x_1006_: u8 = 0;
    let mut v___x_1007_: u8 = 0;
    v___x_1006_ = leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0),
        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0_once),
        _init_l_Std_Http_Internal_Char_isDigitByte___closed__0,
    );
    v___x_1007_ = lean_uint8_dec_le(v___x_1006_, v_c_1005_);
    if v___x_1007_ == 0 {
        return v___x_1007_;
    } else {
        let mut v___x_1008_: u8 = 0;
        let mut v___x_1009_: u8 = 0;
        v___x_1008_ = leanh::lean_uint8_once(
            core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1),
            core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1_once),
            _init_l_Std_Http_Internal_Char_isDigitByte___closed__1,
        );
        v___x_1009_ = lean_uint8_dec_le(v_c_1005_, v___x_1008_);
        return v___x_1009_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isDigitByte___boxed(
    mut v_c_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1011_: u8 = 0;
    let mut v_res_1012_: u8 = 0;
    let mut v_r_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1011_ = (leanh::lean_unbox(v_c_1010_) as u8);
    v_res_1012_ = l_Std_Http_Internal_Char_isDigitByte(v_c_boxed_1011_);
    v_r_1013_ = leanh::lean_box((v_res_1012_) as usize);
    return v_r_1013_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0() -> u8 {
    let mut v___x_1014_: u32 = 0;
    let mut v___x_1015_: u8 = 0;
    v___x_1014_ = 97;
    v___x_1015_ = lean_uint32_to_uint8(v___x_1014_);
    return v___x_1015_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1() -> u8 {
    let mut v___x_1016_: u32 = 0;
    let mut v___x_1017_: u8 = 0;
    v___x_1016_ = 122;
    v___x_1017_ = lean_uint32_to_uint8(v___x_1016_);
    return v___x_1017_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2() -> u8 {
    let mut v___x_1018_: u32 = 0;
    let mut v___x_1019_: u8 = 0;
    v___x_1018_ = 65;
    v___x_1019_ = lean_uint32_to_uint8(v___x_1018_);
    return v___x_1019_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3() -> u8 {
    let mut v___x_1020_: u32 = 0;
    let mut v___x_1021_: u8 = 0;
    v___x_1020_ = 90;
    v___x_1021_ = lean_uint32_to_uint8(v___x_1020_);
    return v___x_1021_;
}
pub unsafe fn l_Std_Http_Internal_Char_isAlphaByte(mut v_c_1022_: u8) -> u8 {
    let mut v___y_1024_: u8 = 0;
    let mut v___x_1025_: u8 = 0;
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1029_: u8 = 0;
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: u8 = 0;
    let mut v___x_1032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1029_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2_once),
                    _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2,
                );
                v___x_1030_ = lean_uint8_dec_le(v___x_1029_, v_c_1022_);
                if v___x_1030_ == 0 {
                    v___y_1024_ = v___x_1030_;
                    state = 1;
                    continue;
                } else {
                    v___x_1031_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__3_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3,
                    );
                    v___x_1032_ = lean_uint8_dec_le(v_c_1022_, v___x_1031_);
                    v___y_1024_ = v___x_1032_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1024_ == 0 {
                    v___x_1025_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0,
                    );
                    v___x_1026_ = lean_uint8_dec_le(v___x_1025_, v_c_1022_);
                    if v___x_1026_ == 0 {
                        return v___x_1026_;
                    } else {
                        v___x_1027_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1,
                        );
                        v___x_1028_ = lean_uint8_dec_le(v_c_1022_, v___x_1027_);
                        return v___x_1028_;
                    }
                } else {
                    return v___y_1024_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isAlphaByte___boxed(
    mut v_c_1033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1034_: u8 = 0;
    let mut v_res_1035_: u8 = 0;
    let mut v_r_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1034_ = (leanh::lean_unbox(v_c_1033_) as u8);
    v_res_1035_ = l_Std_Http_Internal_Char_isAlphaByte(v_c_boxed_1034_);
    v_r_1036_ = leanh::lean_box((v_res_1035_) as usize);
    return v_r_1036_;
}
pub unsafe fn l_Std_Http_Internal_Char_tchar(mut v_c_1037_: u32) -> u8 {
    let mut v___x_1039_: u32 = 0;
    let mut v___x_1040_: u8 = 0;
    let mut v___x_1041_: u32 = 0;
    let mut v___x_1042_: u8 = 0;
    let mut v___y_1044_: u8 = 0;
    let mut v___x_1045_: u32 = 0;
    let mut v___x_1046_: u8 = 0;
    let mut v___x_1047_: u32 = 0;
    let mut v___x_1048_: u8 = 0;
    let mut v___x_1049_: u32 = 0;
    let mut v___x_1050_: u8 = 0;
    let mut v___x_1051_: u32 = 0;
    let mut v___x_1052_: u8 = 0;
    let mut v___x_1053_: u32 = 0;
    let mut v___x_1054_: u8 = 0;
    let mut v___x_1055_: u32 = 0;
    let mut v___x_1056_: u8 = 0;
    let mut v___x_1057_: u32 = 0;
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: u32 = 0;
    let mut v___x_1060_: u8 = 0;
    let mut v___x_1061_: u32 = 0;
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: u32 = 0;
    let mut v___x_1064_: u8 = 0;
    let mut v___x_1065_: u32 = 0;
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: u32 = 0;
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: u32 = 0;
    let mut v___x_1070_: u8 = 0;
    let mut v___x_1071_: u32 = 0;
    let mut v___x_1072_: u8 = 0;
    let mut v___x_1073_: u32 = 0;
    let mut v___x_1074_: u8 = 0;
    let mut v___x_1075_: u32 = 0;
    let mut v___x_1076_: u8 = 0;
    let mut v___x_1077_: u32 = 0;
    let mut v___x_1078_: u8 = 0;
    let mut v___x_1079_: u32 = 0;
    let mut v___x_1080_: u8 = 0;
    let mut v___x_1081_: u32 = 0;
    let mut v___x_1082_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1049_ = 33;
                v___x_1050_ = lean_uint32_dec_eq(v_c_1037_, v___x_1049_);
                if v___x_1050_ == 0 {
                    v___x_1051_ = 35;
                    v___x_1052_ = lean_uint32_dec_eq(v_c_1037_, v___x_1051_);
                    if v___x_1052_ == 0 {
                        v___x_1053_ = 36;
                        v___x_1054_ = lean_uint32_dec_eq(v_c_1037_, v___x_1053_);
                        if v___x_1054_ == 0 {
                            v___x_1055_ = 37;
                            v___x_1056_ = lean_uint32_dec_eq(v_c_1037_, v___x_1055_);
                            if v___x_1056_ == 0 {
                                v___x_1057_ = 38;
                                v___x_1058_ = lean_uint32_dec_eq(v_c_1037_, v___x_1057_);
                                if v___x_1058_ == 0 {
                                    v___x_1059_ = 39;
                                    v___x_1060_ = lean_uint32_dec_eq(v_c_1037_, v___x_1059_);
                                    if v___x_1060_ == 0 {
                                        v___x_1061_ = 42;
                                        v___x_1062_ = lean_uint32_dec_eq(v_c_1037_, v___x_1061_);
                                        if v___x_1062_ == 0 {
                                            v___x_1063_ = 43;
                                            v___x_1064_ =
                                                lean_uint32_dec_eq(v_c_1037_, v___x_1063_);
                                            if v___x_1064_ == 0 {
                                                v___x_1065_ = 45;
                                                v___x_1066_ =
                                                    lean_uint32_dec_eq(v_c_1037_, v___x_1065_);
                                                if v___x_1066_ == 0 {
                                                    v___x_1067_ = 46;
                                                    v___x_1068_ =
                                                        lean_uint32_dec_eq(v_c_1037_, v___x_1067_);
                                                    if v___x_1068_ == 0 {
                                                        v___x_1069_ = 94;
                                                        v___x_1070_ = lean_uint32_dec_eq(
                                                            v_c_1037_,
                                                            v___x_1069_,
                                                        );
                                                        if v___x_1070_ == 0 {
                                                            v___x_1071_ = 95;
                                                            v___x_1072_ = lean_uint32_dec_eq(
                                                                v_c_1037_,
                                                                v___x_1071_,
                                                            );
                                                            if v___x_1072_ == 0 {
                                                                v___x_1073_ = 96;
                                                                v___x_1074_ = lean_uint32_dec_eq(
                                                                    v_c_1037_,
                                                                    v___x_1073_,
                                                                );
                                                                if v___x_1074_ == 0 {
                                                                    v___x_1075_ = 124;
                                                                    v___x_1076_ =
                                                                        lean_uint32_dec_eq(
                                                                            v_c_1037_,
                                                                            v___x_1075_,
                                                                        );
                                                                    if v___x_1076_ == 0 {
                                                                        v___x_1077_ = 126;
                                                                        v___x_1078_ =
                                                                            lean_uint32_dec_eq(
                                                                                v_c_1037_,
                                                                                v___x_1077_,
                                                                            );
                                                                        if v___x_1078_ == 0 {
                                                                            v___x_1079_ = 48;
                                                                            v___x_1080_ =
                                                                                lean_uint32_dec_le(
                                                                                    v___x_1079_,
                                                                                    v_c_1037_,
                                                                                );
                                                                            if v___x_1080_ == 0 {
                                                                                v___y_1044_ =
                                                                                    v___x_1080_;
                                                                                state = 2;
                                                                                continue;
                                                                            } else {
                                                                                v___x_1081_ = 57;
                                                                                v___x_1082_ = lean_uint32_dec_le(v_c_1037_, v___x_1081_);
                                                                                v___y_1044_ =
                                                                                    v___x_1082_;
                                                                                state = 2;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            return v___x_1078_;
                                                                        }
                                                                    } else {
                                                                        return v___x_1076_;
                                                                    }
                                                                } else {
                                                                    return v___x_1074_;
                                                                }
                                                            } else {
                                                                return v___x_1072_;
                                                            }
                                                        } else {
                                                            return v___x_1070_;
                                                        }
                                                    } else {
                                                        return v___x_1068_;
                                                    }
                                                } else {
                                                    return v___x_1066_;
                                                }
                                            } else {
                                                return v___x_1064_;
                                            }
                                        } else {
                                            return v___x_1062_;
                                        }
                                    } else {
                                        return v___x_1060_;
                                    }
                                } else {
                                    return v___x_1058_;
                                }
                            } else {
                                return v___x_1056_;
                            }
                        } else {
                            return v___x_1054_;
                        }
                    } else {
                        return v___x_1052_;
                    }
                } else {
                    return v___x_1050_;
                }
            }
            1 => {
                v___x_1039_ = 97;
                v___x_1040_ = lean_uint32_dec_le(v___x_1039_, v_c_1037_);
                if v___x_1040_ == 0 {
                    return v___x_1040_;
                } else {
                    v___x_1041_ = 122;
                    v___x_1042_ = lean_uint32_dec_le(v_c_1037_, v___x_1041_);
                    return v___x_1042_;
                }
            }
            2 => {
                if v___y_1044_ == 0 {
                    v___x_1045_ = 65;
                    v___x_1046_ = lean_uint32_dec_le(v___x_1045_, v_c_1037_);
                    if v___x_1046_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1047_ = 90;
                        v___x_1048_ = lean_uint32_dec_le(v_c_1037_, v___x_1047_);
                        if v___x_1048_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_1048_;
                        }
                    }
                } else {
                    return v___y_1044_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_tchar___boxed(
    mut v_c_1083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1084_: u32 = 0;
    let mut v_res_1085_: u8 = 0;
    let mut v_r_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1084_ = leanh::lean_unbox_uint32(v_c_1083_);
    leanh::lean_dec(v_c_1083_);
    v_res_1085_ = l_Std_Http_Internal_Char_tchar(v_c_boxed_1084_);
    v_r_1086_ = leanh::lean_box((v_res_1085_) as usize);
    return v_r_1086_;
}
pub unsafe fn l_Std_Http_Internal_Char_vchar(mut v_c_1087_: u32) -> u8 {
    let mut v___x_1088_: u32 = 0;
    let mut v___x_1089_: u8 = 0;
    v___x_1088_ = 33;
    v___x_1089_ = lean_uint32_dec_le(v___x_1088_, v_c_1087_);
    if v___x_1089_ == 0 {
        return v___x_1089_;
    } else {
        let mut v___x_1090_: u32 = 0;
        let mut v___x_1091_: u8 = 0;
        v___x_1090_ = 126;
        v___x_1091_ = lean_uint32_dec_le(v_c_1087_, v___x_1090_);
        return v___x_1091_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_vchar___boxed(
    mut v_c_1092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1093_: u32 = 0;
    let mut v_res_1094_: u8 = 0;
    let mut v_r_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1093_ = leanh::lean_unbox_uint32(v_c_1092_);
    leanh::lean_dec(v_c_1092_);
    v_res_1094_ = l_Std_Http_Internal_Char_vchar(v_c_boxed_1093_);
    v_r_1095_ = leanh::lean_box((v_res_1094_) as usize);
    return v_r_1095_;
}
pub unsafe fn l_Std_Http_Internal_Char_qdtext(mut v_c_1096_: u32) -> u8 {
    let mut v___x_1098_: u32 = 0;
    let mut v___x_1099_: u8 = 0;
    let mut v___x_1100_: u32 = 0;
    let mut v___x_1101_: u8 = 0;
    let mut v___x_1102_: u32 = 0;
    let mut v___x_1103_: u8 = 0;
    let mut v___x_1104_: u32 = 0;
    let mut v___x_1105_: u8 = 0;
    let mut v___x_1106_: u32 = 0;
    let mut v___x_1107_: u8 = 0;
    let mut v___x_1108_: u32 = 0;
    let mut v___x_1109_: u8 = 0;
    let mut v___x_1110_: u32 = 0;
    let mut v___x_1111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1102_ = 9;
                v___x_1103_ = lean_uint32_dec_eq(v_c_1096_, v___x_1102_);
                if v___x_1103_ == 0 {
                    v___x_1104_ = 32;
                    v___x_1105_ = lean_uint32_dec_eq(v_c_1096_, v___x_1104_);
                    if v___x_1105_ == 0 {
                        v___x_1106_ = 33;
                        v___x_1107_ = lean_uint32_dec_eq(v_c_1096_, v___x_1106_);
                        if v___x_1107_ == 0 {
                            v___x_1108_ = 35;
                            v___x_1109_ = lean_uint32_dec_le(v___x_1108_, v_c_1096_);
                            if v___x_1109_ == 0 {
                                state = 1;
                                continue;
                            } else {
                                v___x_1110_ = 91;
                                v___x_1111_ = lean_uint32_dec_le(v_c_1096_, v___x_1110_);
                                if v___x_1111_ == 0 {
                                    state = 1;
                                    continue;
                                } else {
                                    return v___x_1111_;
                                }
                            }
                        } else {
                            return v___x_1107_;
                        }
                    } else {
                        return v___x_1105_;
                    }
                } else {
                    return v___x_1103_;
                }
            }
            1 => {
                v___x_1098_ = 93;
                v___x_1099_ = lean_uint32_dec_le(v___x_1098_, v_c_1096_);
                if v___x_1099_ == 0 {
                    return v___x_1099_;
                } else {
                    v___x_1100_ = 126;
                    v___x_1101_ = lean_uint32_dec_le(v_c_1096_, v___x_1100_);
                    return v___x_1101_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_qdtext___boxed(
    mut v_c_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1113_: u32 = 0;
    let mut v_res_1114_: u8 = 0;
    let mut v_r_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1113_ = leanh::lean_unbox_uint32(v_c_1112_);
    leanh::lean_dec(v_c_1112_);
    v_res_1114_ = l_Std_Http_Internal_Char_qdtext(v_c_boxed_1113_);
    v_r_1115_ = leanh::lean_box((v_res_1114_) as usize);
    return v_r_1115_;
}
pub unsafe fn l_Std_Http_Internal_Char_quotedPairChar(mut v_c_1116_: u32) -> u8 {
    let mut v___x_1117_: u32 = 0;
    let mut v___x_1118_: u8 = 0;
    v___x_1117_ = 9;
    v___x_1118_ = lean_uint32_dec_eq(v_c_1116_, v___x_1117_);
    if v___x_1118_ == 0 {
        let mut v___x_1119_: u32 = 0;
        let mut v___x_1120_: u8 = 0;
        v___x_1119_ = 32;
        v___x_1120_ = lean_uint32_dec_eq(v_c_1116_, v___x_1119_);
        if v___x_1120_ == 0 {
            let mut v___x_1121_: u32 = 0;
            let mut v___x_1122_: u8 = 0;
            v___x_1121_ = 33;
            v___x_1122_ = lean_uint32_dec_le(v___x_1121_, v_c_1116_);
            if v___x_1122_ == 0 {
                return v___x_1122_;
            } else {
                let mut v___x_1123_: u32 = 0;
                let mut v___x_1124_: u8 = 0;
                v___x_1123_ = 126;
                v___x_1124_ = lean_uint32_dec_le(v_c_1116_, v___x_1123_);
                return v___x_1124_;
            }
        } else {
            return v___x_1120_;
        }
    } else {
        return v___x_1118_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_quotedPairChar___boxed(
    mut v_c_1125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1126_: u32 = 0;
    let mut v_res_1127_: u8 = 0;
    let mut v_r_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1126_ = leanh::lean_unbox_uint32(v_c_1125_);
    leanh::lean_dec(v_c_1125_);
    v_res_1127_ = l_Std_Http_Internal_Char_quotedPairChar(v_c_boxed_1126_);
    v_r_1128_ = leanh::lean_box((v_res_1127_) as usize);
    return v_r_1128_;
}
pub unsafe fn l_Std_Http_Internal_Char_quotedStringChar(mut v_c_1129_: u32) -> u8 {
    let mut v___x_1131_: u32 = 0;
    let mut v___x_1132_: u8 = 0;
    let mut v___x_1133_: u32 = 0;
    let mut v___x_1134_: u8 = 0;
    let mut v___x_1135_: u32 = 0;
    let mut v___x_1136_: u8 = 0;
    let mut v___x_1137_: u32 = 0;
    let mut v___x_1138_: u8 = 0;
    let mut v___x_1140_: u32 = 0;
    let mut v___x_1141_: u8 = 0;
    let mut v___x_1142_: u32 = 0;
    let mut v___x_1143_: u8 = 0;
    let mut v___x_1144_: u32 = 0;
    let mut v___x_1145_: u8 = 0;
    let mut v___x_1146_: u32 = 0;
    let mut v___x_1147_: u8 = 0;
    let mut v___x_1148_: u32 = 0;
    let mut v___x_1149_: u8 = 0;
    let mut v___x_1150_: u32 = 0;
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: u32 = 0;
    let mut v___x_1153_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1144_ = 9;
                v___x_1145_ = lean_uint32_dec_eq(v_c_1129_, v___x_1144_);
                if v___x_1145_ == 0 {
                    v___x_1146_ = 32;
                    v___x_1147_ = lean_uint32_dec_eq(v_c_1129_, v___x_1146_);
                    if v___x_1147_ == 0 {
                        v___x_1148_ = 33;
                        v___x_1149_ = lean_uint32_dec_eq(v_c_1129_, v___x_1148_);
                        if v___x_1149_ == 0 {
                            v___x_1150_ = 35;
                            v___x_1151_ = lean_uint32_dec_le(v___x_1150_, v_c_1129_);
                            if v___x_1151_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                v___x_1152_ = 91;
                                v___x_1153_ = lean_uint32_dec_le(v_c_1129_, v___x_1152_);
                                if v___x_1153_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    return v___x_1153_;
                                }
                            }
                        } else {
                            return v___x_1149_;
                        }
                    } else {
                        return v___x_1147_;
                    }
                } else {
                    return v___x_1145_;
                }
            }
            1 => {
                v___x_1131_ = 9;
                v___x_1132_ = lean_uint32_dec_eq(v_c_1129_, v___x_1131_);
                if v___x_1132_ == 0 {
                    v___x_1133_ = 32;
                    v___x_1134_ = lean_uint32_dec_eq(v_c_1129_, v___x_1133_);
                    if v___x_1134_ == 0 {
                        v___x_1135_ = 33;
                        v___x_1136_ = lean_uint32_dec_le(v___x_1135_, v_c_1129_);
                        if v___x_1136_ == 0 {
                            return v___x_1136_;
                        } else {
                            v___x_1137_ = 126;
                            v___x_1138_ = lean_uint32_dec_le(v_c_1129_, v___x_1137_);
                            return v___x_1138_;
                        }
                    } else {
                        return v___x_1134_;
                    }
                } else {
                    return v___x_1132_;
                }
            }
            2 => {
                v___x_1140_ = 93;
                v___x_1141_ = lean_uint32_dec_le(v___x_1140_, v_c_1129_);
                if v___x_1141_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1142_ = 126;
                    v___x_1143_ = lean_uint32_dec_le(v_c_1129_, v___x_1142_);
                    if v___x_1143_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        return v___x_1143_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_quotedStringChar___boxed(
    mut v_c_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1155_: u32 = 0;
    let mut v_res_1156_: u8 = 0;
    let mut v_r_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1155_ = leanh::lean_unbox_uint32(v_c_1154_);
    leanh::lean_dec(v_c_1154_);
    v_res_1156_ = l_Std_Http_Internal_Char_quotedStringChar(v_c_boxed_1155_);
    v_r_1157_ = leanh::lean_box((v_res_1156_) as usize);
    return v_r_1157_;
}
pub unsafe fn l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(
    mut v_c_1158_: u32,
    mut v_h__1_1159_: *mut leanh::LeanObject,
    mut v_h__2_1160_: *mut leanh::LeanObject,
    mut v_h__3_1161_: *mut leanh::LeanObject,
    mut v_h__4_1162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1163_: u32 = 0;
    let mut v___x_1164_: u8 = 0;
    v___x_1163_ = 9;
    v___x_1164_ = lean_uint32_dec_eq(v_c_1158_, v___x_1163_);
    if v___x_1164_ == 0 {
        let mut v___x_1165_: u32 = 0;
        let mut v___x_1166_: u8 = 0;
        leanh::lean_dec(v_h__1_1159_);
        v___x_1165_ = 32;
        v___x_1166_ = lean_uint32_dec_eq(v_c_1158_, v___x_1165_);
        if v___x_1166_ == 0 {
            let mut v___x_1167_: u32 = 0;
            let mut v___x_1168_: u8 = 0;
            leanh::lean_dec(v_h__2_1160_);
            v___x_1167_ = 33;
            v___x_1168_ = lean_uint32_dec_eq(v_c_1158_, v___x_1167_);
            if v___x_1168_ == 0 {
                let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_1161_);
                v___x_1169_ = leanh::lean_box_uint32(v_c_1158_);
                v___x_1170_ = leanh::lean_apply_4(
                    v_h__4_1162_,
                    v___x_1169_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1170_;
            } else {
                let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_1162_);
                v___x_1171_ = leanh::lean_box(0);
                v___x_1172_ = leanh::lean_apply_1(v_h__3_1161_, v___x_1171_);
                return v___x_1172_;
            }
        } else {
            let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1162_);
            leanh::lean_dec(v_h__3_1161_);
            v___x_1173_ = leanh::lean_box(0);
            v___x_1174_ = leanh::lean_apply_1(v_h__2_1160_, v___x_1173_);
            return v___x_1174_;
        }
    } else {
        let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__4_1162_);
        leanh::lean_dec(v_h__3_1161_);
        leanh::lean_dec(v_h__2_1160_);
        v___x_1175_ = leanh::lean_box(0);
        v___x_1176_ = leanh::lean_apply_1(v_h__1_1159_, v___x_1175_);
        return v___x_1176_;
    }
}
pub unsafe fn l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg___boxed(
    mut v_c_1177_: *mut leanh::LeanObject,
    mut v_h__1_1178_: *mut leanh::LeanObject,
    mut v_h__2_1179_: *mut leanh::LeanObject,
    mut v_h__3_1180_: *mut leanh::LeanObject,
    mut v_h__4_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_46__boxed_1182_: u32 = 0;
    let mut v_res_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_46__boxed_1182_ = leanh::lean_unbox_uint32(v_c_1177_);
    leanh::lean_dec(v_c_1177_);
    v_res_1183_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___redArg(v_c_46__boxed_1182_, v_h__1_1178_, v_h__2_1179_, v_h__3_1180_, v_h__4_1181_);
    return v_res_1183_;
}
pub unsafe fn l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(
    mut v_motive_1184_: *mut leanh::LeanObject,
    mut v_c_1185_: u32,
    mut v_h__1_1186_: *mut leanh::LeanObject,
    mut v_h__2_1187_: *mut leanh::LeanObject,
    mut v_h__3_1188_: *mut leanh::LeanObject,
    mut v_h__4_1189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1190_: u32 = 0;
    let mut v___x_1191_: u8 = 0;
    v___x_1190_ = 9;
    v___x_1191_ = lean_uint32_dec_eq(v_c_1185_, v___x_1190_);
    if v___x_1191_ == 0 {
        let mut v___x_1192_: u32 = 0;
        let mut v___x_1193_: u8 = 0;
        leanh::lean_dec(v_h__1_1186_);
        v___x_1192_ = 32;
        v___x_1193_ = lean_uint32_dec_eq(v_c_1185_, v___x_1192_);
        if v___x_1193_ == 0 {
            let mut v___x_1194_: u32 = 0;
            let mut v___x_1195_: u8 = 0;
            leanh::lean_dec(v_h__2_1187_);
            v___x_1194_ = 33;
            v___x_1195_ = lean_uint32_dec_eq(v_c_1185_, v___x_1194_);
            if v___x_1195_ == 0 {
                let mut v___x_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_1188_);
                v___x_1196_ = leanh::lean_box_uint32(v_c_1185_);
                v___x_1197_ = leanh::lean_apply_4(
                    v_h__4_1189_,
                    v___x_1196_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1197_;
            } else {
                let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_1189_);
                v___x_1198_ = leanh::lean_box(0);
                v___x_1199_ = leanh::lean_apply_1(v_h__3_1188_, v___x_1198_);
                return v___x_1199_;
            }
        } else {
            let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1189_);
            leanh::lean_dec(v_h__3_1188_);
            v___x_1200_ = leanh::lean_box(0);
            v___x_1201_ = leanh::lean_apply_1(v_h__2_1187_, v___x_1200_);
            return v___x_1201_;
        }
    } else {
        let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__4_1189_);
        leanh::lean_dec(v_h__3_1188_);
        leanh::lean_dec(v_h__2_1187_);
        v___x_1202_ = leanh::lean_box(0);
        v___x_1203_ = leanh::lean_apply_1(v_h__1_1186_, v___x_1202_);
        return v___x_1203_;
    }
}
pub unsafe fn l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter___boxed(
    mut v_motive_1204_: *mut leanh::LeanObject,
    mut v_c_1205_: *mut leanh::LeanObject,
    mut v_h__1_1206_: *mut leanh::LeanObject,
    mut v_h__2_1207_: *mut leanh::LeanObject,
    mut v_h__3_1208_: *mut leanh::LeanObject,
    mut v_h__4_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_77__boxed_1210_: u32 = 0;
    let mut v_res_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_77__boxed_1210_ = leanh::lean_unbox_uint32(v_c_1205_);
    leanh::lean_dec(v_c_1205_);
    v_res_1211_ =
        l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_qdtext_match__1_splitter(
            v_motive_1204_,
            v_c_77__boxed_1210_,
            v_h__1_1206_,
            v_h__2_1207_,
            v_h__3_1208_,
            v_h__4_1209_,
        );
    return v_res_1211_;
}
pub unsafe fn l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(
    mut v_c_1212_: u32,
    mut v_h__1_1213_: *mut leanh::LeanObject,
    mut v_h__2_1214_: *mut leanh::LeanObject,
    mut v_h__3_1215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1216_: u32 = 0;
    let mut v___x_1217_: u8 = 0;
    v___x_1216_ = 9;
    v___x_1217_ = lean_uint32_dec_eq(v_c_1212_, v___x_1216_);
    if v___x_1217_ == 0 {
        let mut v___x_1218_: u32 = 0;
        let mut v___x_1219_: u8 = 0;
        leanh::lean_dec(v_h__1_1213_);
        v___x_1218_ = 32;
        v___x_1219_ = lean_uint32_dec_eq(v_c_1212_, v___x_1218_);
        if v___x_1219_ == 0 {
            let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1214_);
            v___x_1220_ = leanh::lean_box_uint32(v_c_1212_);
            v___x_1221_ = leanh::lean_apply_3(
                v_h__3_1215_,
                v___x_1220_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1221_;
        } else {
            let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1215_);
            v___x_1222_ = leanh::lean_box(0);
            v___x_1223_ = leanh::lean_apply_1(v_h__2_1214_, v___x_1222_);
            return v___x_1223_;
        }
    } else {
        let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1215_);
        leanh::lean_dec(v_h__2_1214_);
        v___x_1224_ = leanh::lean_box(0);
        v___x_1225_ = leanh::lean_apply_1(v_h__1_1213_, v___x_1224_);
        return v___x_1225_;
    }
}
pub unsafe fn l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg___boxed(
    mut v_c_1226_: *mut leanh::LeanObject,
    mut v_h__1_1227_: *mut leanh::LeanObject,
    mut v_h__2_1228_: *mut leanh::LeanObject,
    mut v_h__3_1229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_33__boxed_1230_: u32 = 0;
    let mut v_res_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_33__boxed_1230_ = leanh::lean_unbox_uint32(v_c_1226_);
    leanh::lean_dec(v_c_1226_);
    v_res_1231_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___redArg(v_c_33__boxed_1230_, v_h__1_1227_, v_h__2_1228_, v_h__3_1229_);
    return v_res_1231_;
}
pub unsafe fn l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(
    mut v_motive_1232_: *mut leanh::LeanObject,
    mut v_c_1233_: u32,
    mut v_h__1_1234_: *mut leanh::LeanObject,
    mut v_h__2_1235_: *mut leanh::LeanObject,
    mut v_h__3_1236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1237_: u32 = 0;
    let mut v___x_1238_: u8 = 0;
    v___x_1237_ = 9;
    v___x_1238_ = lean_uint32_dec_eq(v_c_1233_, v___x_1237_);
    if v___x_1238_ == 0 {
        let mut v___x_1239_: u32 = 0;
        let mut v___x_1240_: u8 = 0;
        leanh::lean_dec(v_h__1_1234_);
        v___x_1239_ = 32;
        v___x_1240_ = lean_uint32_dec_eq(v_c_1233_, v___x_1239_);
        if v___x_1240_ == 0 {
            let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1235_);
            v___x_1241_ = leanh::lean_box_uint32(v_c_1233_);
            v___x_1242_ = leanh::lean_apply_3(
                v_h__3_1236_,
                v___x_1241_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1242_;
        } else {
            let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1236_);
            v___x_1243_ = leanh::lean_box(0);
            v___x_1244_ = leanh::lean_apply_1(v_h__2_1235_, v___x_1243_);
            return v___x_1244_;
        }
    } else {
        let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1236_);
        leanh::lean_dec(v_h__2_1235_);
        v___x_1245_ = leanh::lean_box(0);
        v___x_1246_ = leanh::lean_apply_1(v_h__1_1234_, v___x_1245_);
        return v___x_1246_;
    }
}
pub unsafe fn l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter___boxed(
    mut v_motive_1247_: *mut leanh::LeanObject,
    mut v_c_1248_: *mut leanh::LeanObject,
    mut v_h__1_1249_: *mut leanh::LeanObject,
    mut v_h__2_1250_: *mut leanh::LeanObject,
    mut v_h__3_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_56__boxed_1252_: u32 = 0;
    let mut v_res_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_56__boxed_1252_ = leanh::lean_unbox_uint32(v_c_1248_);
    leanh::lean_dec(v_c_1248_);
    v_res_1253_ = l___private_Std_Http_Internal_Char_0__Std_Http_Internal_Char_quotedPairChar_match__1_splitter(v_motive_1247_, v_c_56__boxed_1252_, v_h__1_1249_, v_h__2_1250_, v_h__3_1251_);
    return v_res_1253_;
}
pub unsafe fn l_Std_Http_Internal_Char_fieldVchar(mut v_c_1254_: u32) -> u8 {
    let mut v___x_1255_: u32 = 0;
    let mut v___x_1256_: u8 = 0;
    v___x_1255_ = 33;
    v___x_1256_ = lean_uint32_dec_le(v___x_1255_, v_c_1254_);
    if v___x_1256_ == 0 {
        return v___x_1256_;
    } else {
        let mut v___x_1257_: u32 = 0;
        let mut v___x_1258_: u8 = 0;
        v___x_1257_ = 126;
        v___x_1258_ = lean_uint32_dec_le(v_c_1254_, v___x_1257_);
        return v___x_1258_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_fieldVchar___boxed(
    mut v_c_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1260_: u32 = 0;
    let mut v_res_1261_: u8 = 0;
    let mut v_r_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1260_ = leanh::lean_unbox_uint32(v_c_1259_);
    leanh::lean_dec(v_c_1259_);
    v_res_1261_ = l_Std_Http_Internal_Char_fieldVchar(v_c_boxed_1260_);
    v_r_1262_ = leanh::lean_box((v_res_1261_) as usize);
    return v_r_1262_;
}
pub unsafe fn l_Std_Http_Internal_Char_fieldContent(mut v_c_1263_: u32) -> u8 {
    let mut v___x_1265_: u32 = 0;
    let mut v___x_1266_: u8 = 0;
    let mut v___x_1267_: u32 = 0;
    let mut v___x_1268_: u8 = 0;
    let mut v___x_1269_: u32 = 0;
    let mut v___x_1270_: u8 = 0;
    let mut v___x_1271_: u32 = 0;
    let mut v___x_1272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1269_ = 33;
                v___x_1270_ = lean_uint32_dec_le(v___x_1269_, v_c_1263_);
                if v___x_1270_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1271_ = 126;
                    v___x_1272_ = lean_uint32_dec_le(v_c_1263_, v___x_1271_);
                    if v___x_1272_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        return v___x_1272_;
                    }
                }
            }
            1 => {
                v___x_1265_ = 32;
                v___x_1266_ = lean_uint32_dec_eq(v_c_1263_, v___x_1265_);
                if v___x_1266_ == 0 {
                    v___x_1267_ = 9;
                    v___x_1268_ = lean_uint32_dec_eq(v_c_1263_, v___x_1267_);
                    return v___x_1268_;
                } else {
                    return v___x_1266_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_fieldContent___boxed(
    mut v_c_1273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1274_: u32 = 0;
    let mut v_res_1275_: u8 = 0;
    let mut v_r_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1274_ = leanh::lean_unbox_uint32(v_c_1273_);
    leanh::lean_dec(v_c_1273_);
    v_res_1275_ = l_Std_Http_Internal_Char_fieldContent(v_c_boxed_1274_);
    v_r_1276_ = leanh::lean_box((v_res_1275_) as usize);
    return v_r_1276_;
}
pub unsafe fn l_Std_Http_Internal_Char_ctext(mut v_c_1277_: u32) -> u8 {
    let mut v___x_1279_: u32 = 0;
    let mut v___x_1280_: u8 = 0;
    let mut v___x_1281_: u32 = 0;
    let mut v___x_1282_: u8 = 0;
    let mut v___x_1284_: u32 = 0;
    let mut v___x_1285_: u8 = 0;
    let mut v___x_1286_: u32 = 0;
    let mut v___x_1287_: u8 = 0;
    let mut v___x_1288_: u32 = 0;
    let mut v___x_1289_: u8 = 0;
    let mut v___x_1290_: u32 = 0;
    let mut v___x_1291_: u8 = 0;
    let mut v___x_1292_: u32 = 0;
    let mut v___x_1293_: u8 = 0;
    let mut v___x_1294_: u32 = 0;
    let mut v___x_1295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1288_ = 9;
                v___x_1289_ = lean_uint32_dec_eq(v_c_1277_, v___x_1288_);
                if v___x_1289_ == 0 {
                    v___x_1290_ = 32;
                    v___x_1291_ = lean_uint32_dec_eq(v_c_1277_, v___x_1290_);
                    if v___x_1291_ == 0 {
                        v___x_1292_ = 33;
                        v___x_1293_ = lean_uint32_dec_le(v___x_1292_, v_c_1277_);
                        if v___x_1293_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_1294_ = 39;
                            v___x_1295_ = lean_uint32_dec_le(v_c_1277_, v___x_1294_);
                            if v___x_1295_ == 0 {
                                state = 2;
                                continue;
                            } else {
                                return v___x_1295_;
                            }
                        }
                    } else {
                        return v___x_1291_;
                    }
                } else {
                    return v___x_1289_;
                }
            }
            1 => {
                v___x_1279_ = 93;
                v___x_1280_ = lean_uint32_dec_le(v___x_1279_, v_c_1277_);
                if v___x_1280_ == 0 {
                    return v___x_1280_;
                } else {
                    v___x_1281_ = 126;
                    v___x_1282_ = lean_uint32_dec_le(v_c_1277_, v___x_1281_);
                    return v___x_1282_;
                }
            }
            2 => {
                v___x_1284_ = 42;
                v___x_1285_ = lean_uint32_dec_le(v___x_1284_, v_c_1277_);
                if v___x_1285_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1286_ = 91;
                    v___x_1287_ = lean_uint32_dec_le(v_c_1277_, v___x_1286_);
                    if v___x_1287_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        return v___x_1287_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_ctext___boxed(
    mut v_c_1296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1297_: u32 = 0;
    let mut v_res_1298_: u8 = 0;
    let mut v_r_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1297_ = leanh::lean_unbox_uint32(v_c_1296_);
    leanh::lean_dec(v_c_1296_);
    v_res_1298_ = l_Std_Http_Internal_Char_ctext(v_c_boxed_1297_);
    v_r_1299_ = leanh::lean_box((v_res_1298_) as usize);
    return v_r_1299_;
}
pub unsafe fn l_Std_Http_Internal_Char_etagc(mut v_c_1300_: u32) -> u8 {
    let mut v___x_1301_: u32 = 0;
    let mut v___x_1302_: u8 = 0;
    v___x_1301_ = 33;
    v___x_1302_ = lean_uint32_dec_eq(v_c_1300_, v___x_1301_);
    if v___x_1302_ == 0 {
        let mut v___x_1303_: u32 = 0;
        let mut v___x_1304_: u8 = 0;
        v___x_1303_ = 35;
        v___x_1304_ = lean_uint32_dec_le(v___x_1303_, v_c_1300_);
        if v___x_1304_ == 0 {
            return v___x_1302_;
        } else {
            let mut v___x_1305_: u32 = 0;
            let mut v___x_1306_: u8 = 0;
            v___x_1305_ = 126;
            v___x_1306_ = lean_uint32_dec_le(v_c_1300_, v___x_1305_);
            if v___x_1306_ == 0 {
                return v___x_1302_;
            } else {
                return v___x_1306_;
            }
        }
    } else {
        return v___x_1302_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_etagc___boxed(
    mut v_c_1307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1308_: u32 = 0;
    let mut v_res_1309_: u8 = 0;
    let mut v_r_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1308_ = leanh::lean_unbox_uint32(v_c_1307_);
    leanh::lean_dec(v_c_1307_);
    v_res_1309_ = l_Std_Http_Internal_Char_etagc(v_c_boxed_1308_);
    v_r_1310_ = leanh::lean_box((v_res_1309_) as usize);
    return v_r_1310_;
}
pub unsafe fn l_Std_Http_Internal_Char_ows(mut v_c_1311_: u32) -> u8 {
    let mut v___x_1312_: u32 = 0;
    let mut v___x_1313_: u8 = 0;
    v___x_1312_ = 32;
    v___x_1313_ = lean_uint32_dec_eq(v_c_1311_, v___x_1312_);
    if v___x_1313_ == 0 {
        let mut v___x_1314_: u32 = 0;
        let mut v___x_1315_: u8 = 0;
        v___x_1314_ = 9;
        v___x_1315_ = lean_uint32_dec_eq(v_c_1311_, v___x_1314_);
        return v___x_1315_;
    } else {
        return v___x_1313_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_ows___boxed(
    mut v_c_1316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1317_: u32 = 0;
    let mut v_res_1318_: u8 = 0;
    let mut v_r_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1317_ = leanh::lean_unbox_uint32(v_c_1316_);
    leanh::lean_dec(v_c_1316_);
    v_res_1318_ = l_Std_Http_Internal_Char_ows(v_c_boxed_1317_);
    v_r_1319_ = leanh::lean_box((v_res_1318_) as usize);
    return v_r_1319_;
}
pub unsafe fn l_Std_Http_Internal_Char_bws(mut v_c_1320_: u32) -> u8 {
    let mut v___x_1321_: u32 = 0;
    let mut v___x_1322_: u8 = 0;
    v___x_1321_ = 32;
    v___x_1322_ = lean_uint32_dec_eq(v_c_1320_, v___x_1321_);
    if v___x_1322_ == 0 {
        let mut v___x_1323_: u32 = 0;
        let mut v___x_1324_: u8 = 0;
        v___x_1323_ = 9;
        v___x_1324_ = lean_uint32_dec_eq(v_c_1320_, v___x_1323_);
        return v___x_1324_;
    } else {
        return v___x_1322_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_bws___boxed(
    mut v_c_1325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1326_: u32 = 0;
    let mut v_res_1327_: u8 = 0;
    let mut v_r_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1326_ = leanh::lean_unbox_uint32(v_c_1325_);
    leanh::lean_dec(v_c_1325_);
    v_res_1327_ = l_Std_Http_Internal_Char_bws(v_c_boxed_1326_);
    v_r_1328_ = leanh::lean_box((v_res_1327_) as usize);
    return v_r_1328_;
}
pub unsafe fn l_Std_Http_Internal_Char_rws(mut v_c_1329_: u32) -> u8 {
    let mut v___x_1330_: u32 = 0;
    let mut v___x_1331_: u8 = 0;
    v___x_1330_ = 32;
    v___x_1331_ = lean_uint32_dec_eq(v_c_1329_, v___x_1330_);
    if v___x_1331_ == 0 {
        let mut v___x_1332_: u32 = 0;
        let mut v___x_1333_: u8 = 0;
        v___x_1332_ = 9;
        v___x_1333_ = lean_uint32_dec_eq(v_c_1329_, v___x_1332_);
        return v___x_1333_;
    } else {
        return v___x_1331_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_rws___boxed(
    mut v_c_1334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1335_: u32 = 0;
    let mut v_res_1336_: u8 = 0;
    let mut v_r_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1335_ = leanh::lean_unbox_uint32(v_c_1334_);
    leanh::lean_dec(v_c_1334_);
    v_res_1336_ = l_Std_Http_Internal_Char_rws(v_c_boxed_1335_);
    v_r_1337_ = leanh::lean_box((v_res_1336_) as usize);
    return v_r_1337_;
}
pub unsafe fn l_Std_Http_Internal_Char_obsText(mut v_c_1338_: u32) -> u8 {
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    v___x_1339_ = leanh::lean_unsigned_to_nat(128);
    v___x_1340_ = lean_uint32_to_nat(v_c_1338_);
    v___x_1341_ = lean_nat_dec_le(v___x_1339_, v___x_1340_);
    leanh::lean_dec(v___x_1340_);
    return v___x_1341_;
}
pub unsafe fn l_Std_Http_Internal_Char_obsText___boxed(
    mut v_c_1342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1343_: u32 = 0;
    let mut v_res_1344_: u8 = 0;
    let mut v_r_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1343_ = leanh::lean_unbox_uint32(v_c_1342_);
    leanh::lean_dec(v_c_1342_);
    v_res_1344_ = l_Std_Http_Internal_Char_obsText(v_c_boxed_1343_);
    v_r_1345_ = leanh::lean_box((v_res_1344_) as usize);
    return v_r_1345_;
}
pub unsafe fn l_Std_Http_Internal_Char_reasonPhraseChar(mut v_c_1346_: u32) -> u8 {
    let mut v___x_1347_: u32 = 0;
    let mut v___x_1348_: u8 = 0;
    v___x_1347_ = 9;
    v___x_1348_ = lean_uint32_dec_eq(v_c_1346_, v___x_1347_);
    if v___x_1348_ == 0 {
        let mut v___x_1349_: u32 = 0;
        let mut v___x_1350_: u8 = 0;
        v___x_1349_ = 32;
        v___x_1350_ = lean_uint32_dec_eq(v_c_1346_, v___x_1349_);
        if v___x_1350_ == 0 {
            let mut v___x_1351_: u32 = 0;
            let mut v___x_1352_: u8 = 0;
            v___x_1351_ = 33;
            v___x_1352_ = lean_uint32_dec_le(v___x_1351_, v_c_1346_);
            if v___x_1352_ == 0 {
                return v___x_1352_;
            } else {
                let mut v___x_1353_: u32 = 0;
                let mut v___x_1354_: u8 = 0;
                v___x_1353_ = 126;
                v___x_1354_ = lean_uint32_dec_le(v_c_1346_, v___x_1353_);
                return v___x_1354_;
            }
        } else {
            return v___x_1350_;
        }
    } else {
        return v___x_1348_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_reasonPhraseChar___boxed(
    mut v_c_1355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1356_: u32 = 0;
    let mut v_res_1357_: u8 = 0;
    let mut v_r_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1356_ = leanh::lean_unbox_uint32(v_c_1355_);
    leanh::lean_dec(v_c_1355_);
    v_res_1357_ = l_Std_Http_Internal_Char_reasonPhraseChar(v_c_boxed_1356_);
    v_r_1358_ = leanh::lean_box((v_res_1357_) as usize);
    return v_r_1358_;
}
pub unsafe fn l_Std_Http_Internal_Char_isHexDigit(mut v_c_1359_: u32) -> u8 {
    let mut v___x_1360_: u32 = 0;
    let mut v___x_1361_: u8 = 0;
    v___x_1360_ = 97;
    v___x_1361_ = lean_uint32_dec_eq(v_c_1359_, v___x_1360_);
    if v___x_1361_ == 0 {
        let mut v___x_1362_: u32 = 0;
        let mut v___x_1363_: u8 = 0;
        v___x_1362_ = 98;
        v___x_1363_ = lean_uint32_dec_eq(v_c_1359_, v___x_1362_);
        if v___x_1363_ == 0 {
            let mut v___x_1364_: u32 = 0;
            let mut v___x_1365_: u8 = 0;
            v___x_1364_ = 99;
            v___x_1365_ = lean_uint32_dec_eq(v_c_1359_, v___x_1364_);
            if v___x_1365_ == 0 {
                let mut v___x_1366_: u32 = 0;
                let mut v___x_1367_: u8 = 0;
                v___x_1366_ = 100;
                v___x_1367_ = lean_uint32_dec_eq(v_c_1359_, v___x_1366_);
                if v___x_1367_ == 0 {
                    let mut v___x_1368_: u32 = 0;
                    let mut v___x_1369_: u8 = 0;
                    v___x_1368_ = 101;
                    v___x_1369_ = lean_uint32_dec_eq(v_c_1359_, v___x_1368_);
                    if v___x_1369_ == 0 {
                        let mut v___x_1370_: u32 = 0;
                        let mut v___x_1371_: u8 = 0;
                        v___x_1370_ = 102;
                        v___x_1371_ = lean_uint32_dec_eq(v_c_1359_, v___x_1370_);
                        if v___x_1371_ == 0 {
                            let mut v___x_1372_: u32 = 0;
                            let mut v___x_1373_: u8 = 0;
                            v___x_1372_ = 65;
                            v___x_1373_ = lean_uint32_dec_eq(v_c_1359_, v___x_1372_);
                            if v___x_1373_ == 0 {
                                let mut v___x_1374_: u32 = 0;
                                let mut v___x_1375_: u8 = 0;
                                v___x_1374_ = 66;
                                v___x_1375_ = lean_uint32_dec_eq(v_c_1359_, v___x_1374_);
                                if v___x_1375_ == 0 {
                                    let mut v___x_1376_: u32 = 0;
                                    let mut v___x_1377_: u8 = 0;
                                    v___x_1376_ = 67;
                                    v___x_1377_ = lean_uint32_dec_eq(v_c_1359_, v___x_1376_);
                                    if v___x_1377_ == 0 {
                                        let mut v___x_1378_: u32 = 0;
                                        let mut v___x_1379_: u8 = 0;
                                        v___x_1378_ = 68;
                                        v___x_1379_ = lean_uint32_dec_eq(v_c_1359_, v___x_1378_);
                                        if v___x_1379_ == 0 {
                                            let mut v___x_1380_: u32 = 0;
                                            let mut v___x_1381_: u8 = 0;
                                            v___x_1380_ = 69;
                                            v___x_1381_ =
                                                lean_uint32_dec_eq(v_c_1359_, v___x_1380_);
                                            if v___x_1381_ == 0 {
                                                let mut v___x_1382_: u32 = 0;
                                                let mut v___x_1383_: u8 = 0;
                                                v___x_1382_ = 70;
                                                v___x_1383_ =
                                                    lean_uint32_dec_eq(v_c_1359_, v___x_1382_);
                                                if v___x_1383_ == 0 {
                                                    let mut v___x_1384_: u32 = 0;
                                                    let mut v___x_1385_: u8 = 0;
                                                    v___x_1384_ = 48;
                                                    v___x_1385_ =
                                                        lean_uint32_dec_le(v___x_1384_, v_c_1359_);
                                                    if v___x_1385_ == 0 {
                                                        return v___x_1385_;
                                                    } else {
                                                        let mut v___x_1386_: u32 = 0;
                                                        let mut v___x_1387_: u8 = 0;
                                                        v___x_1386_ = 57;
                                                        v___x_1387_ = lean_uint32_dec_le(
                                                            v_c_1359_,
                                                            v___x_1386_,
                                                        );
                                                        return v___x_1387_;
                                                    }
                                                } else {
                                                    return v___x_1383_;
                                                }
                                            } else {
                                                return v___x_1381_;
                                            }
                                        } else {
                                            return v___x_1379_;
                                        }
                                    } else {
                                        return v___x_1377_;
                                    }
                                } else {
                                    return v___x_1375_;
                                }
                            } else {
                                return v___x_1373_;
                            }
                        } else {
                            return v___x_1371_;
                        }
                    } else {
                        return v___x_1369_;
                    }
                } else {
                    return v___x_1367_;
                }
            } else {
                return v___x_1365_;
            }
        } else {
            return v___x_1363_;
        }
    } else {
        return v___x_1361_;
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isHexDigit___boxed(
    mut v_c_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1389_: u32 = 0;
    let mut v_res_1390_: u8 = 0;
    let mut v_r_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1389_ = leanh::lean_unbox_uint32(v_c_1388_);
    leanh::lean_dec(v_c_1388_);
    v_res_1390_ = l_Std_Http_Internal_Char_isHexDigit(v_c_boxed_1389_);
    v_r_1391_ = leanh::lean_box((v_res_1390_) as usize);
    return v_r_1391_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__0() -> u8 {
    let mut v___x_1392_: u32 = 0;
    let mut v___x_1393_: u8 = 0;
    v___x_1392_ = 70;
    v___x_1393_ = lean_uint32_to_uint8(v___x_1392_);
    return v___x_1393_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__1() -> u8 {
    let mut v___x_1394_: u32 = 0;
    let mut v___x_1395_: u8 = 0;
    v___x_1394_ = 102;
    v___x_1395_ = lean_uint32_to_uint8(v___x_1394_);
    return v___x_1395_;
}
pub unsafe fn l_Std_Http_Internal_Char_isHexDigitByte(mut v_c_1396_: u8) -> u8 {
    let mut v___y_1398_: u8 = 0;
    let mut v___x_1399_: u8 = 0;
    let mut v___x_1400_: u8 = 0;
    let mut v___x_1401_: u8 = 0;
    let mut v___x_1402_: u8 = 0;
    let mut v___y_1404_: u8 = 0;
    let mut v___x_1405_: u8 = 0;
    let mut v___x_1406_: u8 = 0;
    let mut v___x_1407_: u8 = 0;
    let mut v___x_1408_: u8 = 0;
    let mut v___x_1409_: u8 = 0;
    let mut v___x_1410_: u8 = 0;
    let mut v___x_1411_: u8 = 0;
    let mut v___x_1412_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1409_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0_once),
                    _init_l_Std_Http_Internal_Char_isDigitByte___closed__0,
                );
                v___x_1410_ = lean_uint8_dec_le(v___x_1409_, v_c_1396_);
                if v___x_1410_ == 0 {
                    v___y_1404_ = v___x_1410_;
                    state = 2;
                    continue;
                } else {
                    v___x_1411_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isDigitByte___closed__1_once
                        ),
                        _init_l_Std_Http_Internal_Char_isDigitByte___closed__1,
                    );
                    v___x_1412_ = lean_uint8_dec_le(v_c_1396_, v___x_1411_);
                    v___y_1404_ = v___x_1412_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_1398_ == 0 {
                    v___x_1399_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2,
                    );
                    v___x_1400_ = lean_uint8_dec_le(v___x_1399_, v_c_1396_);
                    if v___x_1400_ == 0 {
                        return v___x_1400_;
                    } else {
                        v___x_1401_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isHexDigitByte___closed__0
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isHexDigitByte___closed__0_once
                            ),
                            _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__0,
                        );
                        v___x_1402_ = lean_uint8_dec_le(v_c_1396_, v___x_1401_);
                        return v___x_1402_;
                    }
                } else {
                    return v___y_1398_;
                }
            }
            2 => {
                if v___y_1404_ == 0 {
                    v___x_1405_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0,
                    );
                    v___x_1406_ = lean_uint8_dec_le(v___x_1405_, v_c_1396_);
                    if v___x_1406_ == 0 {
                        v___y_1398_ = v___x_1406_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1407_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isHexDigitByte___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isHexDigitByte___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isHexDigitByte___closed__1,
                        );
                        v___x_1408_ = lean_uint8_dec_le(v_c_1396_, v___x_1407_);
                        v___y_1398_ = v___x_1408_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1404_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isHexDigitByte___boxed(
    mut v_c_1413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1414_: u8 = 0;
    let mut v_res_1415_: u8 = 0;
    let mut v_r_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1414_ = (leanh::lean_unbox(v_c_1413_) as u8);
    v_res_1415_ = l_Std_Http_Internal_Char_isHexDigitByte(v_c_boxed_1414_);
    v_r_1416_ = leanh::lean_box((v_res_1415_) as usize);
    return v_r_1416_;
}
pub unsafe fn l_Std_Http_Internal_Char_isAlphaNum(mut v_c_1417_: u8) -> u8 {
    let mut v___y_1419_: u8 = 0;
    let mut v___x_1420_: u8 = 0;
    let mut v___x_1421_: u8 = 0;
    let mut v___x_1422_: u8 = 0;
    let mut v___x_1423_: u8 = 0;
    let mut v___y_1425_: u8 = 0;
    let mut v___x_1426_: u8 = 0;
    let mut v___x_1427_: u8 = 0;
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: u8 = 0;
    let mut v___x_1430_: u8 = 0;
    let mut v___x_1431_: u8 = 0;
    let mut v___x_1432_: u8 = 0;
    let mut v___x_1433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1430_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0_once),
                    _init_l_Std_Http_Internal_Char_isDigitByte___closed__0,
                );
                v___x_1431_ = lean_uint8_dec_le(v___x_1430_, v_c_1417_);
                if v___x_1431_ == 0 {
                    v___y_1425_ = v___x_1431_;
                    state = 2;
                    continue;
                } else {
                    v___x_1432_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isDigitByte___closed__1_once
                        ),
                        _init_l_Std_Http_Internal_Char_isDigitByte___closed__1,
                    );
                    v___x_1433_ = lean_uint8_dec_le(v_c_1417_, v___x_1432_);
                    v___y_1425_ = v___x_1433_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_1419_ == 0 {
                    v___x_1420_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2,
                    );
                    v___x_1421_ = lean_uint8_dec_le(v___x_1420_, v_c_1417_);
                    if v___x_1421_ == 0 {
                        return v___x_1421_;
                    } else {
                        v___x_1422_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3,
                        );
                        v___x_1423_ = lean_uint8_dec_le(v_c_1417_, v___x_1422_);
                        return v___x_1423_;
                    }
                } else {
                    return v___y_1419_;
                }
            }
            2 => {
                if v___y_1425_ == 0 {
                    v___x_1426_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0,
                    );
                    v___x_1427_ = lean_uint8_dec_le(v___x_1426_, v_c_1417_);
                    if v___x_1427_ == 0 {
                        v___y_1419_ = v___x_1427_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1428_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1,
                        );
                        v___x_1429_ = lean_uint8_dec_le(v_c_1417_, v___x_1428_);
                        v___y_1419_ = v___x_1429_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1425_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isAlphaNum___boxed(
    mut v_c_1434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1435_: u8 = 0;
    let mut v_res_1436_: u8 = 0;
    let mut v_r_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1435_ = (leanh::lean_unbox(v_c_1434_) as u8);
    v_res_1436_ = l_Std_Http_Internal_Char_isAlphaNum(v_c_boxed_1435_);
    v_r_1437_ = leanh::lean_box((v_res_1436_) as usize);
    return v_r_1437_;
}
pub unsafe fn l_Std_Http_Internal_Char_isAsciiAlphaNumChar(mut v_c_1438_: u32) -> u8 {
    let mut v___x_1440_: u32 = 0;
    let mut v___x_1441_: u8 = 0;
    let mut v___x_1442_: u32 = 0;
    let mut v___x_1443_: u8 = 0;
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: u8 = 0;
    let mut v___y_1448_: u8 = 0;
    let mut v___x_1449_: u32 = 0;
    let mut v___x_1450_: u8 = 0;
    let mut v___x_1451_: u32 = 0;
    let mut v___x_1452_: u8 = 0;
    let mut v___x_1453_: u32 = 0;
    let mut v___x_1454_: u8 = 0;
    let mut v___x_1455_: u32 = 0;
    let mut v___x_1456_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1444_ = lean_uint32_to_nat(v_c_1438_);
                v___x_1445_ = leanh::lean_unsigned_to_nat(128);
                v___x_1446_ = lean_nat_dec_lt(v___x_1444_, v___x_1445_);
                leanh::lean_dec(v___x_1444_);
                if v___x_1446_ == 0 {
                    return v___x_1446_;
                } else {
                    v___x_1453_ = 48;
                    v___x_1454_ = lean_uint32_dec_le(v___x_1453_, v_c_1438_);
                    if v___x_1454_ == 0 {
                        v___y_1448_ = v___x_1454_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1455_ = 57;
                        v___x_1456_ = lean_uint32_dec_le(v_c_1438_, v___x_1455_);
                        v___y_1448_ = v___x_1456_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1440_ = 97;
                v___x_1441_ = lean_uint32_dec_le(v___x_1440_, v_c_1438_);
                if v___x_1441_ == 0 {
                    return v___x_1441_;
                } else {
                    v___x_1442_ = 122;
                    v___x_1443_ = lean_uint32_dec_le(v_c_1438_, v___x_1442_);
                    return v___x_1443_;
                }
            }
            2 => {
                if v___y_1448_ == 0 {
                    v___x_1449_ = 65;
                    v___x_1450_ = lean_uint32_dec_le(v___x_1449_, v_c_1438_);
                    if v___x_1450_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1451_ = 90;
                        v___x_1452_ = lean_uint32_dec_le(v_c_1438_, v___x_1451_);
                        if v___x_1452_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_1446_;
                        }
                    }
                } else {
                    return v___y_1448_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isAsciiAlphaNumChar___boxed(
    mut v_c_1457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1458_: u32 = 0;
    let mut v_res_1459_: u8 = 0;
    let mut v_r_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1458_ = leanh::lean_unbox_uint32(v_c_1457_);
    leanh::lean_dec(v_c_1457_);
    v_res_1459_ = l_Std_Http_Internal_Char_isAsciiAlphaNumChar(v_c_boxed_1458_);
    v_r_1460_ = leanh::lean_box((v_res_1459_) as usize);
    return v_r_1460_;
}
pub unsafe fn l_Std_Http_Internal_Char_isValidSchemeChar(mut v_c_1461_: u32) -> u8 {
    let mut v___y_1463_: u8 = 0;
    let mut v___x_1464_: u32 = 0;
    let mut v___x_1465_: u8 = 0;
    let mut v___x_1466_: u32 = 0;
    let mut v___x_1467_: u8 = 0;
    let mut v___x_1468_: u32 = 0;
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1471_: u32 = 0;
    let mut v___x_1472_: u8 = 0;
    let mut v___x_1473_: u32 = 0;
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: u8 = 0;
    let mut v___y_1479_: u8 = 0;
    let mut v___x_1480_: u32 = 0;
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: u32 = 0;
    let mut v___x_1483_: u8 = 0;
    let mut v___x_1484_: u32 = 0;
    let mut v___x_1485_: u8 = 0;
    let mut v___x_1486_: u32 = 0;
    let mut v___x_1487_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1475_ = lean_uint32_to_nat(v_c_1461_);
                v___x_1476_ = leanh::lean_unsigned_to_nat(128);
                v___x_1477_ = lean_nat_dec_lt(v___x_1475_, v___x_1476_);
                leanh::lean_dec(v___x_1475_);
                if v___x_1477_ == 0 {
                    v___y_1463_ = v___x_1477_;
                    state = 1;
                    continue;
                } else {
                    v___x_1484_ = 48;
                    v___x_1485_ = lean_uint32_dec_le(v___x_1484_, v_c_1461_);
                    if v___x_1485_ == 0 {
                        v___y_1479_ = v___x_1485_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1486_ = 57;
                        v___x_1487_ = lean_uint32_dec_le(v_c_1461_, v___x_1486_);
                        v___y_1479_ = v___x_1487_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1463_ == 0 {
                    v___x_1464_ = 43;
                    v___x_1465_ = lean_uint32_dec_eq(v_c_1461_, v___x_1464_);
                    if v___x_1465_ == 0 {
                        v___x_1466_ = 45;
                        v___x_1467_ = lean_uint32_dec_eq(v_c_1461_, v___x_1466_);
                        if v___x_1467_ == 0 {
                            v___x_1468_ = 46;
                            v___x_1469_ = lean_uint32_dec_eq(v_c_1461_, v___x_1468_);
                            if v___x_1469_ == 0 {
                                return v___y_1463_;
                            } else {
                                return v___x_1469_;
                            }
                        } else {
                            return v___x_1467_;
                        }
                    } else {
                        return v___x_1465_;
                    }
                } else {
                    return v___y_1463_;
                }
            }
            2 => {
                v___x_1471_ = 97;
                v___x_1472_ = lean_uint32_dec_le(v___x_1471_, v_c_1461_);
                if v___x_1472_ == 0 {
                    v___y_1463_ = v___x_1472_;
                    state = 1;
                    continue;
                } else {
                    v___x_1473_ = 122;
                    v___x_1474_ = lean_uint32_dec_le(v_c_1461_, v___x_1473_);
                    v___y_1463_ = v___x_1474_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1479_ == 0 {
                    v___x_1480_ = 65;
                    v___x_1481_ = lean_uint32_dec_le(v___x_1480_, v_c_1461_);
                    if v___x_1481_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_1482_ = 90;
                        v___x_1483_ = lean_uint32_dec_le(v_c_1461_, v___x_1482_);
                        if v___x_1483_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_1463_ = v___x_1477_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___y_1479_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isValidSchemeChar___boxed(
    mut v_c_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1489_: u32 = 0;
    let mut v_res_1490_: u8 = 0;
    let mut v_r_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1489_ = leanh::lean_unbox_uint32(v_c_1488_);
    leanh::lean_dec(v_c_1488_);
    v_res_1490_ = l_Std_Http_Internal_Char_isValidSchemeChar(v_c_boxed_1489_);
    v_r_1491_ = leanh::lean_box((v_res_1490_) as usize);
    return v_r_1491_;
}
pub unsafe fn l_Std_Http_Internal_Char_isValidDomainNameChar(mut v_c_1492_: u32) -> u8 {
    let mut v___y_1494_: u8 = 0;
    let mut v___x_1495_: u32 = 0;
    let mut v___x_1496_: u8 = 0;
    let mut v___x_1497_: u32 = 0;
    let mut v___x_1498_: u8 = 0;
    let mut v___x_1500_: u32 = 0;
    let mut v___x_1501_: u8 = 0;
    let mut v___x_1502_: u32 = 0;
    let mut v___x_1503_: u8 = 0;
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___y_1508_: u8 = 0;
    let mut v___x_1509_: u32 = 0;
    let mut v___x_1510_: u8 = 0;
    let mut v___x_1511_: u32 = 0;
    let mut v___x_1512_: u8 = 0;
    let mut v___x_1513_: u32 = 0;
    let mut v___x_1514_: u8 = 0;
    let mut v___x_1515_: u32 = 0;
    let mut v___x_1516_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1504_ = lean_uint32_to_nat(v_c_1492_);
                v___x_1505_ = leanh::lean_unsigned_to_nat(128);
                v___x_1506_ = lean_nat_dec_lt(v___x_1504_, v___x_1505_);
                leanh::lean_dec(v___x_1504_);
                if v___x_1506_ == 0 {
                    v___y_1494_ = v___x_1506_;
                    state = 1;
                    continue;
                } else {
                    v___x_1513_ = 48;
                    v___x_1514_ = lean_uint32_dec_le(v___x_1513_, v_c_1492_);
                    if v___x_1514_ == 0 {
                        v___y_1508_ = v___x_1514_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1515_ = 57;
                        v___x_1516_ = lean_uint32_dec_le(v_c_1492_, v___x_1515_);
                        v___y_1508_ = v___x_1516_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1494_ == 0 {
                    v___x_1495_ = 45;
                    v___x_1496_ = lean_uint32_dec_eq(v_c_1492_, v___x_1495_);
                    if v___x_1496_ == 0 {
                        v___x_1497_ = 46;
                        v___x_1498_ = lean_uint32_dec_eq(v_c_1492_, v___x_1497_);
                        if v___x_1498_ == 0 {
                            return v___y_1494_;
                        } else {
                            return v___x_1498_;
                        }
                    } else {
                        return v___x_1496_;
                    }
                } else {
                    return v___y_1494_;
                }
            }
            2 => {
                v___x_1500_ = 97;
                v___x_1501_ = lean_uint32_dec_le(v___x_1500_, v_c_1492_);
                if v___x_1501_ == 0 {
                    v___y_1494_ = v___x_1501_;
                    state = 1;
                    continue;
                } else {
                    v___x_1502_ = 122;
                    v___x_1503_ = lean_uint32_dec_le(v_c_1492_, v___x_1502_);
                    v___y_1494_ = v___x_1503_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1508_ == 0 {
                    v___x_1509_ = 65;
                    v___x_1510_ = lean_uint32_dec_le(v___x_1509_, v_c_1492_);
                    if v___x_1510_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_1511_ = 90;
                        v___x_1512_ = lean_uint32_dec_le(v_c_1492_, v___x_1511_);
                        if v___x_1512_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___y_1494_ = v___x_1506_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v___y_1508_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isValidDomainNameChar___boxed(
    mut v_c_1517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1518_: u32 = 0;
    let mut v_res_1519_: u8 = 0;
    let mut v_r_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1518_ = leanh::lean_unbox_uint32(v_c_1517_);
    leanh::lean_dec(v_c_1517_);
    v_res_1519_ = l_Std_Http_Internal_Char_isValidDomainNameChar(v_c_boxed_1518_);
    v_r_1520_ = leanh::lean_box((v_res_1519_) as usize);
    return v_r_1520_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isUnreserved___closed__0() -> u8 {
    let mut v___x_1521_: u32 = 0;
    let mut v___x_1522_: u8 = 0;
    v___x_1521_ = 95;
    v___x_1522_ = lean_uint32_to_uint8(v___x_1521_);
    return v___x_1522_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isUnreserved___closed__1() -> u8 {
    let mut v___x_1523_: u32 = 0;
    let mut v___x_1524_: u8 = 0;
    v___x_1523_ = 126;
    v___x_1524_ = lean_uint32_to_uint8(v___x_1523_);
    return v___x_1524_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isUnreserved___closed__2() -> u8 {
    let mut v___x_1525_: u32 = 0;
    let mut v___x_1526_: u8 = 0;
    v___x_1525_ = 45;
    v___x_1526_ = lean_uint32_to_uint8(v___x_1525_);
    return v___x_1526_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isUnreserved___closed__3() -> u8 {
    let mut v___x_1527_: u32 = 0;
    let mut v___x_1528_: u8 = 0;
    v___x_1527_ = 46;
    v___x_1528_ = lean_uint32_to_uint8(v___x_1527_);
    return v___x_1528_;
}
pub unsafe fn l_Std_Http_Internal_Char_isUnreserved(mut v_c_1529_: u8) -> u8 {
    let mut v___y_1531_: u8 = 0;
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: u8 = 0;
    let mut v___x_1534_: u8 = 0;
    let mut v___x_1535_: u8 = 0;
    let mut v___y_1537_: u8 = 0;
    let mut v___x_1538_: u8 = 0;
    let mut v___x_1539_: u8 = 0;
    let mut v___x_1540_: u8 = 0;
    let mut v___x_1541_: u8 = 0;
    let mut v___y_1543_: u8 = 0;
    let mut v___x_1544_: u8 = 0;
    let mut v___x_1545_: u8 = 0;
    let mut v___x_1546_: u8 = 0;
    let mut v___x_1547_: u8 = 0;
    let mut v___y_1549_: u8 = 0;
    let mut v___x_1550_: u8 = 0;
    let mut v___x_1551_: u8 = 0;
    let mut v___x_1552_: u8 = 0;
    let mut v___x_1553_: u8 = 0;
    let mut v___x_1554_: u8 = 0;
    let mut v___x_1555_: u8 = 0;
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1557_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1554_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0_once),
                    _init_l_Std_Http_Internal_Char_isDigitByte___closed__0,
                );
                v___x_1555_ = lean_uint8_dec_le(v___x_1554_, v_c_1529_);
                if v___x_1555_ == 0 {
                    v___y_1549_ = v___x_1555_;
                    state = 4;
                    continue;
                } else {
                    v___x_1556_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isDigitByte___closed__1_once
                        ),
                        _init_l_Std_Http_Internal_Char_isDigitByte___closed__1,
                    );
                    v___x_1557_ = lean_uint8_dec_le(v_c_1529_, v___x_1556_);
                    v___y_1549_ = v___x_1557_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                if v___y_1531_ == 0 {
                    v___x_1532_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__0,
                    );
                    v___x_1533_ = lean_uint8_dec_eq(v_c_1529_, v___x_1532_);
                    if v___x_1533_ == 0 {
                        v___x_1534_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__1,
                        );
                        v___x_1535_ = lean_uint8_dec_eq(v_c_1529_, v___x_1534_);
                        return v___x_1535_;
                    } else {
                        return v___x_1533_;
                    }
                } else {
                    return v___y_1531_;
                }
            }
            2 => {
                if v___y_1537_ == 0 {
                    v___x_1538_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__2,
                    );
                    v___x_1539_ = lean_uint8_dec_eq(v_c_1529_, v___x_1538_);
                    if v___x_1539_ == 0 {
                        v___x_1540_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__3,
                        );
                        v___x_1541_ = lean_uint8_dec_eq(v_c_1529_, v___x_1540_);
                        v___y_1531_ = v___x_1541_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1531_ = v___x_1539_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1537_;
                }
            }
            3 => {
                if v___y_1543_ == 0 {
                    v___x_1544_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2,
                    );
                    v___x_1545_ = lean_uint8_dec_le(v___x_1544_, v_c_1529_);
                    if v___x_1545_ == 0 {
                        v___y_1537_ = v___x_1545_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1546_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3,
                        );
                        v___x_1547_ = lean_uint8_dec_le(v_c_1529_, v___x_1546_);
                        v___y_1537_ = v___x_1547_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_1543_;
                }
            }
            4 => {
                if v___y_1549_ == 0 {
                    v___x_1550_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0,
                    );
                    v___x_1551_ = lean_uint8_dec_le(v___x_1550_, v_c_1529_);
                    if v___x_1551_ == 0 {
                        v___y_1543_ = v___x_1551_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1552_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1,
                        );
                        v___x_1553_ = lean_uint8_dec_le(v_c_1529_, v___x_1552_);
                        v___y_1543_ = v___x_1553_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_1549_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isUnreserved___boxed(
    mut v_c_1558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1559_: u8 = 0;
    let mut v_res_1560_: u8 = 0;
    let mut v_r_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1559_ = (leanh::lean_unbox(v_c_1558_) as u8);
    v_res_1560_ = l_Std_Http_Internal_Char_isUnreserved(v_c_boxed_1559_);
    v_r_1561_ = leanh::lean_box((v_res_1560_) as usize);
    return v_r_1561_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__0() -> u8 {
    let mut v___x_1562_: u32 = 0;
    let mut v___x_1563_: u8 = 0;
    v___x_1562_ = 38;
    v___x_1563_ = lean_uint32_to_uint8(v___x_1562_);
    return v___x_1563_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__1() -> u8 {
    let mut v___x_1564_: u32 = 0;
    let mut v___x_1565_: u8 = 0;
    v___x_1564_ = 39;
    v___x_1565_ = lean_uint32_to_uint8(v___x_1564_);
    return v___x_1565_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__2() -> u8 {
    let mut v___x_1566_: u32 = 0;
    let mut v___x_1567_: u8 = 0;
    v___x_1566_ = 40;
    v___x_1567_ = lean_uint32_to_uint8(v___x_1566_);
    return v___x_1567_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__3() -> u8 {
    let mut v___x_1568_: u32 = 0;
    let mut v___x_1569_: u8 = 0;
    v___x_1568_ = 41;
    v___x_1569_ = lean_uint32_to_uint8(v___x_1568_);
    return v___x_1569_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__4() -> u8 {
    let mut v___x_1570_: u32 = 0;
    let mut v___x_1571_: u8 = 0;
    v___x_1570_ = 42;
    v___x_1571_ = lean_uint32_to_uint8(v___x_1570_);
    return v___x_1571_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__5() -> u8 {
    let mut v___x_1572_: u32 = 0;
    let mut v___x_1573_: u8 = 0;
    v___x_1572_ = 43;
    v___x_1573_ = lean_uint32_to_uint8(v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__6() -> u8 {
    let mut v___x_1574_: u32 = 0;
    let mut v___x_1575_: u8 = 0;
    v___x_1574_ = 44;
    v___x_1575_ = lean_uint32_to_uint8(v___x_1574_);
    return v___x_1575_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__7() -> u8 {
    let mut v___x_1576_: u32 = 0;
    let mut v___x_1577_: u8 = 0;
    v___x_1576_ = 59;
    v___x_1577_ = lean_uint32_to_uint8(v___x_1576_);
    return v___x_1577_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__8() -> u8 {
    let mut v___x_1578_: u32 = 0;
    let mut v___x_1579_: u8 = 0;
    v___x_1578_ = 61;
    v___x_1579_ = lean_uint32_to_uint8(v___x_1578_);
    return v___x_1579_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__9() -> u8 {
    let mut v___x_1580_: u32 = 0;
    let mut v___x_1581_: u8 = 0;
    v___x_1580_ = 33;
    v___x_1581_ = lean_uint32_to_uint8(v___x_1580_);
    return v___x_1581_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isSubDelims___closed__10() -> u8 {
    let mut v___x_1582_: u32 = 0;
    let mut v___x_1583_: u8 = 0;
    v___x_1582_ = 36;
    v___x_1583_ = lean_uint32_to_uint8(v___x_1582_);
    return v___x_1583_;
}
pub unsafe fn l_Std_Http_Internal_Char_isSubDelims(mut v_c_1584_: u8) -> u8 {
    let mut v___y_1586_: u8 = 0;
    let mut v___x_1587_: u8 = 0;
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1589_: u8 = 0;
    let mut v___x_1590_: u8 = 0;
    let mut v___x_1591_: u8 = 0;
    let mut v___x_1592_: u8 = 0;
    let mut v___x_1593_: u8 = 0;
    let mut v___x_1594_: u8 = 0;
    let mut v___x_1595_: u8 = 0;
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: u8 = 0;
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: u8 = 0;
    let mut v___x_1600_: u8 = 0;
    let mut v___x_1601_: u8 = 0;
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: u8 = 0;
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: u8 = 0;
    let mut v___x_1607_: u8 = 0;
    let mut v___x_1608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1605_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__9),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__9_once),
                    _init_l_Std_Http_Internal_Char_isSubDelims___closed__9,
                );
                v___x_1606_ = lean_uint8_dec_eq(v_c_1584_, v___x_1605_);
                if v___x_1606_ == 0 {
                    v___x_1607_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__10),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__10_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__10,
                    );
                    v___x_1608_ = lean_uint8_dec_eq(v_c_1584_, v___x_1607_);
                    v___y_1586_ = v___x_1608_;
                    state = 1;
                    continue;
                } else {
                    v___y_1586_ = v___x_1606_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_1586_ == 0 {
                    v___x_1587_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__0,
                    );
                    v___x_1588_ = lean_uint8_dec_eq(v_c_1584_, v___x_1587_);
                    if v___x_1588_ == 0 {
                        v___x_1589_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__1,
                        );
                        v___x_1590_ = lean_uint8_dec_eq(v_c_1584_, v___x_1589_);
                        if v___x_1590_ == 0 {
                            v___x_1591_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2_once
                                ),
                                _init_l_Std_Http_Internal_Char_isSubDelims___closed__2,
                            );
                            v___x_1592_ = lean_uint8_dec_eq(v_c_1584_, v___x_1591_);
                            if v___x_1592_ == 0 {
                                v___x_1593_ = leanh::lean_uint8_once(
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3_once
                                    ),
                                    _init_l_Std_Http_Internal_Char_isSubDelims___closed__3,
                                );
                                v___x_1594_ = lean_uint8_dec_eq(v_c_1584_, v___x_1593_);
                                if v___x_1594_ == 0 {
                                    v___x_1595_ = leanh::lean_uint8_once(
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4_once
                                        ),
                                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__4,
                                    );
                                    v___x_1596_ = lean_uint8_dec_eq(v_c_1584_, v___x_1595_);
                                    if v___x_1596_ == 0 {
                                        v___x_1597_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
                                        v___x_1598_ = lean_uint8_dec_eq(v_c_1584_, v___x_1597_);
                                        if v___x_1598_ == 0 {
                                            v___x_1599_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
                                            v___x_1600_ = lean_uint8_dec_eq(v_c_1584_, v___x_1599_);
                                            if v___x_1600_ == 0 {
                                                v___x_1601_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
                                                v___x_1602_ =
                                                    lean_uint8_dec_eq(v_c_1584_, v___x_1601_);
                                                if v___x_1602_ == 0 {
                                                    v___x_1603_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
                                                    v___x_1604_ =
                                                        lean_uint8_dec_eq(v_c_1584_, v___x_1603_);
                                                    return v___x_1604_;
                                                } else {
                                                    return v___x_1602_;
                                                }
                                            } else {
                                                return v___x_1600_;
                                            }
                                        } else {
                                            return v___x_1598_;
                                        }
                                    } else {
                                        return v___x_1596_;
                                    }
                                } else {
                                    return v___x_1594_;
                                }
                            } else {
                                return v___x_1592_;
                            }
                        } else {
                            return v___x_1590_;
                        }
                    } else {
                        return v___x_1588_;
                    }
                } else {
                    return v___y_1586_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isSubDelims___boxed(
    mut v_c_1609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1610_: u8 = 0;
    let mut v_res_1611_: u8 = 0;
    let mut v_r_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1610_ = (leanh::lean_unbox(v_c_1609_) as u8);
    v_res_1611_ = l_Std_Http_Internal_Char_isSubDelims(v_c_boxed_1610_);
    v_r_1612_ = leanh::lean_box((v_res_1611_) as usize);
    return v_r_1612_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isPChar___closed__0() -> u8 {
    let mut v___x_1613_: u32 = 0;
    let mut v___x_1614_: u8 = 0;
    v___x_1613_ = 58;
    v___x_1614_ = lean_uint32_to_uint8(v___x_1613_);
    return v___x_1614_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isPChar___closed__1() -> u8 {
    let mut v___x_1615_: u32 = 0;
    let mut v___x_1616_: u8 = 0;
    v___x_1615_ = 64;
    v___x_1616_ = lean_uint32_to_uint8(v___x_1615_);
    return v___x_1616_;
}
pub unsafe fn l_Std_Http_Internal_Char_isPChar(mut v_c_1617_: u8) -> u8 {
    let mut v___y_1619_: u8 = 0;
    let mut v___x_1620_: u8 = 0;
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: u8 = 0;
    let mut v___x_1623_: u8 = 0;
    let mut v___y_1625_: u8 = 0;
    let mut v___x_1626_: u8 = 0;
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1628_: u8 = 0;
    let mut v___x_1629_: u8 = 0;
    let mut v___x_1630_: u8 = 0;
    let mut v___x_1631_: u8 = 0;
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: u8 = 0;
    let mut v___x_1634_: u8 = 0;
    let mut v___x_1635_: u8 = 0;
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: u8 = 0;
    let mut v___x_1639_: u8 = 0;
    let mut v___x_1640_: u8 = 0;
    let mut v___x_1641_: u8 = 0;
    let mut v___x_1642_: u8 = 0;
    let mut v___x_1643_: u8 = 0;
    let mut v___y_1645_: u8 = 0;
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: u8 = 0;
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: u8 = 0;
    let mut v___y_1651_: u8 = 0;
    let mut v___x_1652_: u8 = 0;
    let mut v___x_1653_: u8 = 0;
    let mut v___x_1654_: u8 = 0;
    let mut v___x_1655_: u8 = 0;
    let mut v___y_1657_: u8 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: u8 = 0;
    let mut v___x_1660_: u8 = 0;
    let mut v___x_1661_: u8 = 0;
    let mut v___y_1663_: u8 = 0;
    let mut v___x_1664_: u8 = 0;
    let mut v___x_1665_: u8 = 0;
    let mut v___x_1666_: u8 = 0;
    let mut v___x_1667_: u8 = 0;
    let mut v___y_1669_: u8 = 0;
    let mut v___x_1670_: u8 = 0;
    let mut v___x_1671_: u8 = 0;
    let mut v___x_1672_: u8 = 0;
    let mut v___x_1673_: u8 = 0;
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1674_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0_once),
                    _init_l_Std_Http_Internal_Char_isDigitByte___closed__0,
                );
                v___x_1675_ = lean_uint8_dec_le(v___x_1674_, v_c_1617_);
                if v___x_1675_ == 0 {
                    v___y_1669_ = v___x_1675_;
                    state = 7;
                    continue;
                } else {
                    v___x_1676_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isDigitByte___closed__1_once
                        ),
                        _init_l_Std_Http_Internal_Char_isDigitByte___closed__1,
                    );
                    v___x_1677_ = lean_uint8_dec_le(v_c_1617_, v___x_1676_);
                    v___y_1669_ = v___x_1677_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                if v___y_1619_ == 0 {
                    v___x_1620_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0_once),
                        _init_l_Std_Http_Internal_Char_isPChar___closed__0,
                    );
                    v___x_1621_ = lean_uint8_dec_eq(v_c_1617_, v___x_1620_);
                    if v___x_1621_ == 0 {
                        v___x_1622_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isPChar___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isPChar___closed__1,
                        );
                        v___x_1623_ = lean_uint8_dec_eq(v_c_1617_, v___x_1622_);
                        return v___x_1623_;
                    } else {
                        return v___x_1621_;
                    }
                } else {
                    return v___y_1619_;
                }
            }
            2 => {
                if v___y_1625_ == 0 {
                    v___x_1626_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__0,
                    );
                    v___x_1627_ = lean_uint8_dec_eq(v_c_1617_, v___x_1626_);
                    if v___x_1627_ == 0 {
                        v___x_1628_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__1,
                        );
                        v___x_1629_ = lean_uint8_dec_eq(v_c_1617_, v___x_1628_);
                        if v___x_1629_ == 0 {
                            v___x_1630_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2_once
                                ),
                                _init_l_Std_Http_Internal_Char_isSubDelims___closed__2,
                            );
                            v___x_1631_ = lean_uint8_dec_eq(v_c_1617_, v___x_1630_);
                            if v___x_1631_ == 0 {
                                v___x_1632_ = leanh::lean_uint8_once(
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3_once
                                    ),
                                    _init_l_Std_Http_Internal_Char_isSubDelims___closed__3,
                                );
                                v___x_1633_ = lean_uint8_dec_eq(v_c_1617_, v___x_1632_);
                                if v___x_1633_ == 0 {
                                    v___x_1634_ = leanh::lean_uint8_once(
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4_once
                                        ),
                                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__4,
                                    );
                                    v___x_1635_ = lean_uint8_dec_eq(v_c_1617_, v___x_1634_);
                                    if v___x_1635_ == 0 {
                                        v___x_1636_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
                                        v___x_1637_ = lean_uint8_dec_eq(v_c_1617_, v___x_1636_);
                                        if v___x_1637_ == 0 {
                                            v___x_1638_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
                                            v___x_1639_ = lean_uint8_dec_eq(v_c_1617_, v___x_1638_);
                                            if v___x_1639_ == 0 {
                                                v___x_1640_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
                                                v___x_1641_ =
                                                    lean_uint8_dec_eq(v_c_1617_, v___x_1640_);
                                                if v___x_1641_ == 0 {
                                                    v___x_1642_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
                                                    v___x_1643_ =
                                                        lean_uint8_dec_eq(v_c_1617_, v___x_1642_);
                                                    v___y_1619_ = v___x_1643_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___y_1619_ = v___x_1641_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___y_1619_ = v___x_1639_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___y_1619_ = v___x_1637_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___y_1619_ = v___x_1635_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_1619_ = v___x_1633_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_1619_ = v___x_1631_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_1619_ = v___x_1629_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_1619_ = v___x_1627_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1625_;
                }
            }
            3 => {
                if v___y_1645_ == 0 {
                    v___x_1646_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__9_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__9,
                    );
                    v___x_1647_ = lean_uint8_dec_eq(v_c_1617_, v___x_1646_);
                    if v___x_1647_ == 0 {
                        v___x_1648_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__10,
                        );
                        v___x_1649_ = lean_uint8_dec_eq(v_c_1617_, v___x_1648_);
                        v___y_1625_ = v___x_1649_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1625_ = v___x_1647_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_1645_;
                }
            }
            4 => {
                if v___y_1651_ == 0 {
                    v___x_1652_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__0,
                    );
                    v___x_1653_ = lean_uint8_dec_eq(v_c_1617_, v___x_1652_);
                    if v___x_1653_ == 0 {
                        v___x_1654_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__1,
                        );
                        v___x_1655_ = lean_uint8_dec_eq(v_c_1617_, v___x_1654_);
                        v___y_1645_ = v___x_1655_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1645_ = v___x_1653_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_1651_;
                }
            }
            5 => {
                if v___y_1657_ == 0 {
                    v___x_1658_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__2,
                    );
                    v___x_1659_ = lean_uint8_dec_eq(v_c_1617_, v___x_1658_);
                    if v___x_1659_ == 0 {
                        v___x_1660_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__3,
                        );
                        v___x_1661_ = lean_uint8_dec_eq(v_c_1617_, v___x_1660_);
                        v___y_1651_ = v___x_1661_;
                        state = 4;
                        continue;
                    } else {
                        v___y_1651_ = v___x_1659_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_1657_;
                }
            }
            6 => {
                if v___y_1663_ == 0 {
                    v___x_1664_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2,
                    );
                    v___x_1665_ = lean_uint8_dec_le(v___x_1664_, v_c_1617_);
                    if v___x_1665_ == 0 {
                        v___y_1657_ = v___x_1665_;
                        state = 5;
                        continue;
                    } else {
                        v___x_1666_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3,
                        );
                        v___x_1667_ = lean_uint8_dec_le(v_c_1617_, v___x_1666_);
                        v___y_1657_ = v___x_1667_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_1663_;
                }
            }
            7 => {
                if v___y_1669_ == 0 {
                    v___x_1670_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0,
                    );
                    v___x_1671_ = lean_uint8_dec_le(v___x_1670_, v_c_1617_);
                    if v___x_1671_ == 0 {
                        v___y_1663_ = v___x_1671_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1672_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1,
                        );
                        v___x_1673_ = lean_uint8_dec_le(v_c_1617_, v___x_1672_);
                        v___y_1663_ = v___x_1673_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_1669_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isPChar___boxed(
    mut v_c_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1679_: u8 = 0;
    let mut v_res_1680_: u8 = 0;
    let mut v_r_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1679_ = (leanh::lean_unbox(v_c_1678_) as u8);
    v_res_1680_ = l_Std_Http_Internal_Char_isPChar(v_c_boxed_1679_);
    v_r_1681_ = leanh::lean_box((v_res_1680_) as usize);
    return v_r_1681_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isQueryChar___closed__0() -> u8 {
    let mut v___x_1682_: u32 = 0;
    let mut v___x_1683_: u8 = 0;
    v___x_1682_ = 47;
    v___x_1683_ = lean_uint32_to_uint8(v___x_1682_);
    return v___x_1683_;
}
pub unsafe fn _init_l_Std_Http_Internal_Char_isQueryChar___closed__1() -> u8 {
    let mut v___x_1684_: u32 = 0;
    let mut v___x_1685_: u8 = 0;
    v___x_1684_ = 63;
    v___x_1685_ = lean_uint32_to_uint8(v___x_1684_);
    return v___x_1685_;
}
pub unsafe fn l_Std_Http_Internal_Char_isQueryChar(mut v_c_1686_: u8) -> u8 {
    let mut v___y_1688_: u8 = 0;
    let mut v___x_1689_: u8 = 0;
    let mut v___x_1690_: u8 = 0;
    let mut v___x_1691_: u8 = 0;
    let mut v___x_1692_: u8 = 0;
    let mut v___y_1694_: u8 = 0;
    let mut v___x_1695_: u8 = 0;
    let mut v___x_1696_: u8 = 0;
    let mut v___x_1697_: u8 = 0;
    let mut v___x_1698_: u8 = 0;
    let mut v___y_1700_: u8 = 0;
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: u8 = 0;
    let mut v___x_1703_: u8 = 0;
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: u8 = 0;
    let mut v___x_1706_: u8 = 0;
    let mut v___x_1707_: u8 = 0;
    let mut v___x_1708_: u8 = 0;
    let mut v___x_1709_: u8 = 0;
    let mut v___x_1710_: u8 = 0;
    let mut v___x_1711_: u8 = 0;
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: u8 = 0;
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: u8 = 0;
    let mut v___x_1716_: u8 = 0;
    let mut v___x_1717_: u8 = 0;
    let mut v___x_1718_: u8 = 0;
    let mut v___y_1720_: u8 = 0;
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: u8 = 0;
    let mut v___x_1724_: u8 = 0;
    let mut v___y_1726_: u8 = 0;
    let mut v___x_1727_: u8 = 0;
    let mut v___x_1728_: u8 = 0;
    let mut v___x_1729_: u8 = 0;
    let mut v___x_1730_: u8 = 0;
    let mut v___y_1732_: u8 = 0;
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: u8 = 0;
    let mut v___x_1735_: u8 = 0;
    let mut v___x_1736_: u8 = 0;
    let mut v___y_1738_: u8 = 0;
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1740_: u8 = 0;
    let mut v___x_1741_: u8 = 0;
    let mut v___x_1742_: u8 = 0;
    let mut v___y_1744_: u8 = 0;
    let mut v___x_1745_: u8 = 0;
    let mut v___x_1746_: u8 = 0;
    let mut v___x_1747_: u8 = 0;
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: u8 = 0;
    let mut v___x_1750_: u8 = 0;
    let mut v___x_1751_: u8 = 0;
    let mut v___x_1752_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1749_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0_once),
                    _init_l_Std_Http_Internal_Char_isDigitByte___closed__0,
                );
                v___x_1750_ = lean_uint8_dec_le(v___x_1749_, v_c_1686_);
                if v___x_1750_ == 0 {
                    v___y_1744_ = v___x_1750_;
                    state = 8;
                    continue;
                } else {
                    v___x_1751_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isDigitByte___closed__1_once
                        ),
                        _init_l_Std_Http_Internal_Char_isDigitByte___closed__1,
                    );
                    v___x_1752_ = lean_uint8_dec_le(v_c_1686_, v___x_1751_);
                    v___y_1744_ = v___x_1752_;
                    state = 8;
                    continue;
                }
            }
            1 => {
                if v___y_1688_ == 0 {
                    v___x_1689_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isQueryChar___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isQueryChar___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isQueryChar___closed__0,
                    );
                    v___x_1690_ = lean_uint8_dec_eq(v_c_1686_, v___x_1689_);
                    if v___x_1690_ == 0 {
                        v___x_1691_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isQueryChar___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isQueryChar___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isQueryChar___closed__1,
                        );
                        v___x_1692_ = lean_uint8_dec_eq(v_c_1686_, v___x_1691_);
                        return v___x_1692_;
                    } else {
                        return v___x_1690_;
                    }
                } else {
                    return v___y_1688_;
                }
            }
            2 => {
                if v___y_1694_ == 0 {
                    v___x_1695_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0_once),
                        _init_l_Std_Http_Internal_Char_isPChar___closed__0,
                    );
                    v___x_1696_ = lean_uint8_dec_eq(v_c_1686_, v___x_1695_);
                    if v___x_1696_ == 0 {
                        v___x_1697_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isPChar___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isPChar___closed__1,
                        );
                        v___x_1698_ = lean_uint8_dec_eq(v_c_1686_, v___x_1697_);
                        v___y_1688_ = v___x_1698_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1688_ = v___x_1696_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1694_;
                }
            }
            3 => {
                if v___y_1700_ == 0 {
                    v___x_1701_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__0,
                    );
                    v___x_1702_ = lean_uint8_dec_eq(v_c_1686_, v___x_1701_);
                    if v___x_1702_ == 0 {
                        v___x_1703_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__1,
                        );
                        v___x_1704_ = lean_uint8_dec_eq(v_c_1686_, v___x_1703_);
                        if v___x_1704_ == 0 {
                            v___x_1705_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2_once
                                ),
                                _init_l_Std_Http_Internal_Char_isSubDelims___closed__2,
                            );
                            v___x_1706_ = lean_uint8_dec_eq(v_c_1686_, v___x_1705_);
                            if v___x_1706_ == 0 {
                                v___x_1707_ = leanh::lean_uint8_once(
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3_once
                                    ),
                                    _init_l_Std_Http_Internal_Char_isSubDelims___closed__3,
                                );
                                v___x_1708_ = lean_uint8_dec_eq(v_c_1686_, v___x_1707_);
                                if v___x_1708_ == 0 {
                                    v___x_1709_ = leanh::lean_uint8_once(
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4_once
                                        ),
                                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__4,
                                    );
                                    v___x_1710_ = lean_uint8_dec_eq(v_c_1686_, v___x_1709_);
                                    if v___x_1710_ == 0 {
                                        v___x_1711_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
                                        v___x_1712_ = lean_uint8_dec_eq(v_c_1686_, v___x_1711_);
                                        if v___x_1712_ == 0 {
                                            v___x_1713_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
                                            v___x_1714_ = lean_uint8_dec_eq(v_c_1686_, v___x_1713_);
                                            if v___x_1714_ == 0 {
                                                v___x_1715_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
                                                v___x_1716_ =
                                                    lean_uint8_dec_eq(v_c_1686_, v___x_1715_);
                                                if v___x_1716_ == 0 {
                                                    v___x_1717_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
                                                    v___x_1718_ =
                                                        lean_uint8_dec_eq(v_c_1686_, v___x_1717_);
                                                    v___y_1694_ = v___x_1718_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___y_1694_ = v___x_1716_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                v___y_1694_ = v___x_1714_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            v___y_1694_ = v___x_1712_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v___y_1694_ = v___x_1710_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_1694_ = v___x_1708_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___y_1694_ = v___x_1706_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_1694_ = v___x_1704_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_1694_ = v___x_1702_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_1700_;
                }
            }
            4 => {
                if v___y_1720_ == 0 {
                    v___x_1721_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__9_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__9,
                    );
                    v___x_1722_ = lean_uint8_dec_eq(v_c_1686_, v___x_1721_);
                    if v___x_1722_ == 0 {
                        v___x_1723_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__10,
                        );
                        v___x_1724_ = lean_uint8_dec_eq(v_c_1686_, v___x_1723_);
                        v___y_1700_ = v___x_1724_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1700_ = v___x_1722_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_1720_;
                }
            }
            5 => {
                if v___y_1726_ == 0 {
                    v___x_1727_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__0,
                    );
                    v___x_1728_ = lean_uint8_dec_eq(v_c_1686_, v___x_1727_);
                    if v___x_1728_ == 0 {
                        v___x_1729_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__1,
                        );
                        v___x_1730_ = lean_uint8_dec_eq(v_c_1686_, v___x_1729_);
                        v___y_1720_ = v___x_1730_;
                        state = 4;
                        continue;
                    } else {
                        v___y_1720_ = v___x_1728_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_1726_;
                }
            }
            6 => {
                if v___y_1732_ == 0 {
                    v___x_1733_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__2,
                    );
                    v___x_1734_ = lean_uint8_dec_eq(v_c_1686_, v___x_1733_);
                    if v___x_1734_ == 0 {
                        v___x_1735_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__3,
                        );
                        v___x_1736_ = lean_uint8_dec_eq(v_c_1686_, v___x_1735_);
                        v___y_1726_ = v___x_1736_;
                        state = 5;
                        continue;
                    } else {
                        v___y_1726_ = v___x_1734_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_1732_;
                }
            }
            7 => {
                if v___y_1738_ == 0 {
                    v___x_1739_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2,
                    );
                    v___x_1740_ = lean_uint8_dec_le(v___x_1739_, v_c_1686_);
                    if v___x_1740_ == 0 {
                        v___y_1732_ = v___x_1740_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1741_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3,
                        );
                        v___x_1742_ = lean_uint8_dec_le(v_c_1686_, v___x_1741_);
                        v___y_1732_ = v___x_1742_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_1738_;
                }
            }
            8 => {
                if v___y_1744_ == 0 {
                    v___x_1745_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0,
                    );
                    v___x_1746_ = lean_uint8_dec_le(v___x_1745_, v_c_1686_);
                    if v___x_1746_ == 0 {
                        v___y_1738_ = v___x_1746_;
                        state = 7;
                        continue;
                    } else {
                        v___x_1747_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1,
                        );
                        v___x_1748_ = lean_uint8_dec_le(v_c_1686_, v___x_1747_);
                        v___y_1738_ = v___x_1748_;
                        state = 7;
                        continue;
                    }
                } else {
                    return v___y_1744_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isQueryChar___boxed(
    mut v_c_1753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1754_: u8 = 0;
    let mut v_res_1755_: u8 = 0;
    let mut v_r_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1754_ = (leanh::lean_unbox(v_c_1753_) as u8);
    v_res_1755_ = l_Std_Http_Internal_Char_isQueryChar(v_c_boxed_1754_);
    v_r_1756_ = leanh::lean_box((v_res_1755_) as usize);
    return v_r_1756_;
}
pub unsafe fn l_Std_Http_Internal_Char_isFragmentChar(mut v_c_1757_: u8) -> u8 {
    let mut v___y_1759_: u8 = 0;
    let mut v___x_1760_: u8 = 0;
    let mut v___x_1761_: u8 = 0;
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: u8 = 0;
    let mut v___y_1765_: u8 = 0;
    let mut v___x_1766_: u8 = 0;
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: u8 = 0;
    let mut v___x_1769_: u8 = 0;
    let mut v___y_1771_: u8 = 0;
    let mut v___x_1772_: u8 = 0;
    let mut v___x_1773_: u8 = 0;
    let mut v___x_1774_: u8 = 0;
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1776_: u8 = 0;
    let mut v___x_1777_: u8 = 0;
    let mut v___x_1778_: u8 = 0;
    let mut v___x_1779_: u8 = 0;
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: u8 = 0;
    let mut v___x_1782_: u8 = 0;
    let mut v___x_1783_: u8 = 0;
    let mut v___x_1784_: u8 = 0;
    let mut v___x_1785_: u8 = 0;
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1787_: u8 = 0;
    let mut v___x_1788_: u8 = 0;
    let mut v___x_1789_: u8 = 0;
    let mut v___y_1791_: u8 = 0;
    let mut v___x_1792_: u8 = 0;
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: u8 = 0;
    let mut v___x_1795_: u8 = 0;
    let mut v___y_1797_: u8 = 0;
    let mut v___x_1798_: u8 = 0;
    let mut v___x_1799_: u8 = 0;
    let mut v___x_1800_: u8 = 0;
    let mut v___x_1801_: u8 = 0;
    let mut v___y_1803_: u8 = 0;
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: u8 = 0;
    let mut v___x_1806_: u8 = 0;
    let mut v___x_1807_: u8 = 0;
    let mut v___y_1809_: u8 = 0;
    let mut v___x_1810_: u8 = 0;
    let mut v___x_1811_: u8 = 0;
    let mut v___x_1812_: u8 = 0;
    let mut v___x_1813_: u8 = 0;
    let mut v___y_1815_: u8 = 0;
    let mut v___x_1816_: u8 = 0;
    let mut v___x_1817_: u8 = 0;
    let mut v___x_1818_: u8 = 0;
    let mut v___x_1819_: u8 = 0;
    let mut v___x_1820_: u8 = 0;
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1820_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0_once),
                    _init_l_Std_Http_Internal_Char_isDigitByte___closed__0,
                );
                v___x_1821_ = lean_uint8_dec_le(v___x_1820_, v_c_1757_);
                if v___x_1821_ == 0 {
                    v___y_1815_ = v___x_1821_;
                    state = 8;
                    continue;
                } else {
                    v___x_1822_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isDigitByte___closed__1_once
                        ),
                        _init_l_Std_Http_Internal_Char_isDigitByte___closed__1,
                    );
                    v___x_1823_ = lean_uint8_dec_le(v_c_1757_, v___x_1822_);
                    v___y_1815_ = v___x_1823_;
                    state = 8;
                    continue;
                }
            }
            1 => {
                if v___y_1759_ == 0 {
                    v___x_1760_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isQueryChar___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isQueryChar___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isQueryChar___closed__0,
                    );
                    v___x_1761_ = lean_uint8_dec_eq(v_c_1757_, v___x_1760_);
                    if v___x_1761_ == 0 {
                        v___x_1762_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isQueryChar___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isQueryChar___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isQueryChar___closed__1,
                        );
                        v___x_1763_ = lean_uint8_dec_eq(v_c_1757_, v___x_1762_);
                        return v___x_1763_;
                    } else {
                        return v___x_1761_;
                    }
                } else {
                    return v___y_1759_;
                }
            }
            2 => {
                if v___y_1765_ == 0 {
                    v___x_1766_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0_once),
                        _init_l_Std_Http_Internal_Char_isPChar___closed__0,
                    );
                    v___x_1767_ = lean_uint8_dec_eq(v_c_1757_, v___x_1766_);
                    if v___x_1767_ == 0 {
                        v___x_1768_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isPChar___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isPChar___closed__1,
                        );
                        v___x_1769_ = lean_uint8_dec_eq(v_c_1757_, v___x_1768_);
                        v___y_1759_ = v___x_1769_;
                        state = 1;
                        continue;
                    } else {
                        v___y_1759_ = v___x_1767_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1765_;
                }
            }
            3 => {
                if v___y_1771_ == 0 {
                    v___x_1772_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__0,
                    );
                    v___x_1773_ = lean_uint8_dec_eq(v_c_1757_, v___x_1772_);
                    if v___x_1773_ == 0 {
                        v___x_1774_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__1,
                        );
                        v___x_1775_ = lean_uint8_dec_eq(v_c_1757_, v___x_1774_);
                        if v___x_1775_ == 0 {
                            v___x_1776_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2_once
                                ),
                                _init_l_Std_Http_Internal_Char_isSubDelims___closed__2,
                            );
                            v___x_1777_ = lean_uint8_dec_eq(v_c_1757_, v___x_1776_);
                            if v___x_1777_ == 0 {
                                v___x_1778_ = leanh::lean_uint8_once(
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3_once
                                    ),
                                    _init_l_Std_Http_Internal_Char_isSubDelims___closed__3,
                                );
                                v___x_1779_ = lean_uint8_dec_eq(v_c_1757_, v___x_1778_);
                                if v___x_1779_ == 0 {
                                    v___x_1780_ = leanh::lean_uint8_once(
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4_once
                                        ),
                                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__4,
                                    );
                                    v___x_1781_ = lean_uint8_dec_eq(v_c_1757_, v___x_1780_);
                                    if v___x_1781_ == 0 {
                                        v___x_1782_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
                                        v___x_1783_ = lean_uint8_dec_eq(v_c_1757_, v___x_1782_);
                                        if v___x_1783_ == 0 {
                                            v___x_1784_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
                                            v___x_1785_ = lean_uint8_dec_eq(v_c_1757_, v___x_1784_);
                                            if v___x_1785_ == 0 {
                                                v___x_1786_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
                                                v___x_1787_ =
                                                    lean_uint8_dec_eq(v_c_1757_, v___x_1786_);
                                                if v___x_1787_ == 0 {
                                                    v___x_1788_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
                                                    v___x_1789_ =
                                                        lean_uint8_dec_eq(v_c_1757_, v___x_1788_);
                                                    v___y_1765_ = v___x_1789_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___y_1765_ = v___x_1787_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                v___y_1765_ = v___x_1785_;
                                                state = 2;
                                                continue;
                                            }
                                        } else {
                                            v___y_1765_ = v___x_1783_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        v___y_1765_ = v___x_1781_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v___y_1765_ = v___x_1779_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v___y_1765_ = v___x_1777_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___y_1765_ = v___x_1775_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_1765_ = v___x_1773_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_1771_;
                }
            }
            4 => {
                if v___y_1791_ == 0 {
                    v___x_1792_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__9_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__9,
                    );
                    v___x_1793_ = lean_uint8_dec_eq(v_c_1757_, v___x_1792_);
                    if v___x_1793_ == 0 {
                        v___x_1794_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__10,
                        );
                        v___x_1795_ = lean_uint8_dec_eq(v_c_1757_, v___x_1794_);
                        v___y_1771_ = v___x_1795_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1771_ = v___x_1793_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_1791_;
                }
            }
            5 => {
                if v___y_1797_ == 0 {
                    v___x_1798_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__0,
                    );
                    v___x_1799_ = lean_uint8_dec_eq(v_c_1757_, v___x_1798_);
                    if v___x_1799_ == 0 {
                        v___x_1800_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__1,
                        );
                        v___x_1801_ = lean_uint8_dec_eq(v_c_1757_, v___x_1800_);
                        v___y_1791_ = v___x_1801_;
                        state = 4;
                        continue;
                    } else {
                        v___y_1791_ = v___x_1799_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_1797_;
                }
            }
            6 => {
                if v___y_1803_ == 0 {
                    v___x_1804_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__2,
                    );
                    v___x_1805_ = lean_uint8_dec_eq(v_c_1757_, v___x_1804_);
                    if v___x_1805_ == 0 {
                        v___x_1806_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__3,
                        );
                        v___x_1807_ = lean_uint8_dec_eq(v_c_1757_, v___x_1806_);
                        v___y_1797_ = v___x_1807_;
                        state = 5;
                        continue;
                    } else {
                        v___y_1797_ = v___x_1805_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_1803_;
                }
            }
            7 => {
                if v___y_1809_ == 0 {
                    v___x_1810_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2,
                    );
                    v___x_1811_ = lean_uint8_dec_le(v___x_1810_, v_c_1757_);
                    if v___x_1811_ == 0 {
                        v___y_1803_ = v___x_1811_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1812_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3,
                        );
                        v___x_1813_ = lean_uint8_dec_le(v_c_1757_, v___x_1812_);
                        v___y_1803_ = v___x_1813_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_1809_;
                }
            }
            8 => {
                if v___y_1815_ == 0 {
                    v___x_1816_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0,
                    );
                    v___x_1817_ = lean_uint8_dec_le(v___x_1816_, v_c_1757_);
                    if v___x_1817_ == 0 {
                        v___y_1809_ = v___x_1817_;
                        state = 7;
                        continue;
                    } else {
                        v___x_1818_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1,
                        );
                        v___x_1819_ = lean_uint8_dec_le(v_c_1757_, v___x_1818_);
                        v___y_1809_ = v___x_1819_;
                        state = 7;
                        continue;
                    }
                } else {
                    return v___y_1815_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isFragmentChar___boxed(
    mut v_c_1824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1825_: u8 = 0;
    let mut v_res_1826_: u8 = 0;
    let mut v_r_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1825_ = (leanh::lean_unbox(v_c_1824_) as u8);
    v_res_1826_ = l_Std_Http_Internal_Char_isFragmentChar(v_c_boxed_1825_);
    v_r_1827_ = leanh::lean_box((v_res_1826_) as usize);
    return v_r_1827_;
}
pub unsafe fn l_Std_Http_Internal_Char_isUserInfoChar(mut v_c_1828_: u8) -> u8 {
    let mut v___y_1830_: u8 = 0;
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1832_: u8 = 0;
    let mut v___y_1834_: u8 = 0;
    let mut v___x_1835_: u8 = 0;
    let mut v___x_1836_: u8 = 0;
    let mut v___x_1837_: u8 = 0;
    let mut v___x_1838_: u8 = 0;
    let mut v___x_1839_: u8 = 0;
    let mut v___x_1840_: u8 = 0;
    let mut v___x_1841_: u8 = 0;
    let mut v___x_1842_: u8 = 0;
    let mut v___x_1843_: u8 = 0;
    let mut v___x_1844_: u8 = 0;
    let mut v___x_1845_: u8 = 0;
    let mut v___x_1846_: u8 = 0;
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: u8 = 0;
    let mut v___x_1849_: u8 = 0;
    let mut v___x_1850_: u8 = 0;
    let mut v___x_1851_: u8 = 0;
    let mut v___x_1852_: u8 = 0;
    let mut v___y_1854_: u8 = 0;
    let mut v___x_1855_: u8 = 0;
    let mut v___x_1856_: u8 = 0;
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1858_: u8 = 0;
    let mut v___y_1860_: u8 = 0;
    let mut v___x_1861_: u8 = 0;
    let mut v___x_1862_: u8 = 0;
    let mut v___x_1863_: u8 = 0;
    let mut v___x_1864_: u8 = 0;
    let mut v___y_1866_: u8 = 0;
    let mut v___x_1867_: u8 = 0;
    let mut v___x_1868_: u8 = 0;
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: u8 = 0;
    let mut v___y_1872_: u8 = 0;
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: u8 = 0;
    let mut v___x_1875_: u8 = 0;
    let mut v___x_1876_: u8 = 0;
    let mut v___y_1878_: u8 = 0;
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: u8 = 0;
    let mut v___x_1881_: u8 = 0;
    let mut v___x_1882_: u8 = 0;
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: u8 = 0;
    let mut v___x_1885_: u8 = 0;
    let mut v___x_1886_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1883_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0_once),
                    _init_l_Std_Http_Internal_Char_isDigitByte___closed__0,
                );
                v___x_1884_ = lean_uint8_dec_le(v___x_1883_, v_c_1828_);
                if v___x_1884_ == 0 {
                    v___y_1878_ = v___x_1884_;
                    state = 7;
                    continue;
                } else {
                    v___x_1885_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isDigitByte___closed__1_once
                        ),
                        _init_l_Std_Http_Internal_Char_isDigitByte___closed__1,
                    );
                    v___x_1886_ = lean_uint8_dec_le(v_c_1828_, v___x_1885_);
                    v___y_1878_ = v___x_1886_;
                    state = 7;
                    continue;
                }
            }
            1 => {
                if v___y_1830_ == 0 {
                    v___x_1831_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0_once),
                        _init_l_Std_Http_Internal_Char_isPChar___closed__0,
                    );
                    v___x_1832_ = lean_uint8_dec_eq(v_c_1828_, v___x_1831_);
                    return v___x_1832_;
                } else {
                    return v___y_1830_;
                }
            }
            2 => {
                if v___y_1834_ == 0 {
                    v___x_1835_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__0,
                    );
                    v___x_1836_ = lean_uint8_dec_eq(v_c_1828_, v___x_1835_);
                    if v___x_1836_ == 0 {
                        v___x_1837_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__1,
                        );
                        v___x_1838_ = lean_uint8_dec_eq(v_c_1828_, v___x_1837_);
                        if v___x_1838_ == 0 {
                            v___x_1839_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2_once
                                ),
                                _init_l_Std_Http_Internal_Char_isSubDelims___closed__2,
                            );
                            v___x_1840_ = lean_uint8_dec_eq(v_c_1828_, v___x_1839_);
                            if v___x_1840_ == 0 {
                                v___x_1841_ = leanh::lean_uint8_once(
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3_once
                                    ),
                                    _init_l_Std_Http_Internal_Char_isSubDelims___closed__3,
                                );
                                v___x_1842_ = lean_uint8_dec_eq(v_c_1828_, v___x_1841_);
                                if v___x_1842_ == 0 {
                                    v___x_1843_ = leanh::lean_uint8_once(
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4_once
                                        ),
                                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__4,
                                    );
                                    v___x_1844_ = lean_uint8_dec_eq(v_c_1828_, v___x_1843_);
                                    if v___x_1844_ == 0 {
                                        v___x_1845_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
                                        v___x_1846_ = lean_uint8_dec_eq(v_c_1828_, v___x_1845_);
                                        if v___x_1846_ == 0 {
                                            v___x_1847_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
                                            v___x_1848_ = lean_uint8_dec_eq(v_c_1828_, v___x_1847_);
                                            if v___x_1848_ == 0 {
                                                v___x_1849_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
                                                v___x_1850_ =
                                                    lean_uint8_dec_eq(v_c_1828_, v___x_1849_);
                                                if v___x_1850_ == 0 {
                                                    v___x_1851_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
                                                    v___x_1852_ =
                                                        lean_uint8_dec_eq(v_c_1828_, v___x_1851_);
                                                    v___y_1830_ = v___x_1852_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___y_1830_ = v___x_1850_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v___y_1830_ = v___x_1848_;
                                                state = 1;
                                                continue;
                                            }
                                        } else {
                                            v___y_1830_ = v___x_1846_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        v___y_1830_ = v___x_1844_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___y_1830_ = v___x_1842_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v___y_1830_ = v___x_1840_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___y_1830_ = v___x_1838_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___y_1830_ = v___x_1836_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_1834_;
                }
            }
            3 => {
                if v___y_1854_ == 0 {
                    v___x_1855_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__9_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__9,
                    );
                    v___x_1856_ = lean_uint8_dec_eq(v_c_1828_, v___x_1855_);
                    if v___x_1856_ == 0 {
                        v___x_1857_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__10,
                        );
                        v___x_1858_ = lean_uint8_dec_eq(v_c_1828_, v___x_1857_);
                        v___y_1834_ = v___x_1858_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1834_ = v___x_1856_;
                        state = 2;
                        continue;
                    }
                } else {
                    return v___y_1854_;
                }
            }
            4 => {
                if v___y_1860_ == 0 {
                    v___x_1861_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__0,
                    );
                    v___x_1862_ = lean_uint8_dec_eq(v_c_1828_, v___x_1861_);
                    if v___x_1862_ == 0 {
                        v___x_1863_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__1,
                        );
                        v___x_1864_ = lean_uint8_dec_eq(v_c_1828_, v___x_1863_);
                        v___y_1854_ = v___x_1864_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1854_ = v___x_1862_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___y_1860_;
                }
            }
            5 => {
                if v___y_1866_ == 0 {
                    v___x_1867_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__2,
                    );
                    v___x_1868_ = lean_uint8_dec_eq(v_c_1828_, v___x_1867_);
                    if v___x_1868_ == 0 {
                        v___x_1869_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__3,
                        );
                        v___x_1870_ = lean_uint8_dec_eq(v_c_1828_, v___x_1869_);
                        v___y_1860_ = v___x_1870_;
                        state = 4;
                        continue;
                    } else {
                        v___y_1860_ = v___x_1868_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___y_1866_;
                }
            }
            6 => {
                if v___y_1872_ == 0 {
                    v___x_1873_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2,
                    );
                    v___x_1874_ = lean_uint8_dec_le(v___x_1873_, v_c_1828_);
                    if v___x_1874_ == 0 {
                        v___y_1866_ = v___x_1874_;
                        state = 5;
                        continue;
                    } else {
                        v___x_1875_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3,
                        );
                        v___x_1876_ = lean_uint8_dec_le(v_c_1828_, v___x_1875_);
                        v___y_1866_ = v___x_1876_;
                        state = 5;
                        continue;
                    }
                } else {
                    return v___y_1872_;
                }
            }
            7 => {
                if v___y_1878_ == 0 {
                    v___x_1879_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0,
                    );
                    v___x_1880_ = lean_uint8_dec_le(v___x_1879_, v_c_1828_);
                    if v___x_1880_ == 0 {
                        v___y_1872_ = v___x_1880_;
                        state = 6;
                        continue;
                    } else {
                        v___x_1881_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1,
                        );
                        v___x_1882_ = lean_uint8_dec_le(v_c_1828_, v___x_1881_);
                        v___y_1872_ = v___x_1882_;
                        state = 6;
                        continue;
                    }
                } else {
                    return v___y_1878_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Http_Internal_Char_isUserInfoChar___boxed(
    mut v_c_1887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1888_: u8 = 0;
    let mut v_res_1889_: u8 = 0;
    let mut v_r_1890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1888_ = (leanh::lean_unbox(v_c_1887_) as u8);
    v_res_1889_ = l_Std_Http_Internal_Char_isUserInfoChar(v_c_boxed_1888_);
    v_r_1890_ = leanh::lean_box((v_res_1889_) as usize);
    return v_r_1890_;
}
pub unsafe fn l_Std_Http_Internal_Char_isQueryDataChar(mut v_c_1891_: u8) -> u8 {
    let mut v___x_1893_: u8 = 0;
    let mut v___x_1894_: u8 = 0;
    let mut v___x_1895_: u8 = 0;
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1897_: u8 = 0;
    let mut v___x_1898_: u8 = 0;
    let mut v___y_1900_: u8 = 0;
    let mut v___y_1902_: u8 = 0;
    let mut v___x_1903_: u8 = 0;
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: u8 = 0;
    let mut v___x_1906_: u8 = 0;
    let mut v___y_1908_: u8 = 0;
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: u8 = 0;
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: u8 = 0;
    let mut v___y_1914_: u8 = 0;
    let mut v___x_1915_: u8 = 0;
    let mut v___x_1916_: u8 = 0;
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: u8 = 0;
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: u8 = 0;
    let mut v___x_1921_: u8 = 0;
    let mut v___x_1922_: u8 = 0;
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: u8 = 0;
    let mut v___x_1925_: u8 = 0;
    let mut v___x_1926_: u8 = 0;
    let mut v___x_1927_: u8 = 0;
    let mut v___x_1928_: u8 = 0;
    let mut v___x_1929_: u8 = 0;
    let mut v___x_1930_: u8 = 0;
    let mut v___x_1931_: u8 = 0;
    let mut v___x_1932_: u8 = 0;
    let mut v___y_1934_: u8 = 0;
    let mut v___x_1935_: u8 = 0;
    let mut v___x_1936_: u8 = 0;
    let mut v___x_1937_: u8 = 0;
    let mut v___x_1938_: u8 = 0;
    let mut v___y_1940_: u8 = 0;
    let mut v___x_1941_: u8 = 0;
    let mut v___x_1942_: u8 = 0;
    let mut v___x_1943_: u8 = 0;
    let mut v___x_1944_: u8 = 0;
    let mut v___y_1946_: u8 = 0;
    let mut v___x_1947_: u8 = 0;
    let mut v___x_1948_: u8 = 0;
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: u8 = 0;
    let mut v___y_1952_: u8 = 0;
    let mut v___x_1953_: u8 = 0;
    let mut v___x_1954_: u8 = 0;
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: u8 = 0;
    let mut v___y_1958_: u8 = 0;
    let mut v___x_1959_: u8 = 0;
    let mut v___x_1960_: u8 = 0;
    let mut v___x_1961_: u8 = 0;
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: u8 = 0;
    let mut v___x_1964_: u8 = 0;
    let mut v___x_1965_: u8 = 0;
    let mut v___x_1966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1963_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__0_once),
                    _init_l_Std_Http_Internal_Char_isDigitByte___closed__0,
                );
                v___x_1964_ = lean_uint8_dec_le(v___x_1963_, v_c_1891_);
                if v___x_1964_ == 0 {
                    v___y_1958_ = v___x_1964_;
                    state = 10;
                    continue;
                } else {
                    v___x_1965_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isDigitByte___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isDigitByte___closed__1_once
                        ),
                        _init_l_Std_Http_Internal_Char_isDigitByte___closed__1,
                    );
                    v___x_1966_ = lean_uint8_dec_le(v_c_1891_, v___x_1965_);
                    v___y_1958_ = v___x_1966_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_1893_ = leanh::lean_uint8_once(
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__0),
                    core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__0_once),
                    _init_l_Std_Http_Internal_Char_isSubDelims___closed__0,
                );
                v___x_1894_ = lean_uint8_dec_eq(v_c_1891_, v___x_1893_);
                if v___x_1894_ == 0 {
                    v___x_1895_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__8_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__8,
                    );
                    v___x_1896_ = lean_uint8_dec_eq(v_c_1891_, v___x_1895_);
                    if v___x_1896_ == 0 {
                        v___x_1897_ = 1;
                        return v___x_1897_;
                    } else {
                        return v___x_1894_;
                    }
                } else {
                    v___x_1898_ = 0;
                    return v___x_1898_;
                }
            }
            2 => {
                if v___y_1900_ == 0 {
                    return v___y_1900_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_1902_ == 0 {
                    v___x_1903_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isQueryChar___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isQueryChar___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isQueryChar___closed__0,
                    );
                    v___x_1904_ = lean_uint8_dec_eq(v_c_1891_, v___x_1903_);
                    if v___x_1904_ == 0 {
                        v___x_1905_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isQueryChar___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isQueryChar___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isQueryChar___closed__1,
                        );
                        v___x_1906_ = lean_uint8_dec_eq(v_c_1891_, v___x_1905_);
                        v___y_1900_ = v___x_1906_;
                        state = 2;
                        continue;
                    } else {
                        v___y_1900_ = v___x_1904_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v___y_1908_ == 0 {
                    v___x_1909_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0),
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__0_once),
                        _init_l_Std_Http_Internal_Char_isPChar___closed__0,
                    );
                    v___x_1910_ = lean_uint8_dec_eq(v_c_1891_, v___x_1909_);
                    if v___x_1910_ == 0 {
                        v___x_1911_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isPChar___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isPChar___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isPChar___closed__1,
                        );
                        v___x_1912_ = lean_uint8_dec_eq(v_c_1891_, v___x_1911_);
                        v___y_1902_ = v___x_1912_;
                        state = 3;
                        continue;
                    } else {
                        v___y_1902_ = v___x_1910_;
                        state = 3;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            5 => {
                if v___y_1914_ == 0 {
                    v___x_1915_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__0,
                    );
                    v___x_1916_ = lean_uint8_dec_eq(v_c_1891_, v___x_1915_);
                    if v___x_1916_ == 0 {
                        v___x_1917_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__1,
                        );
                        v___x_1918_ = lean_uint8_dec_eq(v_c_1891_, v___x_1917_);
                        if v___x_1918_ == 0 {
                            v___x_1919_ = leanh::lean_uint8_once(
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Std_Http_Internal_Char_isSubDelims___closed__2_once
                                ),
                                _init_l_Std_Http_Internal_Char_isSubDelims___closed__2,
                            );
                            v___x_1920_ = lean_uint8_dec_eq(v_c_1891_, v___x_1919_);
                            if v___x_1920_ == 0 {
                                v___x_1921_ = leanh::lean_uint8_once(
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Std_Http_Internal_Char_isSubDelims___closed__3_once
                                    ),
                                    _init_l_Std_Http_Internal_Char_isSubDelims___closed__3,
                                );
                                v___x_1922_ = lean_uint8_dec_eq(v_c_1891_, v___x_1921_);
                                if v___x_1922_ == 0 {
                                    v___x_1923_ = leanh::lean_uint8_once(
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Std_Http_Internal_Char_isSubDelims___closed__4_once
                                        ),
                                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__4,
                                    );
                                    v___x_1924_ = lean_uint8_dec_eq(v_c_1891_, v___x_1923_);
                                    if v___x_1924_ == 0 {
                                        v___x_1925_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__5_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__5);
                                        v___x_1926_ = lean_uint8_dec_eq(v_c_1891_, v___x_1925_);
                                        if v___x_1926_ == 0 {
                                            v___x_1927_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__6_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__6);
                                            v___x_1928_ = lean_uint8_dec_eq(v_c_1891_, v___x_1927_);
                                            if v___x_1928_ == 0 {
                                                v___x_1929_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__7_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__7);
                                                v___x_1930_ =
                                                    lean_uint8_dec_eq(v_c_1891_, v___x_1929_);
                                                if v___x_1930_ == 0 {
                                                    v___x_1931_ = leanh::lean_uint8_once(core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8), core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__8_once), _init_l_Std_Http_Internal_Char_isSubDelims___closed__8);
                                                    v___x_1932_ =
                                                        lean_uint8_dec_eq(v_c_1891_, v___x_1931_);
                                                    v___y_1908_ = v___x_1932_;
                                                    state = 4;
                                                    continue;
                                                } else {
                                                    v___y_1908_ = v___x_1930_;
                                                    state = 4;
                                                    continue;
                                                }
                                            } else {
                                                v___y_1908_ = v___x_1928_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            v___y_1908_ = v___x_1926_;
                                            state = 4;
                                            continue;
                                        }
                                    } else {
                                        v___y_1908_ = v___x_1924_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    v___y_1908_ = v___x_1922_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                v___y_1908_ = v___x_1920_;
                                state = 4;
                                continue;
                            }
                        } else {
                            v___y_1908_ = v___x_1918_;
                            state = 4;
                            continue;
                        }
                    } else {
                        v___y_1908_ = v___x_1916_;
                        state = 4;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            6 => {
                if v___y_1934_ == 0 {
                    v___x_1935_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isSubDelims___closed__9),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isSubDelims___closed__9_once
                        ),
                        _init_l_Std_Http_Internal_Char_isSubDelims___closed__9,
                    );
                    v___x_1936_ = lean_uint8_dec_eq(v_c_1891_, v___x_1935_);
                    if v___x_1936_ == 0 {
                        v___x_1937_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isSubDelims___closed__10_once
                            ),
                            _init_l_Std_Http_Internal_Char_isSubDelims___closed__10,
                        );
                        v___x_1938_ = lean_uint8_dec_eq(v_c_1891_, v___x_1937_);
                        v___y_1914_ = v___x_1938_;
                        state = 5;
                        continue;
                    } else {
                        v___y_1914_ = v___x_1936_;
                        state = 5;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            7 => {
                if v___y_1940_ == 0 {
                    v___x_1941_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__0,
                    );
                    v___x_1942_ = lean_uint8_dec_eq(v_c_1891_, v___x_1941_);
                    if v___x_1942_ == 0 {
                        v___x_1943_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__1,
                        );
                        v___x_1944_ = lean_uint8_dec_eq(v_c_1891_, v___x_1943_);
                        v___y_1934_ = v___x_1944_;
                        state = 6;
                        continue;
                    } else {
                        v___y_1934_ = v___x_1942_;
                        state = 6;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            8 => {
                if v___y_1946_ == 0 {
                    v___x_1947_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isUnreserved___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isUnreserved___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isUnreserved___closed__2,
                    );
                    v___x_1948_ = lean_uint8_dec_eq(v_c_1891_, v___x_1947_);
                    if v___x_1948_ == 0 {
                        v___x_1949_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isUnreserved___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isUnreserved___closed__3,
                        );
                        v___x_1950_ = lean_uint8_dec_eq(v_c_1891_, v___x_1949_);
                        v___y_1940_ = v___x_1950_;
                        state = 7;
                        continue;
                    } else {
                        v___y_1940_ = v___x_1948_;
                        state = 7;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            9 => {
                if v___y_1952_ == 0 {
                    v___x_1953_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__2),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__2_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__2,
                    );
                    v___x_1954_ = lean_uint8_dec_le(v___x_1953_, v_c_1891_);
                    if v___x_1954_ == 0 {
                        v___y_1946_ = v___x_1954_;
                        state = 8;
                        continue;
                    } else {
                        v___x_1955_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__3_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__3,
                        );
                        v___x_1956_ = lean_uint8_dec_le(v_c_1891_, v___x_1955_);
                        v___y_1946_ = v___x_1956_;
                        state = 8;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            10 => {
                if v___y_1958_ == 0 {
                    v___x_1959_ = leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Std_Http_Internal_Char_isAlphaByte___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Std_Http_Internal_Char_isAlphaByte___closed__0_once
                        ),
                        _init_l_Std_Http_Internal_Char_isAlphaByte___closed__0,
                    );
                    v___x_1960_ = lean_uint8_dec_le(v___x_1959_, v_c_1891_);
                    if v___x_1960_ == 0 {
                        v___y_1952_ = v___x_1960_;
                        state = 9;
                        continue;
                    } else {
                        v___x_1961_ = leanh::lean_uint8_once(
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Std_Http_Internal_Char_isAlphaByte___closed__1_once
                            ),
                            _init_l_Std_Http_Internal_Char_isAlphaByte___closed__1,
                        );
                        v___x_1962_ = lean_uint8_dec_le(v_c_1891_, v___x_1961_);
                        v___y_1952_ = v___x_1962_;
                        state = 9;
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
pub unsafe fn l_Std_Http_Internal_Char_isQueryDataChar___boxed(
    mut v_c_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_1968_: u8 = 0;
    let mut v_res_1969_: u8 = 0;
    let mut v_r_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_1968_ = (leanh::lean_unbox(v_c_1967_) as u8);
    v_res_1969_ = l_Std_Http_Internal_Char_isQueryDataChar(v_c_boxed_1968_);
    v_r_1970_ = leanh::lean_box((v_res_1969_) as usize);
    return v_r_1970_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Http_Internal_Char(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Http_Internal_Char(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Http_Internal_Char(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Http_Internal_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Http_Internal_Char(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Http_Internal_Char(builtin);
}