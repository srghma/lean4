// Lean compiler output
// Module: Lake.Version
// Imports: Init.Prelude Init.Data.ToString Init.Data.String.TakeDrop
use crate::ffi::{
    lean_nat_dec_eq, lean_string_append, lean_string_dec_eq, lean_string_utf8_byte_size,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_nextn;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::{
    initialize_Init_Data_ToString, runtime_initialize_Init_Data_ToString,
};
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_githash, l_Lean_version_isRelease, l_Lean_versionString,
};
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
pub static mut l_Lake_version_major: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_version_minor: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_version_patch: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_version_isRelease: u8 = 0;
pub static l_Lake_version_specialDesc___closed__0_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [115, 114, 99, 0],
    };
static mut l_Lake_version_specialDesc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_version_specialDesc___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_version_specialDesc___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [115, 114, 99, 43, 0],
    };
static mut l_Lake_version_specialDesc___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_version_specialDesc___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_version_specialDesc___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_version_specialDesc___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_version_specialDesc___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_version_specialDesc___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_version_specialDesc___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_version_specialDesc___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_version_specialDesc___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_version_specialDesc___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_version_specialDesc___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_version_specialDesc___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_version_specialDesc___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_version_specialDesc___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_version_specialDesc___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_version_specialDesc___closed__8: u8 = 0;
pub static mut l_Lake_version_specialDesc: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_versionStringCore___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionStringCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_versionStringCore___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [46, 0],
    };
static mut l_Lake_versionStringCore___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_versionStringCore___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lake_versionStringCore___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionStringCore___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_versionStringCore___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionStringCore___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_versionStringCore___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionStringCore___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_versionStringCore___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionStringCore___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_versionStringCore___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionStringCore___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_versionStringCore: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_versionString___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lake_versionString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_versionString___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_versionString___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionString___closed__1: u8 = 0;
pub static l_Lake_versionString___closed__2_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [45, 0],
    };
static mut l_Lake_versionString___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_versionString___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_versionString___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionString___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_versionString___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_versionString___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lake_versionString: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_uiVersionString___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            76, 97, 107, 101, 32, 118, 101, 114, 115, 105, 111, 110, 32, 0,
        ],
    };
static mut l_Lake_uiVersionString___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_uiVersionString___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_uiVersionString___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_uiVersionString___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_uiVersionString___closed__2_value: crate::leanh::LeanStringObject<16> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            32, 40, 76, 101, 97, 110, 32, 118, 101, 114, 115, 105, 111, 110, 32, 0,
        ],
    };
static mut l_Lake_uiVersionString___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_uiVersionString___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_uiVersionString___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_uiVersionString___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lake_uiVersionString___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_uiVersionString___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_uiVersionString___closed__5_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [41, 0],
    };
static mut l_Lake_uiVersionString___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_uiVersionString___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_uiVersionString___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_uiVersionString___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_uiVersionString: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lake_version_major() -> *mut crate::leanh::LeanObject {
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_84_ = crate::leanh::lean_unsigned_to_nat(5);
    return v___x_84_;
}
pub unsafe fn _init_l_Lake_version_minor() -> *mut crate::leanh::LeanObject {
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_85_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_85_;
}
pub unsafe fn _init_l_Lake_version_patch() -> *mut crate::leanh::LeanObject {
    let mut v___x_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_86_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_86_;
}
pub unsafe fn _init_l_Lake_version_isRelease() -> u8 {
    let mut v___x_87_: u8 = 0;
    v___x_87_ = l_Lean_version_isRelease;
    return v___x_87_;
}
pub unsafe fn _init_l_Lake_version_specialDesc___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_90_ = l_Lean_githash;
    v___x_91_ = lean_string_utf8_byte_size(v___x_90_);
    return v___x_91_;
}
pub unsafe fn _init_l_Lake_version_specialDesc___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_92_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__2),
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__2_once),
        _init_l_Lake_version_specialDesc___closed__2,
    );
    v___x_93_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_94_ = l_Lean_githash;
    v___x_95_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_95_, 0, v___x_94_);
    crate::leanh::lean_ctor_set(v___x_95_, 1, v___x_93_);
    crate::leanh::lean_ctor_set(v___x_95_, 2, v___x_92_);
    return v___x_95_;
}
pub unsafe fn _init_l_Lake_version_specialDesc___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = crate::leanh::lean_unsigned_to_nat(7);
    v___x_97_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_98_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__3),
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__3_once),
        _init_l_Lake_version_specialDesc___closed__3,
    );
    v___x_99_ = l_String_Slice_Pos_nextn(v___x_98_, v___x_97_, v___x_96_);
    return v___x_99_;
}
pub unsafe fn _init_l_Lake_version_specialDesc___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_100_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__4),
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__4_once),
        _init_l_Lake_version_specialDesc___closed__4,
    );
    v___x_101_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_102_ = l_Lean_githash;
    v___x_103_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_103_, 0, v___x_102_);
    crate::leanh::lean_ctor_set(v___x_103_, 1, v___x_101_);
    crate::leanh::lean_ctor_set(v___x_103_, 2, v___x_100_);
    return v___x_103_;
}
pub unsafe fn _init_l_Lake_version_specialDesc___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_104_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__5),
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__5_once),
        _init_l_Lake_version_specialDesc___closed__5,
    );
    v___x_105_ = l_String_Slice_toString(v___x_104_);
    return v___x_105_;
}
pub unsafe fn _init_l_Lake_version_specialDesc___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_106_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__6),
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__6_once),
        _init_l_Lake_version_specialDesc___closed__6,
    );
    v___x_107_ = l_Lake_version_specialDesc___closed__1;
    v___x_108_ = lean_string_append(v___x_107_, v___x_106_);
    return v___x_108_;
}
pub unsafe fn _init_l_Lake_version_specialDesc___closed__8() -> u8 {
    let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: u8 = 0;
    v___x_109_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_110_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__2),
        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__2_once),
        _init_l_Lake_version_specialDesc___closed__2,
    );
    v___x_111_ = lean_nat_dec_eq(v___x_110_, v___x_109_);
    return v___x_111_;
}
pub unsafe fn _init_l_Lake_version_specialDesc() -> *mut crate::leanh::LeanObject {
    let mut v___y_113_: u8 = 0;
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: u8 = 0;
    let mut v___x_117_: u8 = 0;
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_116_ = l_Lean_version_isRelease;
                if v___x_116_ == 0 {
                    v___y_113_ = v___x_116_;
                    state = 1;
                    continue;
                } else {
                    v___x_117_ = crate::leanh::lean_uint8_once(
                        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__8),
                        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__8_once),
                        _init_l_Lake_version_specialDesc___closed__8,
                    );
                    if v___x_117_ == 0 {
                        v___y_113_ = v___x_116_;
                        state = 1;
                        continue;
                    } else {
                        v___x_118_ = l_Lake_version_specialDesc___closed__0;
                        return v___x_118_;
                    }
                }
            }
            1 => {
                if v___y_113_ == 0 {
                    v___x_114_ = l_Lake_version_specialDesc___closed__0;
                    return v___x_114_;
                } else {
                    v___x_115_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__7),
                        core::ptr::addr_of_mut!(l_Lake_version_specialDesc___closed__7_once),
                        _init_l_Lake_version_specialDesc___closed__7,
                    );
                    return v___x_115_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lake_versionStringCore___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_119_ = crate::leanh::lean_unsigned_to_nat(5);
    v___x_120_ = l_Nat_reprFast(v___x_119_);
    return v___x_120_;
}
pub unsafe fn _init_l_Lake_versionStringCore___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_122_ = l_Lake_versionStringCore___closed__1;
    v___x_123_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__0),
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__0_once),
        _init_l_Lake_versionStringCore___closed__0,
    );
    v___x_124_ = lean_string_append(v___x_123_, v___x_122_);
    return v___x_124_;
}
pub unsafe fn _init_l_Lake_versionStringCore___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_125_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_126_ = l_Nat_reprFast(v___x_125_);
    return v___x_126_;
}
pub unsafe fn _init_l_Lake_versionStringCore___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_127_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__3),
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__3_once),
        _init_l_Lake_versionStringCore___closed__3,
    );
    v___x_128_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__2),
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__2_once),
        _init_l_Lake_versionStringCore___closed__2,
    );
    v___x_129_ = lean_string_append(v___x_128_, v___x_127_);
    return v___x_129_;
}
pub unsafe fn _init_l_Lake_versionStringCore___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_130_ = l_Lake_versionStringCore___closed__1;
    v___x_131_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__4),
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__4_once),
        _init_l_Lake_versionStringCore___closed__4,
    );
    v___x_132_ = lean_string_append(v___x_131_, v___x_130_);
    return v___x_132_;
}
pub unsafe fn _init_l_Lake_versionStringCore___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_133_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__3),
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__3_once),
        _init_l_Lake_versionStringCore___closed__3,
    );
    v___x_134_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__5),
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__5_once),
        _init_l_Lake_versionStringCore___closed__5,
    );
    v___x_135_ = lean_string_append(v___x_134_, v___x_133_);
    return v___x_135_;
}
pub unsafe fn _init_l_Lake_versionStringCore() -> *mut crate::leanh::LeanObject {
    let mut v___x_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_136_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__6),
        core::ptr::addr_of_mut!(l_Lake_versionStringCore___closed__6_once),
        _init_l_Lake_versionStringCore___closed__6,
    );
    return v___x_136_;
}
pub unsafe fn _init_l_Lake_versionString___closed__1() -> u8 {
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: u8 = 0;
    v___x_138_ = l_Lake_versionString___closed__0;
    v___x_139_ = l_Lake_version_specialDesc;
    v___x_140_ = lean_string_dec_eq(v___x_139_, v___x_138_);
    return v___x_140_;
}
pub unsafe fn _init_l_Lake_versionString___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = l_Lake_versionString___closed__2;
    v___x_143_ = l_Lake_versionStringCore;
    v___x_144_ = lean_string_append(v___x_143_, v___x_142_);
    return v___x_144_;
}
pub unsafe fn _init_l_Lake_versionString___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_145_ = l_Lake_version_specialDesc;
    v___x_146_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_versionString___closed__3),
        core::ptr::addr_of_mut!(l_Lake_versionString___closed__3_once),
        _init_l_Lake_versionString___closed__3,
    );
    v___x_147_ = lean_string_append(v___x_146_, v___x_145_);
    return v___x_147_;
}
pub unsafe fn _init_l_Lake_versionString() -> *mut crate::leanh::LeanObject {
    let mut v___x_148_: u8 = 0;
    v___x_148_ = crate::leanh::lean_uint8_once(
        core::ptr::addr_of_mut!(l_Lake_versionString___closed__1),
        core::ptr::addr_of_mut!(l_Lake_versionString___closed__1_once),
        _init_l_Lake_versionString___closed__1,
    );
    if v___x_148_ == 0 {
        let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_149_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lake_versionString___closed__4),
            core::ptr::addr_of_mut!(l_Lake_versionString___closed__4_once),
            _init_l_Lake_versionString___closed__4,
        );
        return v___x_149_;
    } else {
        let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_150_ = l_Lake_versionStringCore;
        return v___x_150_;
    }
}
pub unsafe fn _init_l_Lake_uiVersionString___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_152_ = l_Lake_versionString;
    v___x_153_ = l_Lake_uiVersionString___closed__0;
    v___x_154_ = lean_string_append(v___x_153_, v___x_152_);
    return v___x_154_;
}
pub unsafe fn _init_l_Lake_uiVersionString___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_156_ = l_Lake_uiVersionString___closed__2;
    v___x_157_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_uiVersionString___closed__1),
        core::ptr::addr_of_mut!(l_Lake_uiVersionString___closed__1_once),
        _init_l_Lake_uiVersionString___closed__1,
    );
    v___x_158_ = lean_string_append(v___x_157_, v___x_156_);
    return v___x_158_;
}
pub unsafe fn _init_l_Lake_uiVersionString___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_159_ = l_Lean_versionString;
    v___x_160_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_uiVersionString___closed__3),
        core::ptr::addr_of_mut!(l_Lake_uiVersionString___closed__3_once),
        _init_l_Lake_uiVersionString___closed__3,
    );
    v___x_161_ = lean_string_append(v___x_160_, v___x_159_);
    return v___x_161_;
}
pub unsafe fn _init_l_Lake_uiVersionString___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_163_ = l_Lake_uiVersionString___closed__5;
    v___x_164_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_uiVersionString___closed__4),
        core::ptr::addr_of_mut!(l_Lake_uiVersionString___closed__4_once),
        _init_l_Lake_uiVersionString___closed__4,
    );
    v___x_165_ = lean_string_append(v___x_164_, v___x_163_);
    return v___x_165_;
}
pub unsafe fn _init_l_Lake_uiVersionString() -> *mut crate::leanh::LeanObject {
    let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_uiVersionString___closed__6),
        core::ptr::addr_of_mut!(l_Lake_uiVersionString___closed__6_once),
        _init_l_Lake_uiVersionString___closed__6,
    );
    return v___x_166_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Version(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_version_major = _init_l_Lake_version_major();
    crate::leanh::lean_mark_persistent(l_Lake_version_major);
    l_Lake_version_minor = _init_l_Lake_version_minor();
    crate::leanh::lean_mark_persistent(l_Lake_version_minor);
    l_Lake_version_patch = _init_l_Lake_version_patch();
    crate::leanh::lean_mark_persistent(l_Lake_version_patch);
    l_Lake_version_isRelease = _init_l_Lake_version_isRelease();
    l_Lake_version_specialDesc = _init_l_Lake_version_specialDesc();
    crate::leanh::lean_mark_persistent(l_Lake_version_specialDesc);
    l_Lake_versionStringCore = _init_l_Lake_versionStringCore();
    crate::leanh::lean_mark_persistent(l_Lake_versionStringCore);
    l_Lake_versionString = _init_l_Lake_versionString();
    crate::leanh::lean_mark_persistent(l_Lake_versionString);
    l_Lake_uiVersionString = _init_l_Lake_uiVersionString();
    crate::leanh::lean_mark_persistent(l_Lake_uiVersionString);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Version(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Version(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Version(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Version(builtin);
}
