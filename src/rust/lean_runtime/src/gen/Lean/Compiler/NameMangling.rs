// Lean compiler output
// Module: Lean.Compiler.NameMangling
// Imports: Lean.Setup Init.Data.String.TakeDrop Init.Data.UInt.Lemmas Init.Omega Init.Data.String.Lemmas.FindPos
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Char_ofNat, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Setup::{initialize_Lean_Setup, runtime_initialize_Lean_Setup};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{
    lean_nat_lor, lean_nat_shiftl, lean_nat_shiftr,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint32_land, lean_uint32_shift_left, lean_uint32_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint32_add, lean_uint32_of_nat, lean_uint32_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mod, lean_nat_mul,
    lean_nat_sub, lean_string_dec_eq, lean_string_utf8_byte_size, lean_uint32_dec_eq,
    lean_uint32_dec_le, lean_uint32_dec_lt, lean_uint32_to_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_3, lean_apply_4,
    lean_box, lean_box_uint32, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_uint32,
    lean_unsigned_to_nat,
};
pub static l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 85, 0],
};
static mut l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 117, 0],
};
static mut l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 120, 0],
};
static mut l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2_value
)
    as *mut LeanObject;
pub static l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 95, 0],
};
static mut l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3_value
)
    as *mut LeanObject;
pub static l_String_mangle___closed__0_value: LeanStringObject<1> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_String_mangle___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_mangle___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [48, 48, 0],
};
static mut l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [95, 0],
};
static mut l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1_value
) as *mut LeanObject;
pub static l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [95, 48, 48, 0],
};
static mut l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2_value
) as *mut LeanObject;
pub static l_Lean_mkMangledBoxedName___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 95, 95, 98, 111, 120, 101, 100, 0],
};
static mut l_Lean_mkMangledBoxedName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkMangledBoxedName___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkMangledBoxedName___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_mkMangledBoxedName___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkMangledBoxedName___closed__2_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [95, 48, 48, 95, 95, 98, 111, 120, 101, 100, 0],
};
static mut l_Lean_mkMangledBoxedName___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkMangledBoxedName___closed__2_value) as *mut LeanObject;
pub static l_Lean_mkModuleInitializationPrefix___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [114, 117, 110, 116, 105, 109, 101, 95, 0],
    };
static mut l_Lean_mkModuleInitializationPrefix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkModuleInitializationPrefix___closed__0_value) as *mut LeanObject;
pub static l_Lean_mkModuleInitializationPrefix___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [109, 101, 116, 97, 95, 0],
    };
static mut l_Lean_mkModuleInitializationPrefix___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkModuleInitializationPrefix___closed__1_value) as *mut LeanObject;
pub static l_Lean_mkModuleInitializationFunctionName___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 95, 0],
    };
static mut l_Lean_mkModuleInitializationFunctionName___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkModuleInitializationFunctionName___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_mkPackageSymbolPrefix___closed__0_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [108, 95, 0],
};
static mut l_Lean_mkPackageSymbolPrefix___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkPackageSymbolPrefix___closed__0_value) as *mut LeanObject;
pub static l_Lean_mkPackageSymbolPrefix___closed__1_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [108, 112, 95, 0],
};
static mut l_Lean_mkPackageSymbolPrefix___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_mkPackageSymbolPrefix___closed__1_value) as *mut LeanObject;
pub static mut l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(
    mut v_n_731_: u32,
) -> u32 {
    let mut v___x_732_: u32 = 0;
    let mut v___x_733_: u8 = 0;
    v___x_732_ = 10;
    v___x_733_ = lean_uint32_dec_lt(v_n_731_, v___x_732_);
    if v___x_733_ == 0 {
        let mut v___x_734_: u32 = 0;
        let mut v___x_735_: u32 = 0;
        v___x_734_ = 87;
        v___x_735_ = lean_uint32_add(v_n_731_, v___x_734_);
        return v___x_735_;
    } else {
        let mut v___x_736_: u32 = 0;
        let mut v___x_737_: u32 = 0;
        v___x_736_ = 48;
        v___x_737_ = lean_uint32_add(v_n_731_, v___x_736_);
        return v___x_737_;
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg___boxed(
    mut v_n_738_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_739_: u32 = 0;
    let mut v_res_740_: u32 = 0;
    let mut v_r_741_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_739_ = lean_unbox_uint32(v_n_738_);
    lean_dec(v_n_738_);
    v_res_740_ =
        l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(v_n_boxed_739_);
    v_r_741_ = lean_box_uint32(v_res_740_);
    return v_r_741_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_digitChar(
    mut v_n_742_: u32,
    mut v_h_743_: *mut LeanObject,
) -> u32 {
    let mut v___x_744_: u32 = 0;
    v___x_744_ = l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(v_n_742_);
    return v___x_744_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_digitChar___boxed(
    mut v_n_745_: *mut LeanObject,
    mut v_h_746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_boxed_747_: u32 = 0;
    let mut v_res_748_: u32 = 0;
    let mut v_r_749_: *mut LeanObject = core::ptr::null_mut();
    v_n_boxed_747_ = lean_unbox_uint32(v_n_745_);
    lean_dec(v_n_745_);
    v_res_748_ =
        l___private_Lean_Compiler_NameMangling_0__String_digitChar(v_n_boxed_747_, v_h_746_);
    v_r_749_ = lean_box_uint32(v_res_748_);
    return v_r_749_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_pushHex(
    mut v_n_750_: *mut LeanObject,
    mut v_val_751_: u32,
    mut v_s_752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_754_: u8 = 0;
    let mut v_one_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u32 = 0;
    let mut v___x_758_: u32 = 0;
    let mut v___x_759_: u32 = 0;
    let mut v___x_760_: u32 = 0;
    let mut v___x_761_: u32 = 0;
    let mut v_i_762_: u32 = 0;
    let mut v___x_763_: u32 = 0;
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_753_ = lean_unsigned_to_nat(0);
                v_isZero_754_ = lean_nat_dec_eq(v_n_750_, v_zero_753_);
                if v_isZero_754_ == 1 {
                    lean_dec(v_n_750_);
                    return v_s_752_;
                } else {
                    v_one_755_ = lean_unsigned_to_nat(1);
                    v_n_756_ = lean_nat_sub(v_n_750_, v_one_755_);
                    lean_dec(v_n_750_);
                    v___x_757_ = lean_uint32_of_nat(v_n_756_);
                    v___x_758_ = 2;
                    v___x_759_ = lean_uint32_shift_left(v___x_757_, v___x_758_);
                    v___x_760_ = lean_uint32_shift_right(v_val_751_, v___x_759_);
                    v___x_761_ = 15;
                    v_i_762_ = lean_uint32_land(v___x_760_, v___x_761_);
                    v___x_763_ =
                        l___private_Lean_Compiler_NameMangling_0__String_digitChar___redArg(
                            v_i_762_,
                        );
                    v___x_764_ = lean_string_push(v_s_752_, v___x_763_);
                    v_n_750_ = v_n_756_;
                    v_s_752_ = v___x_764_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_pushHex___boxed(
    mut v_n_766_: *mut LeanObject,
    mut v_val_767_: *mut LeanObject,
    mut v_s_768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_boxed_769_: u32 = 0;
    let mut v_res_770_: *mut LeanObject = core::ptr::null_mut();
    v_val_boxed_769_ = lean_unbox_uint32(v_val_767_);
    lean_dec(v_val_767_);
    v_res_770_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(
        v_n_766_,
        v_val_boxed_769_,
        v_s_768_,
    );
    return v_res_770_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_mangleAux(
    mut v_s_775_: *mut LeanObject,
    mut v_pos_776_: *mut LeanObject,
    mut v_r_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: u8 = 0;
    let mut v_c_780_: u32 = 0;
    let mut v_pos_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_786_: u8 = 0;
    let mut v___x_787_: u32 = 0;
    let mut v___x_788_: u8 = 0;
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: u8 = 0;
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: u8 = 0;
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_813_: u8 = 0;
    let mut v___x_814_: u32 = 0;
    let mut v___x_815_: u8 = 0;
    let mut v___x_816_: u32 = 0;
    let mut v___x_817_: u8 = 0;
    let mut v___x_819_: u32 = 0;
    let mut v___x_820_: u8 = 0;
    let mut v___x_821_: u32 = 0;
    let mut v___x_822_: u8 = 0;
    let mut v___x_823_: u32 = 0;
    let mut v___x_824_: u8 = 0;
    let mut v___x_825_: u32 = 0;
    let mut v___x_826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_778_ = lean_string_utf8_byte_size(v_s_775_);
                v___x_779_ = lean_nat_dec_eq(v_pos_776_, v___x_778_);
                if v___x_779_ == 0 {
                    v_c_780_ = lean_string_utf8_get_fast(v_s_775_, v_pos_776_);
                    v_pos_781_ = lean_string_utf8_next_fast(v_s_775_, v_pos_776_);
                    lean_dec(v_pos_776_);
                    v___x_823_ = 65;
                    v___x_824_ = lean_uint32_dec_le(v___x_823_, v_c_780_);
                    if v___x_824_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        v___x_825_ = 90;
                        v___x_826_ = lean_uint32_dec_le(v_c_780_, v___x_825_);
                        if v___x_826_ == 0 {
                            state = 4;
                            continue;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_pos_776_);
                    return v_r_777_;
                }
            }
            1 => {
                v___x_783_ = lean_string_push(v_r_777_, v_c_780_);
                v_pos_776_ = v_pos_781_;
                v_r_777_ = v___x_783_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_786_ == 0 {
                    v___x_787_ = 95;
                    v___x_788_ = lean_uint32_dec_eq(v_c_780_, v___x_787_);
                    if v___x_788_ == 0 {
                        v___x_789_ = lean_uint32_to_nat(v_c_780_);
                        v___x_790_ = lean_unsigned_to_nat(256);
                        v___x_791_ = lean_nat_dec_lt(v___x_789_, v___x_790_);
                        if v___x_791_ == 0 {
                            v___x_792_ = lean_unsigned_to_nat(65536);
                            v___x_793_ = lean_nat_dec_lt(v___x_789_, v___x_792_);
                            lean_dec(v___x_789_);
                            if v___x_793_ == 0 {
                                v___x_794_ = lean_unsigned_to_nat(8);
                                v___x_795_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__0;
                                v___x_796_ = lean_string_append(v_r_777_, v___x_795_);
                                v___x_797_ =
                                    l___private_Lean_Compiler_NameMangling_0__String_pushHex(
                                        v___x_794_, v_c_780_, v___x_796_,
                                    );
                                v_pos_776_ = v_pos_781_;
                                v_r_777_ = v___x_797_;
                                state = 0;
                                continue;
                            } else {
                                v___x_799_ = lean_unsigned_to_nat(4);
                                v___x_800_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
                                v___x_801_ = lean_string_append(v_r_777_, v___x_800_);
                                v___x_802_ =
                                    l___private_Lean_Compiler_NameMangling_0__String_pushHex(
                                        v___x_799_, v_c_780_, v___x_801_,
                                    );
                                v_pos_776_ = v_pos_781_;
                                v_r_777_ = v___x_802_;
                                state = 0;
                                continue;
                            }
                        } else {
                            lean_dec(v___x_789_);
                            v___x_804_ = lean_unsigned_to_nat(2);
                            v___x_805_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
                            v___x_806_ = lean_string_append(v_r_777_, v___x_805_);
                            v___x_807_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex(
                                v___x_804_, v_c_780_, v___x_806_,
                            );
                            v_pos_776_ = v_pos_781_;
                            v_r_777_ = v___x_807_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_809_ =
                            l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
                        v___x_810_ = lean_string_append(v_r_777_, v___x_809_);
                        v_pos_776_ = v_pos_781_;
                        v_r_777_ = v___x_810_;
                        state = 0;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_813_ == 0 {
                    v___x_814_ = 48;
                    v___x_815_ = lean_uint32_dec_le(v___x_814_, v_c_780_);
                    if v___x_815_ == 0 {
                        v___y_786_ = v___x_815_;
                        state = 2;
                        continue;
                    } else {
                        v___x_816_ = 57;
                        v___x_817_ = lean_uint32_dec_le(v_c_780_, v___x_816_);
                        v___y_786_ = v___x_817_;
                        state = 2;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_819_ = 97;
                v___x_820_ = lean_uint32_dec_le(v___x_819_, v_c_780_);
                if v___x_820_ == 0 {
                    v___y_813_ = v___x_820_;
                    state = 3;
                    continue;
                } else {
                    v___x_821_ = 122;
                    v___x_822_ = lean_uint32_dec_le(v_c_780_, v___x_821_);
                    v___y_813_ = v___x_822_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_mangleAux___boxed(
    mut v_s_827_: *mut LeanObject,
    mut v_pos_828_: *mut LeanObject,
    mut v_r_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_830_: *mut LeanObject = core::ptr::null_mut();
    v_res_830_ =
        l___private_Lean_Compiler_NameMangling_0__String_mangleAux(v_s_827_, v_pos_828_, v_r_829_);
    lean_dec_ref(v_s_827_);
    return v_res_830_;
}
pub unsafe fn l_String_mangle(mut v_s_832_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    v___x_833_ = lean_unsigned_to_nat(0);
    v___x_834_ = l_String_mangle___closed__0;
    v___x_835_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(
        v_s_832_, v___x_833_, v___x_834_,
    );
    return v___x_835_;
}
pub unsafe fn l_String_mangle___boxed(mut v_s_836_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_837_: *mut LeanObject = core::ptr::null_mut();
    v_res_837_ = l_String_mangle(v_s_836_);
    lean_dec_ref(v_s_836_);
    return v_res_837_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(
    mut v_x_838_: *mut LeanObject,
    mut v_x_839_: *mut LeanObject,
    mut v_x_840_: *mut LeanObject,
) -> u8 {
    let mut v_zero_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_842_: u8 = 0;
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v_one_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_851_: u8 = 0;
    let mut v_ch_852_: u32 = 0;
    let mut v___y_854_: u8 = 0;
    let mut v___x_855_: u32 = 0;
    let mut v___x_856_: u8 = 0;
    let mut v___x_857_: u32 = 0;
    let mut v___x_858_: u8 = 0;
    let mut v___x_859_: u32 = 0;
    let mut v___x_860_: u8 = 0;
    let mut v___x_861_: u32 = 0;
    let mut v___x_862_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_841_ = lean_unsigned_to_nat(0);
                v_isZero_842_ = lean_nat_dec_eq(v_x_838_, v_zero_841_);
                if v_isZero_842_ == 1 {
                    lean_dec(v_x_840_);
                    lean_dec(v_x_838_);
                    return v_isZero_842_;
                } else {
                    v___x_843_ = lean_string_utf8_byte_size(v_x_839_);
                    v___x_844_ = lean_nat_dec_eq(v_x_840_, v___x_843_);
                    if v___x_844_ == 0 {
                        v_one_845_ = lean_unsigned_to_nat(1);
                        v_n_846_ = lean_nat_sub(v_x_838_, v_one_845_);
                        lean_dec(v_x_838_);
                        v_ch_852_ = lean_string_utf8_get_fast(v_x_839_, v_x_840_);
                        v___x_859_ = 48;
                        v___x_860_ = lean_uint32_dec_le(v___x_859_, v_ch_852_);
                        if v___x_860_ == 0 {
                            v___y_854_ = v___x_860_;
                            state = 3;
                            continue;
                        } else {
                            v___x_861_ = 57;
                            v___x_862_ = lean_uint32_dec_le(v_ch_852_, v___x_861_);
                            v___y_854_ = v___x_862_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_x_840_);
                        lean_dec(v_x_838_);
                        return v_isZero_842_;
                    }
                }
            }
            1 => {
                v___x_848_ = lean_string_utf8_next_fast(v_x_839_, v_x_840_);
                lean_dec(v_x_840_);
                v_x_838_ = v_n_846_;
                v_x_840_ = v___x_848_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_851_ == 0 {
                    lean_dec(v_n_846_);
                    lean_dec(v_x_840_);
                    return v___y_851_;
                } else {
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v___y_854_ == 0 {
                    v___x_855_ = 97;
                    v___x_856_ = lean_uint32_dec_le(v___x_855_, v_ch_852_);
                    if v___x_856_ == 0 {
                        v___y_851_ = v___x_856_;
                        state = 2;
                        continue;
                    } else {
                        v___x_857_ = 102;
                        v___x_858_ = lean_uint32_dec_le(v_ch_852_, v___x_857_);
                        v___y_851_ = v___x_858_;
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
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex___boxed(
    mut v_x_863_: *mut LeanObject,
    mut v_x_864_: *mut LeanObject,
    mut v_x_865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_866_: u8 = 0;
    let mut v_r_867_: *mut LeanObject = core::ptr::null_mut();
    v_res_866_ =
        l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v_x_863_, v_x_864_, v_x_865_);
    lean_dec_ref(v_x_864_);
    v_r_867_ = lean_box((v_res_866_) as usize);
    return v_r_867_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(
    mut v_c_868_: u32,
) -> *mut LeanObject {
    let mut v___y_870_: u8 = 0;
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: u32 = 0;
    let mut v___x_873_: u32 = 0;
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_877_: u8 = 0;
    let mut v___x_878_: u32 = 0;
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: u32 = 0;
    let mut v___x_881_: u8 = 0;
    let mut v___x_882_: u32 = 0;
    let mut v___x_883_: u32 = 0;
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: u32 = 0;
    let mut v___x_887_: u8 = 0;
    let mut v___x_888_: u32 = 0;
    let mut v___x_889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_886_ = 48;
                v___x_887_ = lean_uint32_dec_le(v___x_886_, v_c_868_);
                if v___x_887_ == 0 {
                    v___y_877_ = v___x_887_;
                    state = 2;
                    continue;
                } else {
                    v___x_888_ = 57;
                    v___x_889_ = lean_uint32_dec_le(v_c_868_, v___x_888_);
                    v___y_877_ = v___x_889_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_870_ == 0 {
                    v___x_871_ = lean_box(0);
                    return v___x_871_;
                } else {
                    v___x_872_ = 87;
                    v___x_873_ = lean_uint32_sub(v_c_868_, v___x_872_);
                    v___x_874_ = lean_uint32_to_nat(v___x_873_);
                    v___x_875_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_875_, 0, v___x_874_);
                    return v___x_875_;
                }
            }
            2 => {
                if v___y_877_ == 0 {
                    v___x_878_ = 97;
                    v___x_879_ = lean_uint32_dec_le(v___x_878_, v_c_868_);
                    if v___x_879_ == 0 {
                        v___y_870_ = v___x_879_;
                        state = 1;
                        continue;
                    } else {
                        v___x_880_ = 102;
                        v___x_881_ = lean_uint32_dec_le(v_c_868_, v___x_880_);
                        v___y_870_ = v___x_881_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_882_ = 48;
                    v___x_883_ = lean_uint32_sub(v_c_868_, v___x_882_);
                    v___x_884_ = lean_uint32_to_nat(v___x_883_);
                    v___x_885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_885_, 0, v___x_884_);
                    return v___x_885_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f___boxed(
    mut v_c_890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_c_boxed_891_: u32 = 0;
    let mut v_res_892_: *mut LeanObject = core::ptr::null_mut();
    v_c_boxed_891_ = lean_unbox_uint32(v_c_890_);
    lean_dec(v_c_890_);
    v_res_892_ = l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v_c_boxed_891_);
    return v_res_892_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(
    mut v_k_893_: *mut LeanObject,
    mut v_s_894_: *mut LeanObject,
    mut v_p_895_: *mut LeanObject,
    mut v_acc_896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_898_: u8 = 0;
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: u32 = 0;
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_897_ = lean_unsigned_to_nat(0);
                v_isZero_898_ = lean_nat_dec_eq(v_k_893_, v_zero_897_);
                if v_isZero_898_ == 1 {
                    lean_dec(v_k_893_);
                    v___x_899_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_899_, 0, v_p_895_);
                    lean_ctor_set(v___x_899_, 1, v_acc_896_);
                    v___x_900_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_900_, 0, v___x_899_);
                    return v___x_900_;
                } else {
                    v___x_901_ = lean_string_utf8_byte_size(v_s_894_);
                    v___x_902_ = lean_nat_dec_eq(v_p_895_, v___x_901_);
                    if v___x_902_ == 0 {
                        v___x_903_ = lean_string_utf8_get_fast(v_s_894_, v_p_895_);
                        v___x_904_ =
                            l___private_Lean_Compiler_NameMangling_0__Lean_fromHex_x3f(v___x_903_);
                        if lean_obj_tag(v___x_904_) == 0 {
                            lean_dec(v_acc_896_);
                            lean_dec(v_p_895_);
                            lean_dec(v_k_893_);
                            v___x_905_ = lean_box(0);
                            return v___x_905_;
                        } else {
                            v_val_906_ = lean_ctor_get(v___x_904_, 0);
                            lean_inc(v_val_906_);
                            lean_dec_ref_known(v___x_904_, 1);
                            v_one_907_ = lean_unsigned_to_nat(1);
                            v_n_908_ = lean_nat_sub(v_k_893_, v_one_907_);
                            lean_dec(v_k_893_);
                            v___x_909_ = lean_string_utf8_next_fast(v_s_894_, v_p_895_);
                            lean_dec(v_p_895_);
                            v___x_910_ = lean_unsigned_to_nat(4);
                            v___x_911_ = lean_nat_shiftl(v_acc_896_, v___x_910_);
                            lean_dec(v_acc_896_);
                            v___x_912_ = lean_nat_lor(v___x_911_, v_val_906_);
                            lean_dec(v_val_906_);
                            lean_dec(v___x_911_);
                            v_k_893_ = v_n_908_;
                            v_p_895_ = v___x_909_;
                            v_acc_896_ = v___x_912_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_acc_896_);
                        lean_dec(v_p_895_);
                        lean_dec(v_k_893_);
                        v___x_914_ = lean_box(0);
                        return v___x_914_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f___boxed(
    mut v_k_915_: *mut LeanObject,
    mut v_s_916_: *mut LeanObject,
    mut v_p_917_: *mut LeanObject,
    mut v_acc_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_919_: *mut LeanObject = core::ptr::null_mut();
    v_res_919_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(
        v_k_915_, v_s_916_, v_p_917_, v_acc_918_,
    );
    lean_dec_ref(v_s_916_);
    return v_res_919_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(
    mut v_n_920_: *mut LeanObject,
    mut v_h__1_921_: *mut LeanObject,
    mut v_h__2_922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_924_: u8 = 0;
    v_zero_923_ = lean_unsigned_to_nat(0);
    v_isZero_924_ = lean_nat_dec_eq(v_n_920_, v_zero_923_);
    if v_isZero_924_ == 1 {
        let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_922_);
        v___x_925_ = lean_box(0);
        v___x_926_ = lean_apply_1(v_h__1_921_, v___x_925_);
        return v___x_926_;
    } else {
        let mut v_one_927_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_921_);
        v_one_927_ = lean_unsigned_to_nat(1);
        v_n_928_ = lean_nat_sub(v_n_920_, v_one_927_);
        v___x_929_ = lean_apply_1(v_h__2_922_, v_n_928_);
        return v___x_929_;
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg___boxed(
    mut v_n_930_: *mut LeanObject,
    mut v_h__1_931_: *mut LeanObject,
    mut v_h__2_932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_933_: *mut LeanObject = core::ptr::null_mut();
    v_res_933_ =
        l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___redArg(
            v_n_930_,
            v_h__1_931_,
            v_h__2_932_,
        );
    lean_dec(v_n_930_);
    return v_res_933_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(
    mut v_motive_934_: *mut LeanObject,
    mut v_n_935_: *mut LeanObject,
    mut v_h__1_936_: *mut LeanObject,
    mut v_h__2_937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_939_: u8 = 0;
    v_zero_938_ = lean_unsigned_to_nat(0);
    v_isZero_939_ = lean_nat_dec_eq(v_n_935_, v_zero_938_);
    if v_isZero_939_ == 1 {
        let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_937_);
        v___x_940_ = lean_box(0);
        v___x_941_ = lean_apply_1(v_h__1_936_, v___x_940_);
        return v___x_941_;
    } else {
        let mut v_one_942_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_936_);
        v_one_942_ = lean_unsigned_to_nat(1);
        v_n_943_ = lean_nat_sub(v_n_935_, v_one_942_);
        v___x_944_ = lean_apply_1(v_h__2_937_, v_n_943_);
        return v___x_944_;
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter___boxed(
    mut v_motive_945_: *mut LeanObject,
    mut v_n_946_: *mut LeanObject,
    mut v_h__1_947_: *mut LeanObject,
    mut v_h__2_948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_949_: *mut LeanObject = core::ptr::null_mut();
    v_res_949_ = l___private_Lean_Compiler_NameMangling_0__String_pushHex_match__1_splitter(
        v_motive_945_,
        v_n_946_,
        v_h__1_947_,
        v_h__2_948_,
    );
    lean_dec(v_n_946_);
    return v_res_949_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter___redArg(
    mut v_x_950_: *mut LeanObject,
    mut v_h__1_951_: *mut LeanObject,
    mut v_h__2_952_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_950_) == 0 {
        let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_951_);
        v___x_953_ = lean_box(0);
        v___x_954_ = lean_apply_1(v_h__2_952_, v___x_953_);
        return v___x_954_;
    } else {
        let mut v_val_955_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_952_);
        v_val_955_ = lean_ctor_get(v_x_950_, 0);
        lean_inc(v_val_955_);
        lean_dec_ref_known(v_x_950_, 1);
        v___x_956_ = lean_apply_1(v_h__1_951_, v_val_955_);
        return v___x_956_;
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f_match__1_splitter(
    mut v_motive_957_: *mut LeanObject,
    mut v_x_958_: *mut LeanObject,
    mut v_h__1_959_: *mut LeanObject,
    mut v_h__2_960_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_958_) == 0 {
        let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_959_);
        v___x_961_ = lean_box(0);
        v___x_962_ = lean_apply_1(v_h__2_960_, v___x_961_);
        return v___x_962_;
    } else {
        let mut v_val_963_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_960_);
        v_val_963_ = lean_ctor_get(v_x_958_, 0);
        lean_inc(v_val_963_);
        lean_dec_ref_known(v_x_958_, 1);
        v___x_964_ = lean_apply_1(v_h__1_959_, v_val_963_);
        return v___x_964_;
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(
    mut v_s_965_: *mut LeanObject,
    mut v_p_966_: *mut LeanObject,
) -> u8 {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: u8 = 0;
    let mut v_b_969_: u32 = 0;
    let mut v___x_970_: u32 = 0;
    let mut v___x_971_: u8 = 0;
    let mut v___x_972_: u32 = 0;
    let mut v___x_973_: u8 = 0;
    let mut v___x_974_: u32 = 0;
    let mut v___x_975_: u8 = 0;
    let mut v___x_976_: u32 = 0;
    let mut v___x_977_: u8 = 0;
    let mut v___x_978_: u32 = 0;
    let mut v___x_979_: u8 = 0;
    let mut v___x_980_: u32 = 0;
    let mut v___x_981_: u8 = 0;
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u8 = 0;
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: u8 = 0;
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_967_ = lean_string_utf8_byte_size(v_s_965_);
                v___x_968_ = lean_nat_dec_eq(v_p_966_, v___x_967_);
                if v___x_968_ == 0 {
                    v_b_969_ = lean_string_utf8_get_fast(v_s_965_, v_p_966_);
                    v___x_970_ = 95;
                    v___x_971_ = lean_uint32_dec_eq(v_b_969_, v___x_970_);
                    if v___x_971_ == 0 {
                        v___x_972_ = 120;
                        v___x_973_ = lean_uint32_dec_eq(v_b_969_, v___x_972_);
                        if v___x_973_ == 0 {
                            v___x_974_ = 117;
                            v___x_975_ = lean_uint32_dec_eq(v_b_969_, v___x_974_);
                            if v___x_975_ == 0 {
                                v___x_976_ = 85;
                                v___x_977_ = lean_uint32_dec_eq(v_b_969_, v___x_976_);
                                if v___x_977_ == 0 {
                                    lean_dec(v_p_966_);
                                    v___x_978_ = 48;
                                    v___x_979_ = lean_uint32_dec_le(v___x_978_, v_b_969_);
                                    if v___x_979_ == 0 {
                                        return v___x_979_;
                                    } else {
                                        v___x_980_ = 57;
                                        v___x_981_ = lean_uint32_dec_le(v_b_969_, v___x_980_);
                                        return v___x_981_;
                                    }
                                } else {
                                    v___x_982_ = lean_unsigned_to_nat(8);
                                    v___x_983_ = lean_string_utf8_next_fast(v_s_965_, v_p_966_);
                                    lean_dec(v_p_966_);
                                    v___x_984_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(v___x_982_, v_s_965_, v___x_983_);
                                    return v___x_984_;
                                }
                            } else {
                                v___x_985_ = lean_unsigned_to_nat(4);
                                v___x_986_ = lean_string_utf8_next_fast(v_s_965_, v_p_966_);
                                lean_dec(v_p_966_);
                                v___x_987_ =
                                    l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(
                                        v___x_985_, v_s_965_, v___x_986_,
                                    );
                                return v___x_987_;
                            }
                        } else {
                            v___x_988_ = lean_unsigned_to_nat(2);
                            v___x_989_ = lean_string_utf8_next_fast(v_s_965_, v_p_966_);
                            lean_dec(v_p_966_);
                            v___x_990_ =
                                l___private_Lean_Compiler_NameMangling_0__Lean_checkLowerHex(
                                    v___x_988_, v_s_965_, v___x_989_,
                                );
                            return v___x_990_;
                        }
                    } else {
                        v___x_991_ = lean_string_utf8_next_fast(v_s_965_, v_p_966_);
                        lean_dec(v_p_966_);
                        v_p_966_ = v___x_991_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_p_966_);
                    return v___x_968_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation___boxed(
    mut v_s_993_: *mut LeanObject,
    mut v_p_994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_995_: u8 = 0;
    let mut v_r_996_: *mut LeanObject = core::ptr::null_mut();
    v_res_995_ =
        l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(v_s_993_, v_p_994_);
    lean_dec_ref(v_s_993_);
    v_r_996_ = lean_box((v_res_995_) as usize);
    return v_r_996_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(
    mut v_prev_997_: *mut LeanObject,
    mut v_next_998_: *mut LeanObject,
) -> u8 {
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    let mut v_str_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: u8 = 0;
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: u32 = 0;
    let mut v___x_1011_: u32 = 0;
    let mut v___x_1012_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_prev_997_) == 1 {
                    v_str_1002_ = lean_ctor_get(v_prev_997_, 1);
                    v___x_1003_ = lean_string_utf8_byte_size(v_str_1002_);
                    v___x_1004_ = lean_unsigned_to_nat(0);
                    v___x_1005_ = lean_nat_dec_eq(v___x_1003_, v___x_1004_);
                    if v___x_1005_ == 0 {
                        lean_inc_ref(v_str_1002_);
                        v___x_1006_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v___x_1006_, 0, v_str_1002_);
                        lean_ctor_set(v___x_1006_, 1, v___x_1004_);
                        lean_ctor_set(v___x_1006_, 2, v___x_1003_);
                        v___x_1007_ = lean_unsigned_to_nat(1);
                        v___x_1008_ = lean_nat_sub(v___x_1003_, v___x_1007_);
                        v___x_1009_ = l_String_Slice_posLE(v___x_1006_, v___x_1008_);
                        lean_dec_ref_known(v___x_1006_, 3);
                        v___x_1010_ = lean_string_utf8_get_fast(v_str_1002_, v___x_1009_);
                        lean_dec(v___x_1009_);
                        v___x_1011_ = 95;
                        v___x_1012_ = lean_uint32_dec_eq(v___x_1010_, v___x_1011_);
                        if v___x_1012_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            return v___x_1012_;
                        }
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1000_ = lean_unsigned_to_nat(0);
                v___x_1001_ = l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(
                    v_next_998_,
                    v___x_1000_,
                );
                return v___x_1001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation___boxed(
    mut v_prev_1013_: *mut LeanObject,
    mut v_next_1014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1015_: u8 = 0;
    let mut v_r_1016_: *mut LeanObject = core::ptr::null_mut();
    v_res_1015_ = l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(
        v_prev_1013_,
        v_next_1014_,
    );
    lean_dec_ref(v_next_1014_);
    lean_dec(v_prev_1013_);
    v_r_1016_ = lean_box((v_res_1015_) as usize);
    return v_r_1016_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(
    mut v_x_1020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: u8 = 0;
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_m1_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: u8 = 0;
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_i_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_1020_) {
                0 => {
                    v___x_1021_ = l_String_mangle___closed__0;
                    return v___x_1021_;
                }
                1 => {
                    v_pre_1022_ = lean_ctor_get(v_x_1020_, 0);
                    lean_inc(v_pre_1022_);
                    v_str_1023_ = lean_ctor_get(v_x_1020_, 1);
                    lean_inc_ref(v_str_1023_);
                    lean_dec_ref_known(v_x_1020_, 2);
                    v_m_1024_ = l_String_mangle(v_str_1023_);
                    lean_dec_ref(v_str_1023_);
                    if lean_obj_tag(v_pre_1022_) == 0 {
                        v___x_1025_ = lean_unsigned_to_nat(0);
                        v___x_1026_ =
                            l___private_Lean_Compiler_NameMangling_0__Lean_checkDisambiguation(
                                v_m_1024_,
                                v___x_1025_,
                            );
                        if v___x_1026_ == 0 {
                            return v_m_1024_;
                        } else {
                            v___x_1027_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__0;
                            v___x_1028_ = lean_string_append(v___x_1027_, v_m_1024_);
                            lean_dec_ref(v_m_1024_);
                            return v___x_1028_;
                        }
                    } else {
                        lean_inc(v_pre_1022_);
                        v_m1_1029_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(
                            v_pre_1022_,
                        );
                        v___x_1034_ =
                            l___private_Lean_Compiler_NameMangling_0__Lean_needDisambiguation(
                                v_pre_1022_,
                                v_m_1024_,
                            );
                        lean_dec(v_pre_1022_);
                        if v___x_1034_ == 0 {
                            v___x_1035_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
                            v___y_1031_ = v___x_1035_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1036_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__2;
                            v___y_1031_ = v___x_1036_;
                            state = 1;
                            continue;
                        }
                    }
                }
                _ => {
                    v_pre_1037_ = lean_ctor_get(v_x_1020_, 0);
                    if lean_obj_tag(v_pre_1037_) == 0 {
                        v_i_1038_ = lean_ctor_get(v_x_1020_, 1);
                        lean_inc(v_i_1038_);
                        lean_dec_ref_known(v_x_1020_, 2);
                        v___x_1039_ = l_Nat_reprFast(v_i_1038_);
                        v___x_1040_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
                        v___x_1041_ = lean_string_append(v___x_1039_, v___x_1040_);
                        return v___x_1041_;
                    } else {
                        lean_inc(v_pre_1037_);
                        v_i_1042_ = lean_ctor_get(v_x_1020_, 1);
                        lean_inc(v_i_1042_);
                        lean_dec_ref_known(v_x_1020_, 2);
                        v___x_1043_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(
                            v_pre_1037_,
                        );
                        v___x_1044_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
                        v___x_1045_ = lean_string_append(v___x_1043_, v___x_1044_);
                        v___x_1046_ = l_Nat_reprFast(v_i_1042_);
                        v___x_1047_ = lean_string_append(v___x_1045_, v___x_1046_);
                        lean_dec_ref(v___x_1046_);
                        v___x_1048_ = lean_string_append(v___x_1047_, v___x_1044_);
                        return v___x_1048_;
                    }
                }
            },
            1 => {
                v___x_1032_ = lean_string_append(v_m1_1029_, v___y_1031_);
                v___x_1033_ = lean_string_append(v___x_1032_, v_m_1024_);
                lean_dec_ref(v_m_1024_);
                return v___x_1033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Name_mangle(
    mut v_n_1049_: *mut LeanObject,
    mut v_pre_1050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    v___x_1051_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_1049_);
    v___x_1052_ = lean_string_append(v_pre_1050_, v___x_1051_);
    lean_dec_ref(v___x_1051_);
    return v___x_1052_;
}
pub unsafe fn _init_l_Lean_mkMangledBoxedName___closed__1() -> *mut LeanObject {
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    v___x_1054_ = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
    v___x_1055_ = lean_string_utf8_byte_size(v___x_1054_);
    return v___x_1055_;
}
pub unsafe fn lean_mk_mangled_boxed_name(mut v_s_1057_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: u8 = 0;
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: u8 = 0;
    let mut v___x_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1061_ =
                    l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
                v___x_1062_ = lean_string_utf8_byte_size(v_s_1057_);
                v___x_1063_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_mkMangledBoxedName___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_mkMangledBoxedName___closed__1_once),
                    _init_l_Lean_mkMangledBoxedName___closed__1,
                );
                v___x_1064_ = lean_nat_dec_le(v___x_1063_, v___x_1062_);
                if v___x_1064_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1065_ = lean_unsigned_to_nat(0);
                    v___x_1066_ = lean_nat_sub(v___x_1062_, v___x_1063_);
                    v___x_1067_ = lean_string_memcmp(
                        v_s_1057_,
                        v___x_1061_,
                        v___x_1066_,
                        v___x_1065_,
                        v___x_1063_,
                    );
                    lean_dec(v___x_1066_);
                    if v___x_1067_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1068_ = l_Lean_mkMangledBoxedName___closed__2;
                        v___x_1069_ = lean_string_append(v_s_1057_, v___x_1068_);
                        return v___x_1069_;
                    }
                }
            }
            1 => {
                v___x_1059_ = l_Lean_mkMangledBoxedName___closed__0;
                v___x_1060_ = lean_string_append(v_s_1057_, v___x_1059_);
                return v___x_1060_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkModuleInitializationStem(
    mut v_moduleName_1070_: *mut LeanObject,
    mut v_pkg_x3f_1071_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_pkg_x3f_1071_) == 0 {
        let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
        v___x_1072_ = l_String_mangle___closed__0;
        v___x_1073_ = l_Lean_Name_mangle(v_moduleName_1070_, v___x_1072_);
        return v___x_1073_;
    } else {
        let mut v_val_1074_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
        v_val_1074_ = lean_ctor_get(v_pkg_x3f_1071_, 0);
        v___x_1075_ = l_String_mangle(v_val_1074_);
        v___x_1076_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
        v___x_1077_ = lean_string_append(v___x_1075_, v___x_1076_);
        v___x_1078_ = l_Lean_Name_mangle(v_moduleName_1070_, v___x_1077_);
        return v___x_1078_;
    }
}
pub unsafe fn l_Lean_mkModuleInitializationStem___boxed(
    mut v_moduleName_1079_: *mut LeanObject,
    mut v_pkg_x3f_1080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1081_: *mut LeanObject = core::ptr::null_mut();
    v_res_1081_ = l_Lean_mkModuleInitializationStem(v_moduleName_1079_, v_pkg_x3f_1080_);
    lean_dec(v_pkg_x3f_1080_);
    return v_res_1081_;
}
pub unsafe fn l_Lean_mkModuleInitializationPrefix(mut v_phases_1084_: u8) -> *mut LeanObject {
    match v_phases_1084_ {
        0 => {
            let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
            v___x_1085_ = l_Lean_mkModuleInitializationPrefix___closed__0;
            return v___x_1085_;
        }
        1 => {
            let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
            v___x_1086_ = l_Lean_mkModuleInitializationPrefix___closed__1;
            return v___x_1086_;
        }
        _ => {
            let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
            v___x_1087_ = l_String_mangle___closed__0;
            return v___x_1087_;
        }
    }
}
pub unsafe fn l_Lean_mkModuleInitializationPrefix___boxed(
    mut v_phases_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phases_boxed_1089_: u8 = 0;
    let mut v_res_1090_: *mut LeanObject = core::ptr::null_mut();
    v_phases_boxed_1089_ = (lean_unbox(v_phases_1088_) as u8);
    v_res_1090_ = l_Lean_mkModuleInitializationPrefix(v_phases_boxed_1089_);
    return v_res_1090_;
}
pub unsafe fn l_Lean_mkModuleInitializationFunctionName(
    mut v_moduleName_1092_: *mut LeanObject,
    mut v_pkg_x3f_1093_: *mut LeanObject,
    mut v_phases_1094_: u8,
) -> *mut LeanObject {
    let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    v___x_1095_ = l_Lean_mkModuleInitializationPrefix(v_phases_1094_);
    v___x_1096_ = l_Lean_mkModuleInitializationFunctionName___closed__0;
    v___x_1097_ = lean_string_append(v___x_1095_, v___x_1096_);
    v___x_1098_ = l_Lean_mkModuleInitializationStem(v_moduleName_1092_, v_pkg_x3f_1093_);
    v___x_1099_ = lean_string_append(v___x_1097_, v___x_1098_);
    lean_dec_ref(v___x_1098_);
    return v___x_1099_;
}
pub unsafe fn l_Lean_mkModuleInitializationFunctionName___boxed(
    mut v_moduleName_1100_: *mut LeanObject,
    mut v_pkg_x3f_1101_: *mut LeanObject,
    mut v_phases_1102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_phases_boxed_1103_: u8 = 0;
    let mut v_res_1104_: *mut LeanObject = core::ptr::null_mut();
    v_phases_boxed_1103_ = (lean_unbox(v_phases_1102_) as u8);
    v_res_1104_ = l_Lean_mkModuleInitializationFunctionName(
        v_moduleName_1100_,
        v_pkg_x3f_1101_,
        v_phases_boxed_1103_,
    );
    lean_dec(v_pkg_x3f_1101_);
    return v_res_1104_;
}
pub unsafe fn l_Lean_mkPackageSymbolPrefix(
    mut v_pkg_x3f_1107_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_pkg_x3f_1107_) == 0 {
        let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
        v___x_1108_ = l_Lean_mkPackageSymbolPrefix___closed__0;
        return v___x_1108_;
    } else {
        let mut v_val_1109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
        v_val_1109_ = lean_ctor_get(v_pkg_x3f_1107_, 0);
        v___x_1110_ = l_Lean_mkPackageSymbolPrefix___closed__1;
        v___x_1111_ = l_String_mangle(v_val_1109_);
        v___x_1112_ = lean_string_append(v___x_1110_, v___x_1111_);
        lean_dec_ref(v___x_1111_);
        v___x_1113_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
        v___x_1114_ = lean_string_append(v___x_1112_, v___x_1113_);
        return v___x_1114_;
    }
}
pub unsafe fn l_Lean_mkPackageSymbolPrefix___boxed(
    mut v_pkg_x3f_1115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1116_: *mut LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Lean_mkPackageSymbolPrefix(v_pkg_x3f_1115_);
    lean_dec(v_pkg_x3f_1115_);
    return v_res_1116_;
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(
    mut v_x_1117_: *mut LeanObject,
    mut v_x_1118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1120_: u8 = 0;
    let mut v___x_1121_: u32 = 0;
    let mut v_one_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1119_ = lean_unsigned_to_nat(0);
                v_isZero_1120_ = lean_nat_dec_eq(v_x_1117_, v_zero_1119_);
                if v_isZero_1120_ == 1 {
                    lean_dec(v_x_1117_);
                    return v_x_1118_;
                } else {
                    v___x_1121_ = 95;
                    v_one_1122_ = lean_unsigned_to_nat(1);
                    v_n_1123_ = lean_nat_sub(v_x_1117_, v_one_1122_);
                    lean_dec(v_x_1117_);
                    v___x_1124_ = lean_string_push(v_x_1118_, v___x_1121_);
                    v_x_1117_ = v_n_1123_;
                    v_x_1118_ = v___x_1124_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(
    mut v_s_1126_: *mut LeanObject,
    mut v_p_u2080_1127_: *mut LeanObject,
    mut v_res_1128_: *mut LeanObject,
    mut v_acc_1129_: *mut LeanObject,
    mut v_ucount_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: u8 = 0;
    let mut v_ch_1133_: u32 = 0;
    let mut v_p_1134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: u32 = 0;
    let mut v___x_1138_: u32 = 0;
    let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: u32 = 0;
    let mut v___x_1142_: u8 = 0;
    let mut v___x_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: u32 = 0;
    let mut v___x_1156_: u8 = 0;
    let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: u32 = 0;
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u32 = 0;
    let mut v___x_1170_: u8 = 0;
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: u32 = 0;
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1184_: u8 = 0;
    let mut v___x_1185_: u32 = 0;
    let mut v___x_1186_: u32 = 0;
    let mut v___x_1187_: u8 = 0;
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1192_: u8 = 0;
    let mut v___x_1193_: u32 = 0;
    let mut v___x_1194_: u8 = 0;
    let mut v___x_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_acc_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: u32 = 0;
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1209_: u32 = 0;
    let mut v___x_1210_: u8 = 0;
    let mut v___x_1211_: u8 = 0;
    let mut v___x_1212_: u8 = 0;
    let mut v___x_1213_: u32 = 0;
    let mut v___x_1214_: u8 = 0;
    let mut v___x_1215_: u32 = 0;
    let mut v___x_1216_: u8 = 0;
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1131_ = lean_string_utf8_byte_size(v_s_1126_);
                v___x_1132_ = lean_nat_dec_eq(v_p_u2080_1127_, v___x_1131_);
                if v___x_1132_ == 0 {
                    v_ch_1133_ = lean_string_utf8_get_fast(v_s_1126_, v_p_u2080_1127_);
                    v_p_1134_ = lean_string_utf8_next_fast(v_s_1126_, v_p_u2080_1127_);
                    lean_dec(v_p_u2080_1127_);
                    v___x_1141_ = 95;
                    v___x_1142_ = lean_uint32_dec_eq(v_ch_1133_, v___x_1141_);
                    if v___x_1142_ == 0 {
                        v___x_1143_ = lean_unsigned_to_nat(2);
                        v___x_1144_ = lean_nat_mod(v_ucount_1130_, v___x_1143_);
                        v___x_1145_ = lean_unsigned_to_nat(0);
                        v___x_1212_ = lean_nat_dec_eq(v___x_1144_, v___x_1145_);
                        lean_dec(v___x_1144_);
                        if v___x_1212_ == 0 {
                            v___x_1213_ = 48;
                            v___x_1214_ = lean_uint32_dec_le(v___x_1213_, v_ch_1133_);
                            if v___x_1214_ == 0 {
                                v___y_1192_ = v___x_1214_;
                                state = 6;
                                continue;
                            } else {
                                v___x_1215_ = 57;
                                v___x_1216_ = lean_uint32_dec_le(v_ch_1133_, v___x_1215_);
                                v___y_1192_ = v___x_1216_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v___x_1217_ = lean_unsigned_to_nat(1);
                            v___x_1218_ = lean_nat_shiftr(v_ucount_1130_, v___x_1217_);
                            lean_dec(v_ucount_1130_);
                            v___x_1219_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_1218_, v_acc_1129_);
                            v___x_1220_ = lean_string_push(v___x_1219_, v_ch_1133_);
                            v_p_u2080_1127_ = v_p_1134_;
                            v_acc_1129_ = v___x_1220_;
                            v_ucount_1130_ = v___x_1145_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_1222_ = lean_unsigned_to_nat(1);
                        v___x_1223_ = lean_nat_add(v_ucount_1130_, v___x_1222_);
                        lean_dec(v_ucount_1130_);
                        v_p_u2080_1127_ = v_p_1134_;
                        v_ucount_1130_ = v___x_1223_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec(v_p_u2080_1127_);
                    v___x_1225_ = lean_unsigned_to_nat(1);
                    v___x_1226_ = lean_nat_shiftr(v_ucount_1130_, v___x_1225_);
                    lean_dec(v_ucount_1130_);
                    v___x_1227_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_1226_, v_acc_1129_);
                    v___x_1228_ = l_Lean_Name_str___override(v_res_1128_, v___x_1227_);
                    return v___x_1228_;
                }
            }
            1 => {
                v___x_1137_ = 48;
                v___x_1138_ = lean_uint32_sub(v_ch_1133_, v___x_1137_);
                v___x_1139_ = lean_uint32_to_nat(v___x_1138_);
                v___x_1140_ =
                    l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(
                        v_s_1126_,
                        v_p_1134_,
                        v___y_1136_,
                        v___x_1139_,
                    );
                return v___x_1140_;
            }
            2 => {
                v___x_1147_ = l_Lean_Name_str___override(v_res_1128_, v_acc_1129_);
                v___x_1148_ = l_String_mangle___closed__0;
                v___x_1149_ = lean_unsigned_to_nat(1);
                v___x_1150_ = lean_nat_shiftr(v_ucount_1130_, v___x_1149_);
                lean_dec(v_ucount_1130_);
                v___x_1151_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_1150_, v___x_1148_);
                v___x_1152_ = lean_string_push(v___x_1151_, v_ch_1133_);
                v_p_u2080_1127_ = v_p_1134_;
                v_res_1128_ = v___x_1147_;
                v_acc_1129_ = v___x_1152_;
                v_ucount_1130_ = v___x_1145_;
                state = 0;
                continue;
            }
            3 => {
                v___x_1155_ = 85;
                v___x_1156_ = lean_uint32_dec_eq(v_ch_1133_, v___x_1155_);
                if v___x_1156_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_1157_ = lean_unsigned_to_nat(8);
                    v___x_1158_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(
                        v___x_1157_,
                        v_s_1126_,
                        v_p_1134_,
                        v___x_1145_,
                    );
                    if lean_obj_tag(v___x_1158_) == 1 {
                        v_val_1159_ = lean_ctor_get(v___x_1158_, 0);
                        lean_inc(v_val_1159_);
                        lean_dec_ref_known(v___x_1158_, 1);
                        v_fst_1160_ = lean_ctor_get(v_val_1159_, 0);
                        lean_inc(v_fst_1160_);
                        v_snd_1161_ = lean_ctor_get(v_val_1159_, 1);
                        lean_inc(v_snd_1161_);
                        lean_dec(v_val_1159_);
                        v___x_1162_ = lean_unsigned_to_nat(1);
                        v___x_1163_ = lean_nat_shiftr(v_ucount_1130_, v___x_1162_);
                        lean_dec(v_ucount_1130_);
                        v_acc_1164_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_1163_, v_acc_1129_);
                        v___x_1165_ = l_Char_ofNat(v_snd_1161_);
                        lean_dec(v_snd_1161_);
                        v___x_1166_ = lean_string_push(v_acc_1164_, v___x_1165_);
                        v_p_u2080_1127_ = v_fst_1160_;
                        v_acc_1129_ = v___x_1166_;
                        v_ucount_1130_ = v___x_1145_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_1158_);
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1169_ = 117;
                v___x_1170_ = lean_uint32_dec_eq(v_ch_1133_, v___x_1169_);
                if v___x_1170_ == 0 {
                    state = 3;
                    continue;
                } else {
                    v___x_1171_ = lean_unsigned_to_nat(4);
                    v___x_1172_ = l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(
                        v___x_1171_,
                        v_s_1126_,
                        v_p_1134_,
                        v___x_1145_,
                    );
                    if lean_obj_tag(v___x_1172_) == 1 {
                        v_val_1173_ = lean_ctor_get(v___x_1172_, 0);
                        lean_inc(v_val_1173_);
                        lean_dec_ref_known(v___x_1172_, 1);
                        v_fst_1174_ = lean_ctor_get(v_val_1173_, 0);
                        lean_inc(v_fst_1174_);
                        v_snd_1175_ = lean_ctor_get(v_val_1173_, 1);
                        lean_inc(v_snd_1175_);
                        lean_dec(v_val_1173_);
                        v___x_1176_ = lean_unsigned_to_nat(1);
                        v___x_1177_ = lean_nat_shiftr(v_ucount_1130_, v___x_1176_);
                        lean_dec(v_ucount_1130_);
                        v_acc_1178_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_1177_, v_acc_1129_);
                        v___x_1179_ = l_Char_ofNat(v_snd_1175_);
                        lean_dec(v_snd_1175_);
                        v___x_1180_ = lean_string_push(v_acc_1178_, v___x_1179_);
                        v_p_u2080_1127_ = v_fst_1174_;
                        v_acc_1129_ = v___x_1180_;
                        v_ucount_1130_ = v___x_1145_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_1172_);
                        state = 3;
                        continue;
                    }
                }
            }
            5 => {
                if v___y_1184_ == 0 {
                    v___y_1136_ = v___y_1183_;
                    state = 1;
                    continue;
                } else {
                    v___x_1185_ = lean_string_utf8_get_fast(v_s_1126_, v_p_1134_);
                    v___x_1186_ = 48;
                    v___x_1187_ = lean_uint32_dec_eq(v___x_1185_, v___x_1186_);
                    if v___x_1187_ == 0 {
                        v___y_1136_ = v___y_1183_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1188_ = lean_string_utf8_next_fast(v_s_1126_, v_p_1134_);
                        v___x_1189_ = l_String_mangle___closed__0;
                        v_p_u2080_1127_ = v___x_1188_;
                        v_res_1128_ = v___y_1183_;
                        v_acc_1129_ = v___x_1189_;
                        v_ucount_1130_ = v___x_1145_;
                        state = 0;
                        continue;
                    }
                }
            }
            6 => {
                if v___y_1192_ == 0 {
                    v___x_1193_ = 120;
                    v___x_1194_ = lean_uint32_dec_eq(v_ch_1133_, v___x_1193_);
                    if v___x_1194_ == 0 {
                        state = 4;
                        continue;
                    } else {
                        v___x_1195_ =
                            l___private_Lean_Compiler_NameMangling_0__Lean_parseLowerHex_x3f(
                                v___x_1143_,
                                v_s_1126_,
                                v_p_1134_,
                                v___x_1145_,
                            );
                        if lean_obj_tag(v___x_1195_) == 1 {
                            v_val_1196_ = lean_ctor_get(v___x_1195_, 0);
                            lean_inc(v_val_1196_);
                            lean_dec_ref_known(v___x_1195_, 1);
                            v_fst_1197_ = lean_ctor_get(v_val_1196_, 0);
                            lean_inc(v_fst_1197_);
                            v_snd_1198_ = lean_ctor_get(v_val_1196_, 1);
                            lean_inc(v_snd_1198_);
                            lean_dec(v_val_1196_);
                            v___x_1199_ = lean_unsigned_to_nat(1);
                            v___x_1200_ = lean_nat_shiftr(v_ucount_1130_, v___x_1199_);
                            lean_dec(v_ucount_1130_);
                            v_acc_1201_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_1200_, v_acc_1129_);
                            v___x_1202_ = l_Char_ofNat(v_snd_1198_);
                            lean_dec(v_snd_1198_);
                            v___x_1203_ = lean_string_push(v_acc_1201_, v___x_1202_);
                            v_p_u2080_1127_ = v_fst_1197_;
                            v_acc_1129_ = v___x_1203_;
                            v_ucount_1130_ = v___x_1145_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v___x_1195_);
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_1205_ = lean_unsigned_to_nat(1);
                    v___x_1206_ = lean_nat_shiftr(v_ucount_1130_, v___x_1205_);
                    lean_dec(v_ucount_1130_);
                    v___x_1207_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_spec__2(v___x_1206_, v_acc_1129_);
                    v_res_1208_ = l_Lean_Name_str___override(v_res_1128_, v___x_1207_);
                    v___x_1209_ = 48;
                    v___x_1210_ = lean_uint32_dec_eq(v_ch_1133_, v___x_1209_);
                    if v___x_1210_ == 0 {
                        v___y_1136_ = v_res_1208_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1211_ = lean_nat_dec_eq(v_p_1134_, v___x_1131_);
                        if v___x_1211_ == 0 {
                            v___y_1183_ = v_res_1208_;
                            v___y_1184_ = v___x_1210_;
                            state = 5;
                            continue;
                        } else {
                            v___y_1183_ = v_res_1208_;
                            v___y_1184_ = v___x_1142_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(
    mut v_s_1229_: *mut LeanObject,
    mut v_p_1230_: *mut LeanObject,
    mut v_res_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: u8 = 0;
    let mut v_ch_1234_: u32 = 0;
    let mut v_p_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: u32 = 0;
    let mut v___x_1238_: u32 = 0;
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1242_: u8 = 0;
    let mut v___x_1243_: u32 = 0;
    let mut v___x_1244_: u32 = 0;
    let mut v___x_1245_: u8 = 0;
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1251_: u8 = 0;
    let mut v___x_1252_: u32 = 0;
    let mut v___x_1253_: u8 = 0;
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: u32 = 0;
    let mut v___x_1262_: u8 = 0;
    let mut v___x_1263_: u8 = 0;
    let mut v___x_1264_: u32 = 0;
    let mut v___x_1265_: u8 = 0;
    let mut v___x_1266_: u32 = 0;
    let mut v___x_1267_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1232_ = lean_string_utf8_byte_size(v_s_1229_);
                v___x_1233_ = lean_nat_dec_eq(v_p_1230_, v___x_1232_);
                if v___x_1233_ == 0 {
                    v_ch_1234_ = lean_string_utf8_get_fast(v_s_1229_, v_p_1230_);
                    v_p_1235_ = lean_string_utf8_next_fast(v_s_1229_, v_p_1230_);
                    v___x_1264_ = 48;
                    v___x_1265_ = lean_uint32_dec_le(v___x_1264_, v_ch_1234_);
                    if v___x_1265_ == 0 {
                        v___y_1251_ = v___x_1265_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1266_ = 57;
                        v___x_1267_ = lean_uint32_dec_le(v_ch_1234_, v___x_1266_);
                        v___y_1251_ = v___x_1267_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v_res_1231_;
                }
            }
            1 => {
                v___x_1237_ = 48;
                v___x_1238_ = lean_uint32_sub(v_ch_1234_, v___x_1237_);
                v___x_1239_ = lean_uint32_to_nat(v___x_1238_);
                v___x_1240_ =
                    l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(
                        v_s_1229_,
                        v_p_1235_,
                        v_res_1231_,
                        v___x_1239_,
                    );
                return v___x_1240_;
            }
            2 => {
                if v___y_1242_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_1243_ = lean_string_utf8_get_fast(v_s_1229_, v_p_1235_);
                    v___x_1244_ = 48;
                    v___x_1245_ = lean_uint32_dec_eq(v___x_1243_, v___x_1244_);
                    if v___x_1245_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1246_ = lean_string_utf8_next_fast(v_s_1229_, v_p_1235_);
                        v___x_1247_ = l_String_mangle___closed__0;
                        v___x_1248_ = lean_unsigned_to_nat(0);
                        v___x_1249_ =
                            l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(
                                v_s_1229_,
                                v___x_1246_,
                                v_res_1231_,
                                v___x_1247_,
                                v___x_1248_,
                            );
                        return v___x_1249_;
                    }
                }
            }
            3 => {
                if v___y_1251_ == 0 {
                    v___x_1252_ = 95;
                    v___x_1253_ = lean_uint32_dec_eq(v_ch_1234_, v___x_1252_);
                    if v___x_1253_ == 0 {
                        v___x_1254_ = l_String_mangle___closed__0;
                        v___x_1255_ = lean_string_push(v___x_1254_, v_ch_1234_);
                        v___x_1256_ = lean_unsigned_to_nat(0);
                        v___x_1257_ =
                            l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(
                                v_s_1229_,
                                v_p_1235_,
                                v_res_1231_,
                                v___x_1255_,
                                v___x_1256_,
                            );
                        return v___x_1257_;
                    } else {
                        v___x_1258_ = l_String_mangle___closed__0;
                        v___x_1259_ = lean_unsigned_to_nat(1);
                        v___x_1260_ =
                            l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(
                                v_s_1229_,
                                v_p_1235_,
                                v_res_1231_,
                                v___x_1258_,
                                v___x_1259_,
                            );
                        return v___x_1260_;
                    }
                } else {
                    v___x_1261_ = 48;
                    v___x_1262_ = lean_uint32_dec_eq(v_ch_1234_, v___x_1261_);
                    if v___x_1262_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        v___x_1263_ = lean_nat_dec_eq(v_p_1235_, v___x_1232_);
                        if v___x_1263_ == 0 {
                            v___y_1242_ = v___x_1262_;
                            state = 2;
                            continue;
                        } else {
                            v___y_1242_ = v___x_1233_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(
    mut v_s_1268_: *mut LeanObject,
    mut v_p_1269_: *mut LeanObject,
    mut v_res_1270_: *mut LeanObject,
    mut v_n_1271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: u8 = 0;
    let mut v_ch_1274_: u32 = 0;
    let mut v_p_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1277_: u8 = 0;
    let mut v_res_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: u8 = 0;
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: u32 = 0;
    let mut v___x_1285_: u32 = 0;
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: u32 = 0;
    let mut v___x_1290_: u8 = 0;
    let mut v___x_1291_: u32 = 0;
    let mut v___x_1292_: u8 = 0;
    let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1272_ = lean_string_utf8_byte_size(v_s_1268_);
                v___x_1273_ = lean_nat_dec_eq(v_p_1269_, v___x_1272_);
                if v___x_1273_ == 0 {
                    v_ch_1274_ = lean_string_utf8_get_fast(v_s_1268_, v_p_1269_);
                    v_p_1275_ = lean_string_utf8_next_fast(v_s_1268_, v_p_1269_);
                    lean_dec(v_p_1269_);
                    v___x_1289_ = 48;
                    v___x_1290_ = lean_uint32_dec_le(v___x_1289_, v_ch_1274_);
                    if v___x_1290_ == 0 {
                        v___y_1277_ = v___x_1290_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1291_ = 57;
                        v___x_1292_ = lean_uint32_dec_le(v_ch_1274_, v___x_1291_);
                        v___y_1277_ = v___x_1292_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_p_1269_);
                    v___x_1293_ = l_Lean_Name_num___override(v_res_1270_, v_n_1271_);
                    return v___x_1293_;
                }
            }
            1 => {
                if v___y_1277_ == 0 {
                    v_res_1278_ = l_Lean_Name_num___override(v_res_1270_, v_n_1271_);
                    v___x_1279_ = lean_nat_dec_eq(v_p_1275_, v___x_1272_);
                    if v___x_1279_ == 0 {
                        v___x_1280_ = lean_string_utf8_next_fast(v_s_1268_, v_p_1275_);
                        v___x_1281_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(v_s_1268_, v___x_1280_, v_res_1278_);
                        return v___x_1281_;
                    } else {
                        return v_res_1278_;
                    }
                } else {
                    v___x_1282_ = lean_unsigned_to_nat(10);
                    v___x_1283_ = lean_nat_mul(v_n_1271_, v___x_1282_);
                    lean_dec(v_n_1271_);
                    v___x_1284_ = 48;
                    v___x_1285_ = lean_uint32_sub(v_ch_1274_, v___x_1284_);
                    v___x_1286_ = lean_uint32_to_nat(v___x_1285_);
                    v___x_1287_ = lean_nat_add(v___x_1283_, v___x_1286_);
                    lean_dec(v___x_1286_);
                    lean_dec(v___x_1283_);
                    v_p_1269_ = v_p_1275_;
                    v_n_1271_ = v___x_1287_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum___boxed(
    mut v_s_1294_: *mut LeanObject,
    mut v_p_1295_: *mut LeanObject,
    mut v_res_1296_: *mut LeanObject,
    mut v_n_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1298_: *mut LeanObject = core::ptr::null_mut();
    v_res_1298_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_decodeNum(
        v_s_1294_,
        v_p_1295_,
        v_res_1296_,
        v_n_1297_,
    );
    lean_dec_ref(v_s_1294_);
    return v_res_1298_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart___boxed(
    mut v_s_1299_: *mut LeanObject,
    mut v_p_1300_: *mut LeanObject,
    mut v_res_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1302_: *mut LeanObject = core::ptr::null_mut();
    v_res_1302_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(
        v_s_1299_,
        v_p_1300_,
        v_res_1301_,
    );
    lean_dec(v_p_1300_);
    lean_dec_ref(v_s_1299_);
    return v_res_1302_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux___boxed(
    mut v_s_1303_: *mut LeanObject,
    mut v_p_u2080_1304_: *mut LeanObject,
    mut v_res_1305_: *mut LeanObject,
    mut v_acc_1306_: *mut LeanObject,
    mut v_ucount_1307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1308_: *mut LeanObject = core::ptr::null_mut();
    v_res_1308_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux(
        v_s_1303_,
        v_p_u2080_1304_,
        v_res_1305_,
        v_acc_1306_,
        v_ucount_1307_,
    );
    lean_dec_ref(v_s_1303_);
    return v_res_1308_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_1309_: u32 = 0;
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    v___x_1309_ = 120;
    v___x_1310_ = lean_box_uint32(v___x_1309_);
    return v___x_1310_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(
    mut v_ch_1311_: u32,
    mut v_x_1312_: *mut LeanObject,
    mut v_h__1_1313_: *mut LeanObject,
    mut v_h__2_1314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1315_: u32 = 0;
    let mut v___x_1316_: u8 = 0;
    v___x_1315_ = 120;
    v___x_1316_ = lean_uint32_dec_eq(v_ch_1311_, v___x_1315_);
    if v___x_1316_ == 0 {
        let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1313_);
        v___x_1317_ = lean_box_uint32(v_ch_1311_);
        v___x_1318_ = lean_apply_4(
            v_h__2_1314_,
            v___x_1317_,
            v_x_1312_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1318_;
    } else {
        if lean_obj_tag(v_x_1312_) == 1 {
            let mut v_val_1319_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_1320_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1314_);
            v_val_1319_ = lean_ctor_get(v_x_1312_, 0);
            lean_inc(v_val_1319_);
            lean_dec_ref_known(v_x_1312_, 1);
            v_fst_1320_ = lean_ctor_get(v_val_1319_, 0);
            lean_inc(v_fst_1320_);
            v_snd_1321_ = lean_ctor_get(v_val_1319_, 1);
            lean_inc(v_snd_1321_);
            lean_dec(v_val_1319_);
            v___x_1322_ = lean_apply_3(v_h__1_1313_, v_fst_1320_, v_snd_1321_, lean_box(0));
            return v___x_1322_;
        } else {
            let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1324_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1313_);
            v___x_1323_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
            v___x_1324_ = lean_apply_4(
                v_h__2_1314_,
                v___x_1323_,
                v_x_1312_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1324_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed(
    mut v_ch_1325_: *mut LeanObject,
    mut v_x_1326_: *mut LeanObject,
    mut v_h__1_1327_: *mut LeanObject,
    mut v_h__2_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ch_81__boxed_1329_: u32 = 0;
    let mut v_res_1330_: *mut LeanObject = core::ptr::null_mut();
    v_ch_81__boxed_1329_ = lean_unbox_uint32(v_ch_1325_);
    lean_dec(v_ch_1325_);
    v_res_1330_ =
        l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg(
            v_ch_81__boxed_1329_,
            v_x_1326_,
            v_h__1_1327_,
            v_h__2_1328_,
        );
    return v_res_1330_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(
    mut v_s_1331_: *mut LeanObject,
    mut v_motive_1332_: *mut LeanObject,
    mut v_ch_1333_: u32,
    mut v_x_1334_: *mut LeanObject,
    mut v_h__1_1335_: *mut LeanObject,
    mut v_h__2_1336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1337_: u32 = 0;
    let mut v___x_1338_: u8 = 0;
    v___x_1337_ = 120;
    v___x_1338_ = lean_uint32_dec_eq(v_ch_1333_, v___x_1337_);
    if v___x_1338_ == 0 {
        let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1335_);
        v___x_1339_ = lean_box_uint32(v_ch_1333_);
        v___x_1340_ = lean_apply_4(
            v_h__2_1336_,
            v___x_1339_,
            v_x_1334_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1340_;
    } else {
        if lean_obj_tag(v_x_1334_) == 1 {
            let mut v_val_1341_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_1342_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1343_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1344_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1336_);
            v_val_1341_ = lean_ctor_get(v_x_1334_, 0);
            lean_inc(v_val_1341_);
            lean_dec_ref_known(v_x_1334_, 1);
            v_fst_1342_ = lean_ctor_get(v_val_1341_, 0);
            lean_inc(v_fst_1342_);
            v_snd_1343_ = lean_ctor_get(v_val_1341_, 1);
            lean_inc(v_snd_1343_);
            lean_dec(v_val_1341_);
            v___x_1344_ = lean_apply_3(v_h__1_1335_, v_fst_1342_, v_snd_1343_, lean_box(0));
            return v___x_1344_;
        } else {
            let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1335_);
            v___x_1345_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1;
            v___x_1346_ = lean_apply_4(
                v_h__2_1336_,
                v___x_1345_,
                v_x_1334_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1346_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___boxed(
    mut v_s_1347_: *mut LeanObject,
    mut v_motive_1348_: *mut LeanObject,
    mut v_ch_1349_: *mut LeanObject,
    mut v_x_1350_: *mut LeanObject,
    mut v_h__1_1351_: *mut LeanObject,
    mut v_h__2_1352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ch_111__boxed_1353_: u32 = 0;
    let mut v_res_1354_: *mut LeanObject = core::ptr::null_mut();
    v_ch_111__boxed_1353_ = lean_unbox_uint32(v_ch_1349_);
    lean_dec(v_ch_1349_);
    v_res_1354_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter(
        v_s_1347_,
        v_motive_1348_,
        v_ch_111__boxed_1353_,
        v_x_1350_,
        v_h__1_1351_,
        v_h__2_1352_,
    );
    lean_dec_ref(v_s_1347_);
    return v_res_1354_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_1355_: u32 = 0;
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    v___x_1355_ = 117;
    v___x_1356_ = lean_box_uint32(v___x_1355_);
    return v___x_1356_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(
    mut v_ch_1357_: u32,
    mut v_x_1358_: *mut LeanObject,
    mut v_h__1_1359_: *mut LeanObject,
    mut v_h__2_1360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1361_: u32 = 0;
    let mut v___x_1362_: u8 = 0;
    v___x_1361_ = 117;
    v___x_1362_ = lean_uint32_dec_eq(v_ch_1357_, v___x_1361_);
    if v___x_1362_ == 0 {
        let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1359_);
        v___x_1363_ = lean_box_uint32(v_ch_1357_);
        v___x_1364_ = lean_apply_4(
            v_h__2_1360_,
            v___x_1363_,
            v_x_1358_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1364_;
    } else {
        if lean_obj_tag(v_x_1358_) == 1 {
            let mut v_val_1365_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_1366_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1367_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1360_);
            v_val_1365_ = lean_ctor_get(v_x_1358_, 0);
            lean_inc(v_val_1365_);
            lean_dec_ref_known(v_x_1358_, 1);
            v_fst_1366_ = lean_ctor_get(v_val_1365_, 0);
            lean_inc(v_fst_1366_);
            v_snd_1367_ = lean_ctor_get(v_val_1365_, 1);
            lean_inc(v_snd_1367_);
            lean_dec(v_val_1365_);
            v___x_1368_ = lean_apply_3(v_h__1_1359_, v_fst_1366_, v_snd_1367_, lean_box(0));
            return v___x_1368_;
        } else {
            let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1359_);
            v___x_1369_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
            v___x_1370_ = lean_apply_4(
                v_h__2_1360_,
                v___x_1369_,
                v_x_1358_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1370_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed(
    mut v_ch_1371_: *mut LeanObject,
    mut v_x_1372_: *mut LeanObject,
    mut v_h__1_1373_: *mut LeanObject,
    mut v_h__2_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ch_81__boxed_1375_: u32 = 0;
    let mut v_res_1376_: *mut LeanObject = core::ptr::null_mut();
    v_ch_81__boxed_1375_ = lean_unbox_uint32(v_ch_1371_);
    lean_dec(v_ch_1371_);
    v_res_1376_ =
        l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg(
            v_ch_81__boxed_1375_,
            v_x_1372_,
            v_h__1_1373_,
            v_h__2_1374_,
        );
    return v_res_1376_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(
    mut v_s_1377_: *mut LeanObject,
    mut v_motive_1378_: *mut LeanObject,
    mut v_ch_1379_: u32,
    mut v_x_1380_: *mut LeanObject,
    mut v_h__1_1381_: *mut LeanObject,
    mut v_h__2_1382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1383_: u32 = 0;
    let mut v___x_1384_: u8 = 0;
    v___x_1383_ = 117;
    v___x_1384_ = lean_uint32_dec_eq(v_ch_1379_, v___x_1383_);
    if v___x_1384_ == 0 {
        let mut v___x_1385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1381_);
        v___x_1385_ = lean_box_uint32(v_ch_1379_);
        v___x_1386_ = lean_apply_4(
            v_h__2_1382_,
            v___x_1385_,
            v_x_1380_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1386_;
    } else {
        if lean_obj_tag(v_x_1380_) == 1 {
            let mut v_val_1387_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_1388_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1389_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1382_);
            v_val_1387_ = lean_ctor_get(v_x_1380_, 0);
            lean_inc(v_val_1387_);
            lean_dec_ref_known(v_x_1380_, 1);
            v_fst_1388_ = lean_ctor_get(v_val_1387_, 0);
            lean_inc(v_fst_1388_);
            v_snd_1389_ = lean_ctor_get(v_val_1387_, 1);
            lean_inc(v_snd_1389_);
            lean_dec(v_val_1387_);
            v___x_1390_ = lean_apply_3(v_h__1_1381_, v_fst_1388_, v_snd_1389_, lean_box(0));
            return v___x_1390_;
        } else {
            let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1381_);
            v___x_1391_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1;
            v___x_1392_ = lean_apply_4(
                v_h__2_1382_,
                v___x_1391_,
                v_x_1380_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1392_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___boxed(
    mut v_s_1393_: *mut LeanObject,
    mut v_motive_1394_: *mut LeanObject,
    mut v_ch_1395_: *mut LeanObject,
    mut v_x_1396_: *mut LeanObject,
    mut v_h__1_1397_: *mut LeanObject,
    mut v_h__2_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ch_111__boxed_1399_: u32 = 0;
    let mut v_res_1400_: *mut LeanObject = core::ptr::null_mut();
    v_ch_111__boxed_1399_ = lean_unbox_uint32(v_ch_1395_);
    lean_dec(v_ch_1395_);
    v_res_1400_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter(
        v_s_1393_,
        v_motive_1394_,
        v_ch_111__boxed_1399_,
        v_x_1396_,
        v_h__1_1397_,
        v_h__2_1398_,
    );
    lean_dec_ref(v_s_1393_);
    return v_res_1400_;
}
pub unsafe fn _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_1401_: u32 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    v___x_1401_ = 85;
    v___x_1402_ = lean_box_uint32(v___x_1401_);
    return v___x_1402_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(
    mut v_ch_1403_: u32,
    mut v_x_1404_: *mut LeanObject,
    mut v_h__1_1405_: *mut LeanObject,
    mut v_h__2_1406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1407_: u32 = 0;
    let mut v___x_1408_: u8 = 0;
    v___x_1407_ = 85;
    v___x_1408_ = lean_uint32_dec_eq(v_ch_1403_, v___x_1407_);
    if v___x_1408_ == 0 {
        let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1405_);
        v___x_1409_ = lean_box_uint32(v_ch_1403_);
        v___x_1410_ = lean_apply_4(
            v_h__2_1406_,
            v___x_1409_,
            v_x_1404_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1410_;
    } else {
        if lean_obj_tag(v_x_1404_) == 1 {
            let mut v_val_1411_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_1412_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1413_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1414_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1406_);
            v_val_1411_ = lean_ctor_get(v_x_1404_, 0);
            lean_inc(v_val_1411_);
            lean_dec_ref_known(v_x_1404_, 1);
            v_fst_1412_ = lean_ctor_get(v_val_1411_, 0);
            lean_inc(v_fst_1412_);
            v_snd_1413_ = lean_ctor_get(v_val_1411_, 1);
            lean_inc(v_snd_1413_);
            lean_dec(v_val_1411_);
            v___x_1414_ = lean_apply_3(v_h__1_1405_, v_fst_1412_, v_snd_1413_, lean_box(0));
            return v___x_1414_;
        } else {
            let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1416_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1405_);
            v___x_1415_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
            v___x_1416_ = lean_apply_4(
                v_h__2_1406_,
                v___x_1415_,
                v_x_1404_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1416_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed(
    mut v_ch_1417_: *mut LeanObject,
    mut v_x_1418_: *mut LeanObject,
    mut v_h__1_1419_: *mut LeanObject,
    mut v_h__2_1420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ch_81__boxed_1421_: u32 = 0;
    let mut v_res_1422_: *mut LeanObject = core::ptr::null_mut();
    v_ch_81__boxed_1421_ = lean_unbox_uint32(v_ch_1417_);
    lean_dec(v_ch_1417_);
    v_res_1422_ =
        l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg(
            v_ch_81__boxed_1421_,
            v_x_1418_,
            v_h__1_1419_,
            v_h__2_1420_,
        );
    return v_res_1422_;
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(
    mut v_s_1423_: *mut LeanObject,
    mut v_motive_1424_: *mut LeanObject,
    mut v_ch_1425_: u32,
    mut v_x_1426_: *mut LeanObject,
    mut v_h__1_1427_: *mut LeanObject,
    mut v_h__2_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1429_: u32 = 0;
    let mut v___x_1430_: u8 = 0;
    v___x_1429_ = 85;
    v___x_1430_ = lean_uint32_dec_eq(v_ch_1425_, v___x_1429_);
    if v___x_1430_ == 0 {
        let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1427_);
        v___x_1431_ = lean_box_uint32(v_ch_1425_);
        v___x_1432_ = lean_apply_4(
            v_h__2_1428_,
            v___x_1431_,
            v_x_1426_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1432_;
    } else {
        if lean_obj_tag(v_x_1426_) == 1 {
            let mut v_val_1433_: *mut LeanObject = core::ptr::null_mut();
            let mut v_fst_1434_: *mut LeanObject = core::ptr::null_mut();
            let mut v_snd_1435_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1428_);
            v_val_1433_ = lean_ctor_get(v_x_1426_, 0);
            lean_inc(v_val_1433_);
            lean_dec_ref_known(v_x_1426_, 1);
            v_fst_1434_ = lean_ctor_get(v_val_1433_, 0);
            lean_inc(v_fst_1434_);
            v_snd_1435_ = lean_ctor_get(v_val_1433_, 1);
            lean_inc(v_snd_1435_);
            lean_dec(v_val_1433_);
            v___x_1436_ = lean_apply_3(v_h__1_1427_, v_fst_1434_, v_snd_1435_, lean_box(0));
            return v___x_1436_;
        } else {
            let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1427_);
            v___x_1437_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1;
            v___x_1438_ = lean_apply_4(
                v_h__2_1428_,
                v___x_1437_,
                v_x_1426_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1438_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___boxed(
    mut v_s_1439_: *mut LeanObject,
    mut v_motive_1440_: *mut LeanObject,
    mut v_ch_1441_: *mut LeanObject,
    mut v_x_1442_: *mut LeanObject,
    mut v_h__1_1443_: *mut LeanObject,
    mut v_h__2_1444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ch_111__boxed_1445_: u32 = 0;
    let mut v_res_1446_: *mut LeanObject = core::ptr::null_mut();
    v_ch_111__boxed_1445_ = lean_unbox_uint32(v_ch_1441_);
    lean_dec(v_ch_1441_);
    v_res_1446_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter(
        v_s_1439_,
        v_motive_1440_,
        v_ch_111__boxed_1445_,
        v_x_1442_,
        v_h__1_1443_,
        v_h__2_1444_,
    );
    lean_dec_ref(v_s_1439_);
    return v_res_1446_;
}
pub unsafe fn l_Lean_Name_demangle(mut v_s_1447_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v___x_1448_ = lean_unsigned_to_nat(0);
    v___x_1449_ = lean_box(0);
    v___x_1450_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_nameStart(
        v_s_1447_,
        v___x_1448_,
        v___x_1449_,
    );
    return v___x_1450_;
}
pub unsafe fn l_Lean_Name_demangle___boxed(mut v_s_1451_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1452_: *mut LeanObject = core::ptr::null_mut();
    v_res_1452_ = l_Lean_Name_demangle(v_s_1451_);
    lean_dec_ref(v_s_1451_);
    return v_res_1452_;
}
pub unsafe fn l_Lean_Name_demangle_x3f(mut v_s_1453_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: u8 = 0;
    v_n_1454_ = l_Lean_Name_demangle(v_s_1453_);
    lean_inc(v_n_1454_);
    v___x_1455_ = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(v_n_1454_);
    v___x_1456_ = lean_string_dec_eq(v___x_1455_, v_s_1453_);
    lean_dec_ref(v___x_1455_);
    if v___x_1456_ == 0 {
        let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_n_1454_);
        v___x_1457_ = lean_box(0);
        return v___x_1457_;
    } else {
        let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
        v___x_1458_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1458_, 0, v_n_1454_);
        return v___x_1458_;
    }
}
pub unsafe fn l_Lean_Name_demangle_x3f___boxed(mut v_s_1459_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1460_: *mut LeanObject = core::ptr::null_mut();
    v_res_1460_ = l_Lean_Name_demangle_x3f(v_s_1459_);
    lean_dec_ref(v_s_1459_);
    return v_res_1460_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_NameMangling(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Setup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1();
    lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__6_splitter___redArg___boxed__const__1);
    l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1();
    lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__4_splitter___redArg___boxed__const__1);
    l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1();
    lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_demangleAux_match__1_splitter___redArg___boxed__const__1);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_NameMangling(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_NameMangling(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Setup(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NameMangling(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_NameMangling(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_NameMangling(builtin);
}
