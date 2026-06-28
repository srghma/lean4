// Lean compiler output
// Module: Lake.Toml.Data.DateTime
// Imports: Lake.Util.Date Lake.Util.String Init.Data.String.Search Init.Data.Iterators.Consumers.Collect Init.Data.Iterators.Consumers.Loop Init.Data.ToString.Macro
use crate::r#gen::Init::Core::l_instDecidableEqProd___redArg;
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Option::Basic::l_Option_instDecidableEq___redArg;
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_Pos_get_x3f;
use crate::r#gen::Init::Data::String::FindPos::{
    l_String_Slice_Pos_prev_x3f, l_String_Slice_Pos_prevn,
};
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_positions;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Init::Data::String::Slice::{l_String_Slice_toNat_x3f, l_String_Slice_toString};
use crate::r#gen::Init::Data::String::Subslice::l_String_Slice_subslice_x21;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Lake::Util::Date::{
    initialize_Lake_Util_Date, l_Lake_Date_ofString_x3f, l_Lake_Date_toString,
    l_Lake_instDecidableEqDate_decEq, l_Lake_instInhabitedDate_default,
    runtime_initialize_Lake_Util_Date,
};
use crate::r#gen::Lake::Util::String::{
    initialize_Lake_Util_String, l_Lake_rpadAscii, l_Lake_zpad, runtime_initialize_Lake_Util_String,
};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_extract, lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_string_utf8_byte_size, lean_uint32_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_uint32,
    lean_unsigned_to_nat,
};
pub static l_Lake_Toml_instInhabitedTime_default___closed__0_value: LeanCtorObject<5> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_Toml_instInhabitedTime_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedTime_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_instInhabitedTime_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedTime_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_instInhabitedTime: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedTime_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_Time_zero: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedTime_default___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_Time_instOfNat: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instInhabitedTime_default___closed__0_value) as *mut LeanObject;
pub static l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Time_ofString_x3f___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lake_Toml_Time_ofString_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Time_ofString_x3f___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Time_toString___closed__0_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l_Lake_Toml_Time_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Time_toString___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_Time_toString___closed__1_value: LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lake_Toml_Time_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Time_toString___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_Time_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_Time_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_Time_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Time_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_Time_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_Time_instToString___closed__0_value) as *mut LeanObject;
static mut l_Lake_Toml_instInhabitedDateTime_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_Toml_instInhabitedDateTime_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lake_Toml_instInhabitedDateTime_default: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lake_Toml_instInhabitedDateTime: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_Toml_instCoeDateDateTime___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_instCoeDateDateTime___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_instCoeDateDateTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instCoeDateDateTime___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_instCoeDateDateTime: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instCoeDateDateTime___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_instCoeTimeDateTime___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_instCoeTimeDateTime___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_instCoeTimeDateTime___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instCoeTimeDateTime___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_instCoeTimeDateTime: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_instCoeTimeDateTime___closed__0_value) as *mut LeanObject;
pub static l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_DateTime_toString___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [84, 0],
    };
static mut l_Lake_Toml_DateTime_toString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_DateTime_toString___closed__0_value) as *mut LeanObject;
pub static l_Lake_Toml_DateTime_toString___closed__1_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [43, 0],
    };
static mut l_Lake_Toml_DateTime_toString___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_DateTime_toString___closed__1_value) as *mut LeanObject;
pub static l_Lake_Toml_DateTime_toString___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Toml_DateTime_toString___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_DateTime_toString___closed__2_value) as *mut LeanObject;
pub static l_Lake_Toml_DateTime_toString___closed__3_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [90, 0],
    };
static mut l_Lake_Toml_DateTime_toString___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_DateTime_toString___closed__3_value) as *mut LeanObject;
pub static l_Lake_Toml_DateTime_instToString___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_Toml_DateTime_toString as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_Toml_DateTime_instToString___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_DateTime_instToString___closed__0_value) as *mut LeanObject;
pub static mut l_Lake_Toml_DateTime_instToString: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Toml_DateTime_instToString___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_Toml_instDecidableEqTime_decEq(
    mut v_x_1005_: *mut LeanObject,
    mut v_x_1006_: *mut LeanObject,
) -> u8 {
    let mut v_hour_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fracExponent_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fracMantissa_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hour_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fracExponent_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fracMantissa_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: u8 = 0;
    v_hour_1007_ = lean_ctor_get(v_x_1005_, 0);
    v_minute_1008_ = lean_ctor_get(v_x_1005_, 1);
    v_second_1009_ = lean_ctor_get(v_x_1005_, 2);
    v_fracExponent_1010_ = lean_ctor_get(v_x_1005_, 3);
    v_fracMantissa_1011_ = lean_ctor_get(v_x_1005_, 4);
    v_hour_1012_ = lean_ctor_get(v_x_1006_, 0);
    v_minute_1013_ = lean_ctor_get(v_x_1006_, 1);
    v_second_1014_ = lean_ctor_get(v_x_1006_, 2);
    v_fracExponent_1015_ = lean_ctor_get(v_x_1006_, 3);
    v_fracMantissa_1016_ = lean_ctor_get(v_x_1006_, 4);
    v___x_1017_ = lean_nat_dec_eq(v_hour_1007_, v_hour_1012_);
    if v___x_1017_ == 0 {
        return v___x_1017_;
    } else {
        let mut v___x_1018_: u8 = 0;
        v___x_1018_ = lean_nat_dec_eq(v_minute_1008_, v_minute_1013_);
        if v___x_1018_ == 0 {
            return v___x_1018_;
        } else {
            let mut v___x_1019_: u8 = 0;
            v___x_1019_ = lean_nat_dec_eq(v_second_1009_, v_second_1014_);
            if v___x_1019_ == 0 {
                return v___x_1019_;
            } else {
                let mut v___x_1020_: u8 = 0;
                v___x_1020_ = lean_nat_dec_eq(v_fracExponent_1010_, v_fracExponent_1015_);
                if v___x_1020_ == 0 {
                    return v___x_1020_;
                } else {
                    let mut v___x_1021_: u8 = 0;
                    v___x_1021_ = lean_nat_dec_eq(v_fracMantissa_1011_, v_fracMantissa_1016_);
                    return v___x_1021_;
                }
            }
        }
    }
}
pub unsafe fn l_Lake_Toml_instDecidableEqTime_decEq___boxed(
    mut v_x_1022_: *mut LeanObject,
    mut v_x_1023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1024_: u8 = 0;
    let mut v_r_1025_: *mut LeanObject = core::ptr::null_mut();
    v_res_1024_ = l_Lake_Toml_instDecidableEqTime_decEq(v_x_1022_, v_x_1023_);
    lean_dec_ref(v_x_1023_);
    lean_dec_ref(v_x_1022_);
    v_r_1025_ = lean_box((v_res_1024_) as usize);
    return v_r_1025_;
}
pub unsafe fn l_Lake_Toml_instDecidableEqTime(
    mut v_x_1026_: *mut LeanObject,
    mut v_x_1027_: *mut LeanObject,
) -> u8 {
    let mut v___x_1028_: u8 = 0;
    v___x_1028_ = l_Lake_Toml_instDecidableEqTime_decEq(v_x_1026_, v_x_1027_);
    return v___x_1028_;
}
pub unsafe fn l_Lake_Toml_instDecidableEqTime___boxed(
    mut v_x_1029_: *mut LeanObject,
    mut v_x_1030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1031_: u8 = 0;
    let mut v_r_1032_: *mut LeanObject = core::ptr::null_mut();
    v_res_1031_ = l_Lake_Toml_instDecidableEqTime(v_x_1029_, v_x_1030_);
    lean_dec_ref(v_x_1030_);
    lean_dec_ref(v_x_1029_);
    v_r_1032_ = lean_box((v_res_1031_) as usize);
    return v_r_1032_;
}
pub unsafe fn l_Lake_Toml_Time_ofValid_x3f(
    mut v_hour_1035_: *mut LeanObject,
    mut v_minute_1036_: *mut LeanObject,
    mut v_second_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: u8 = 0;
    v___x_1038_ = lean_unsigned_to_nat(23);
    v___x_1039_ = lean_nat_dec_le(v_hour_1035_, v___x_1038_);
    if v___x_1039_ == 0 {
        let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_second_1037_);
        lean_dec(v_minute_1036_);
        lean_dec(v_hour_1035_);
        v___x_1040_ = lean_box(0);
        return v___x_1040_;
    } else {
        let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1042_: u8 = 0;
        v___x_1041_ = lean_unsigned_to_nat(59);
        v___x_1042_ = lean_nat_dec_le(v_minute_1036_, v___x_1041_);
        if v___x_1042_ == 0 {
            let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_second_1037_);
            lean_dec(v_minute_1036_);
            lean_dec(v_hour_1035_);
            v___x_1043_ = lean_box(0);
            return v___x_1043_;
        } else {
            let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1045_: u8 = 0;
            v___x_1044_ = lean_unsigned_to_nat(60);
            v___x_1045_ = lean_nat_dec_le(v_second_1037_, v___x_1044_);
            if v___x_1045_ == 0 {
                let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_second_1037_);
                lean_dec(v_minute_1036_);
                lean_dec(v_hour_1035_);
                v___x_1046_ = lean_box(0);
                return v___x_1046_;
            } else {
                let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
                v___x_1047_ = lean_unsigned_to_nat(0);
                v___x_1048_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_1048_, 0, v_hour_1035_);
                lean_ctor_set(v___x_1048_, 1, v_minute_1036_);
                lean_ctor_set(v___x_1048_, 2, v_second_1037_);
                lean_ctor_set(v___x_1048_, 3, v___x_1047_);
                lean_ctor_set(v___x_1048_, 4, v___x_1047_);
                v___x_1049_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1049_, 0, v___x_1048_);
                return v___x_1049_;
            }
        }
    }
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(
    mut v_s_1052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    v___x_1053_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0;
    return v___x_1053_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___boxed(
    mut v_s_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1055_: *mut LeanObject = core::ptr::null_mut();
    v_res_1055_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(v_s_1054_);
    lean_dec_ref(v_s_1054_);
    return v_res_1055_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(
    mut v_s_1056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    v___x_1057_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0;
    return v___x_1057_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2___boxed(
    mut v_s_1058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1059_: *mut LeanObject = core::ptr::null_mut();
    v_res_1059_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(v_s_1058_);
    lean_dec_ref(v_s_1058_);
    return v_res_1059_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(
    mut v_head_1060_: *mut LeanObject,
    mut v_a_1061_: *mut LeanObject,
    mut v_b_1062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currPos_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1067_: u8 = 0;
    let mut v_str_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: u8 = 0;
    let mut v___x_1082_: u32 = 0;
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: u32 = 0;
    let mut v___x_1085_: u8 = 0;
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1102_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1061_) == 0 {
                    v_currPos_1063_ = lean_ctor_get(v_a_1061_, 0);
                    v_searcher_1064_ = lean_ctor_get(v_a_1061_, 1);
                    v_isSharedCheck_1102_ = (!lean_is_exclusive(v_a_1061_)) as u8;
                    if v_isSharedCheck_1102_ == 0 {
                        v___x_1066_ = v_a_1061_;
                        v_isShared_1067_ = v_isSharedCheck_1102_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_searcher_1064_);
                        lean_inc(v_currPos_1063_);
                        lean_dec(v_a_1061_);
                        v___x_1066_ = lean_box(0);
                        v_isShared_1067_ = v_isSharedCheck_1102_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1062_;
                }
            }
            1 => {
                v_str_1068_ = lean_ctor_get(v_head_1060_, 0);
                v_startInclusive_1069_ = lean_ctor_get(v_head_1060_, 1);
                v_endExclusive_1070_ = lean_ctor_get(v_head_1060_, 2);
                v___x_1080_ = lean_nat_sub(v_endExclusive_1070_, v_startInclusive_1069_);
                v___x_1081_ = lean_nat_dec_eq(v_searcher_1064_, v___x_1080_);
                if v___x_1081_ == 0 {
                    lean_dec(v___x_1080_);
                    v___x_1082_ = 46;
                    v___x_1083_ = lean_nat_add(v_startInclusive_1069_, v_searcher_1064_);
                    v___x_1084_ = lean_string_utf8_get_fast(v_str_1068_, v___x_1083_);
                    v___x_1085_ = lean_uint32_dec_eq(v___x_1084_, v___x_1082_);
                    if v___x_1085_ == 0 {
                        lean_dec(v_searcher_1064_);
                        v___x_1086_ = lean_string_utf8_next_fast(v_str_1068_, v___x_1083_);
                        lean_dec(v___x_1083_);
                        v___x_1087_ = lean_nat_sub(v___x_1086_, v_startInclusive_1069_);
                        if v_isShared_1067_ == 0 {
                            lean_ctor_set(v___x_1066_, 1, v___x_1087_);
                            v___x_1089_ = v___x_1066_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_currPos_1063_);
                            lean_ctor_set(v_reuseFailAlloc_1091_, 1, v___x_1087_);
                            v___x_1089_ = v_reuseFailAlloc_1091_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1092_ = lean_string_utf8_next_fast(v_str_1068_, v___x_1083_);
                        v___x_1093_ = lean_nat_sub(v___x_1092_, v___x_1083_);
                        lean_dec(v___x_1083_);
                        v___x_1094_ = lean_nat_add(v_searcher_1064_, v___x_1093_);
                        lean_dec(v___x_1093_);
                        v_slice_1095_ = l_String_Slice_subslice_x21(
                            v_head_1060_,
                            v_currPos_1063_,
                            v_searcher_1064_,
                        );
                        lean_inc(v___x_1094_);
                        if v_isShared_1067_ == 0 {
                            lean_ctor_set(v___x_1066_, 1, v___x_1094_);
                            lean_ctor_set(v___x_1066_, 0, v___x_1094_);
                            v_nextIt_1097_ = v___x_1066_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1094_);
                            lean_ctor_set(v_reuseFailAlloc_1100_, 1, v___x_1094_);
                            v_nextIt_1097_ = v_reuseFailAlloc_1100_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1066_);
                    lean_dec(v_searcher_1064_);
                    v___x_1101_ = lean_box(1);
                    v_it_1072_ = v___x_1101_;
                    v_startInclusive_1073_ = v_currPos_1063_;
                    v_endExclusive_1074_ = v___x_1080_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1075_ = lean_nat_add(v_startInclusive_1069_, v_startInclusive_1073_);
                lean_dec(v_startInclusive_1073_);
                v___x_1076_ = lean_nat_add(v_startInclusive_1069_, v_endExclusive_1074_);
                lean_dec(v_endExclusive_1074_);
                lean_inc_ref(v_str_1068_);
                v___x_1077_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1077_, 0, v_str_1068_);
                lean_ctor_set(v___x_1077_, 1, v___x_1075_);
                lean_ctor_set(v___x_1077_, 2, v___x_1076_);
                v___x_1078_ = lean_array_push(v_b_1062_, v___x_1077_);
                v_a_1061_ = v_it_1072_;
                v_b_1062_ = v___x_1078_;
                state = 0;
                continue;
            }
            3 => {
                v_a_1061_ = v___x_1089_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1098_ = lean_ctor_get(v_slice_1095_, 0);
                lean_inc(v_startInclusive_1098_);
                v_endExclusive_1099_ = lean_ctor_get(v_slice_1095_, 1);
                lean_inc(v_endExclusive_1099_);
                lean_dec_ref(v_slice_1095_);
                v_it_1072_ = v_nextIt_1097_;
                v_startInclusive_1073_ = v_startInclusive_1098_;
                v_endExclusive_1074_ = v_endExclusive_1099_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg___boxed(
    mut v_head_1103_: *mut LeanObject,
    mut v_a_1104_: *mut LeanObject,
    mut v_b_1105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1106_: *mut LeanObject = core::ptr::null_mut();
    v_res_1106_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_1103_, v_a_1104_, v_b_1105_);
    lean_dec_ref(v_head_1103_);
    return v_res_1106_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(
    mut v_t_1107_: *mut LeanObject,
    mut v___x_1108_: *mut LeanObject,
    mut v___x_1109_: *mut LeanObject,
    mut v_a_1110_: *mut LeanObject,
    mut v_b_1111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_1119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1123_: u8 = 0;
    let mut v_startInclusive_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: u32 = 0;
    let mut v___x_1129_: u32 = 0;
    let mut v___x_1130_: u8 = 0;
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1146_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1110_) == 0 {
                    v_currPos_1119_ = lean_ctor_get(v_a_1110_, 0);
                    v_searcher_1120_ = lean_ctor_get(v_a_1110_, 1);
                    v_isSharedCheck_1146_ = (!lean_is_exclusive(v_a_1110_)) as u8;
                    if v_isSharedCheck_1146_ == 0 {
                        v___x_1122_ = v_a_1110_;
                        v_isShared_1123_ = v_isSharedCheck_1146_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_searcher_1120_);
                        lean_inc(v_currPos_1119_);
                        lean_dec(v_a_1110_);
                        v___x_1122_ = lean_box(0);
                        v_isShared_1123_ = v_isSharedCheck_1146_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1109_);
                    lean_dec_ref(v_t_1107_);
                    return v_b_1111_;
                }
            }
            1 => {
                lean_inc_ref(v_t_1107_);
                v___x_1116_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1116_, 0, v_t_1107_);
                lean_ctor_set(v___x_1116_, 1, v_startInclusive_1114_);
                lean_ctor_set(v___x_1116_, 2, v_endExclusive_1115_);
                v___x_1117_ = lean_array_push(v_b_1111_, v___x_1116_);
                v_a_1110_ = v_it_1113_;
                v_b_1111_ = v___x_1117_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1124_ = lean_ctor_get(v___x_1108_, 1);
                v_endExclusive_1125_ = lean_ctor_get(v___x_1108_, 2);
                v___x_1126_ = lean_nat_sub(v_endExclusive_1125_, v_startInclusive_1124_);
                v___x_1127_ = lean_nat_dec_eq(v_searcher_1120_, v___x_1126_);
                lean_dec(v___x_1126_);
                if v___x_1127_ == 0 {
                    v___x_1128_ = 58;
                    v___x_1129_ = lean_string_utf8_get_fast(v_t_1107_, v_searcher_1120_);
                    v___x_1130_ = lean_uint32_dec_eq(v___x_1129_, v___x_1128_);
                    if v___x_1130_ == 0 {
                        v___x_1131_ = lean_string_utf8_next_fast(v_t_1107_, v_searcher_1120_);
                        lean_dec(v_searcher_1120_);
                        if v_isShared_1123_ == 0 {
                            lean_ctor_set(v___x_1122_, 1, v___x_1131_);
                            v___x_1133_ = v___x_1122_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_currPos_1119_);
                            lean_ctor_set(v_reuseFailAlloc_1135_, 1, v___x_1131_);
                            v___x_1133_ = v_reuseFailAlloc_1135_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1136_ = lean_string_utf8_next_fast(v_t_1107_, v_searcher_1120_);
                        v___x_1137_ = lean_nat_sub(v___x_1136_, v_searcher_1120_);
                        v___x_1138_ = lean_nat_add(v_searcher_1120_, v___x_1137_);
                        lean_dec(v___x_1137_);
                        v_slice_1139_ = l_String_Slice_subslice_x21(
                            v___x_1108_,
                            v_currPos_1119_,
                            v_searcher_1120_,
                        );
                        lean_inc(v___x_1138_);
                        if v_isShared_1123_ == 0 {
                            lean_ctor_set(v___x_1122_, 1, v___x_1138_);
                            lean_ctor_set(v___x_1122_, 0, v___x_1138_);
                            v_nextIt_1141_ = v___x_1122_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___x_1138_);
                            lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1138_);
                            v_nextIt_1141_ = v_reuseFailAlloc_1144_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1122_);
                    lean_dec(v_searcher_1120_);
                    v___x_1145_ = lean_box(1);
                    lean_inc(v___x_1109_);
                    v_it_1113_ = v___x_1145_;
                    v_startInclusive_1114_ = v_currPos_1119_;
                    v_endExclusive_1115_ = v___x_1109_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v_a_1110_ = v___x_1133_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1142_ = lean_ctor_get(v_slice_1139_, 0);
                lean_inc(v_startInclusive_1142_);
                v_endExclusive_1143_ = lean_ctor_get(v_slice_1139_, 1);
                lean_inc(v_endExclusive_1143_);
                lean_dec_ref(v_slice_1139_);
                v_it_1113_ = v_nextIt_1141_;
                v_startInclusive_1114_ = v_startInclusive_1142_;
                v_endExclusive_1115_ = v_endExclusive_1143_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg___boxed(
    mut v_t_1147_: *mut LeanObject,
    mut v___x_1148_: *mut LeanObject,
    mut v___x_1149_: *mut LeanObject,
    mut v_a_1150_: *mut LeanObject,
    mut v_b_1151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1152_: *mut LeanObject = core::ptr::null_mut();
    v_res_1152_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_1147_, v___x_1148_, v___x_1149_, v_a_1150_, v_b_1151_);
    lean_dec_ref(v___x_1148_);
    return v_res_1152_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(
    mut v_head_1153_: *mut LeanObject,
    mut v_a_1154_: *mut LeanObject,
    mut v_b_1155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: u8 = 0;
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1156_ = lean_ctor_get(v_head_1153_, 0);
                v_startInclusive_1157_ = lean_ctor_get(v_head_1153_, 1);
                v_endExclusive_1158_ = lean_ctor_get(v_head_1153_, 2);
                v___x_1159_ = lean_nat_sub(v_endExclusive_1158_, v_startInclusive_1157_);
                v___x_1160_ = lean_nat_dec_eq(v_a_1154_, v___x_1159_);
                lean_dec(v___x_1159_);
                if v___x_1160_ == 0 {
                    v___x_1161_ = lean_nat_add(v_startInclusive_1157_, v_a_1154_);
                    lean_dec(v_a_1154_);
                    v___x_1162_ = lean_string_utf8_next_fast(v_str_1156_, v___x_1161_);
                    lean_dec(v___x_1161_);
                    v___x_1163_ = lean_nat_sub(v___x_1162_, v_startInclusive_1157_);
                    v___x_1164_ = lean_unsigned_to_nat(1);
                    v___x_1165_ = lean_nat_add(v_b_1155_, v___x_1164_);
                    lean_dec(v_b_1155_);
                    v_a_1154_ = v___x_1163_;
                    v_b_1155_ = v___x_1165_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_1154_);
                    return v_b_1155_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg___boxed(
    mut v_head_1167_: *mut LeanObject,
    mut v_a_1168_: *mut LeanObject,
    mut v_b_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1170_: *mut LeanObject = core::ptr::null_mut();
    v_res_1170_ =
        l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(
            v_head_1167_,
            v_a_1168_,
            v_b_1169_,
        );
    lean_dec_ref(v_head_1167_);
    return v_res_1170_;
}
pub unsafe fn l_Lake_Toml_Time_ofString_x3f(mut v_t_1173_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1230_: u8 = 0;
    let mut v_hour_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1236_: u8 = 0;
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1247_: u8 = 0;
    let mut v_unused_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1250_: u8 = 0;
    let mut v___x_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1174_ = lean_unsigned_to_nat(0);
                v___x_1175_ = lean_string_utf8_byte_size(v_t_1173_);
                lean_inc_ref(v_t_1173_);
                v___x_1176_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1176_, 0, v_t_1173_);
                lean_ctor_set(v___x_1176_, 1, v___x_1174_);
                lean_ctor_set(v___x_1176_, 2, v___x_1175_);
                v___x_1177_ =
                    l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0(
                        v___x_1176_,
                    );
                v___x_1178_ = l_Lake_Toml_Time_ofString_x3f___closed__0;
                v___x_1179_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_1173_, v___x_1176_, v___x_1175_, v___x_1177_, v___x_1178_);
                lean_dec_ref_known(v___x_1176_, 3);
                v___x_1180_ = lean_array_to_list(v___x_1179_);
                if lean_obj_tag(v___x_1180_) == 1 {
                    v_tail_1181_ = lean_ctor_get(v___x_1180_, 1);
                    lean_inc(v_tail_1181_);
                    if lean_obj_tag(v_tail_1181_) == 1 {
                        v_tail_1182_ = lean_ctor_get(v_tail_1181_, 1);
                        if lean_obj_tag(v_tail_1182_) == 0 {
                            v_head_1183_ = lean_ctor_get(v___x_1180_, 0);
                            lean_inc(v_head_1183_);
                            lean_dec_ref_known(v___x_1180_, 2);
                            v_head_1184_ = lean_ctor_get(v_tail_1181_, 0);
                            lean_inc(v_head_1184_);
                            lean_dec_ref_known(v_tail_1181_, 2);
                            v___x_1185_ = l_String_Slice_toNat_x3f(v_head_1183_);
                            lean_dec(v_head_1183_);
                            if lean_obj_tag(v___x_1185_) == 0 {
                                lean_dec(v_head_1184_);
                                v___x_1186_ = lean_box(0);
                                return v___x_1186_;
                            } else {
                                v_val_1187_ = lean_ctor_get(v___x_1185_, 0);
                                lean_inc(v_val_1187_);
                                lean_dec_ref_known(v___x_1185_, 1);
                                v___x_1188_ = l_String_Slice_toNat_x3f(v_head_1184_);
                                lean_dec(v_head_1184_);
                                if lean_obj_tag(v___x_1188_) == 0 {
                                    lean_dec(v_val_1187_);
                                    v___x_1189_ = lean_box(0);
                                    return v___x_1189_;
                                } else {
                                    v_val_1190_ = lean_ctor_get(v___x_1188_, 0);
                                    lean_inc(v_val_1190_);
                                    lean_dec_ref_known(v___x_1188_, 1);
                                    v___x_1191_ = l_Lake_Toml_Time_ofValid_x3f(
                                        v_val_1187_,
                                        v_val_1190_,
                                        v___x_1174_,
                                    );
                                    return v___x_1191_;
                                }
                            }
                        } else {
                            lean_inc_ref(v_tail_1182_);
                            v_tail_1192_ = lean_ctor_get(v_tail_1182_, 1);
                            if lean_obj_tag(v_tail_1192_) == 0 {
                                v_head_1193_ = lean_ctor_get(v___x_1180_, 0);
                                lean_inc(v_head_1193_);
                                lean_dec_ref_known(v___x_1180_, 2);
                                v_head_1194_ = lean_ctor_get(v_tail_1181_, 0);
                                lean_inc(v_head_1194_);
                                lean_dec_ref_known(v_tail_1181_, 2);
                                v_head_1195_ = lean_ctor_get(v_tail_1182_, 0);
                                lean_inc(v_head_1195_);
                                lean_dec_ref_known(v_tail_1182_, 2);
                                v___x_1196_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__2(v_head_1195_);
                                v___x_1197_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_1195_, v___x_1196_, v___x_1178_);
                                lean_dec(v_head_1195_);
                                v___x_1198_ = lean_array_to_list(v___x_1197_);
                                if lean_obj_tag(v___x_1198_) == 1 {
                                    v_tail_1199_ = lean_ctor_get(v___x_1198_, 1);
                                    lean_inc(v_tail_1199_);
                                    if lean_obj_tag(v_tail_1199_) == 0 {
                                        v_head_1200_ = lean_ctor_get(v___x_1198_, 0);
                                        lean_inc(v_head_1200_);
                                        lean_dec_ref_known(v___x_1198_, 2);
                                        v___x_1201_ = l_String_Slice_toNat_x3f(v_head_1193_);
                                        lean_dec(v_head_1193_);
                                        if lean_obj_tag(v___x_1201_) == 0 {
                                            lean_dec(v_head_1200_);
                                            lean_dec(v_head_1194_);
                                            v___x_1202_ = lean_box(0);
                                            return v___x_1202_;
                                        } else {
                                            v_val_1203_ = lean_ctor_get(v___x_1201_, 0);
                                            lean_inc(v_val_1203_);
                                            lean_dec_ref_known(v___x_1201_, 1);
                                            v___x_1204_ = l_String_Slice_toNat_x3f(v_head_1194_);
                                            lean_dec(v_head_1194_);
                                            if lean_obj_tag(v___x_1204_) == 0 {
                                                lean_dec(v_val_1203_);
                                                lean_dec(v_head_1200_);
                                                v___x_1205_ = lean_box(0);
                                                return v___x_1205_;
                                            } else {
                                                v_val_1206_ = lean_ctor_get(v___x_1204_, 0);
                                                lean_inc(v_val_1206_);
                                                lean_dec_ref_known(v___x_1204_, 1);
                                                v___x_1207_ =
                                                    l_String_Slice_toNat_x3f(v_head_1200_);
                                                lean_dec(v_head_1200_);
                                                if lean_obj_tag(v___x_1207_) == 0 {
                                                    lean_dec(v_val_1206_);
                                                    lean_dec(v_val_1203_);
                                                    v___x_1208_ = lean_box(0);
                                                    return v___x_1208_;
                                                } else {
                                                    v_val_1209_ = lean_ctor_get(v___x_1207_, 0);
                                                    lean_inc(v_val_1209_);
                                                    lean_dec_ref_known(v___x_1207_, 1);
                                                    v___x_1210_ = l_Lake_Toml_Time_ofValid_x3f(
                                                        v_val_1203_,
                                                        v_val_1206_,
                                                        v_val_1209_,
                                                    );
                                                    return v___x_1210_;
                                                }
                                            }
                                        }
                                    } else {
                                        v_tail_1211_ = lean_ctor_get(v_tail_1199_, 1);
                                        if lean_obj_tag(v_tail_1211_) == 0 {
                                            v_head_1212_ = lean_ctor_get(v___x_1198_, 0);
                                            lean_inc(v_head_1212_);
                                            lean_dec_ref_known(v___x_1198_, 2);
                                            v_head_1213_ = lean_ctor_get(v_tail_1199_, 0);
                                            lean_inc(v_head_1213_);
                                            lean_dec_ref_known(v_tail_1199_, 2);
                                            v___x_1214_ = l_String_Slice_toNat_x3f(v_head_1193_);
                                            lean_dec(v_head_1193_);
                                            if lean_obj_tag(v___x_1214_) == 0 {
                                                lean_dec(v_head_1213_);
                                                lean_dec(v_head_1212_);
                                                lean_dec(v_head_1194_);
                                                v___x_1215_ = lean_box(0);
                                                return v___x_1215_;
                                            } else {
                                                v_val_1216_ = lean_ctor_get(v___x_1214_, 0);
                                                lean_inc(v_val_1216_);
                                                lean_dec_ref_known(v___x_1214_, 1);
                                                v___x_1217_ =
                                                    l_String_Slice_toNat_x3f(v_head_1194_);
                                                lean_dec(v_head_1194_);
                                                if lean_obj_tag(v___x_1217_) == 0 {
                                                    lean_dec(v_val_1216_);
                                                    lean_dec(v_head_1213_);
                                                    lean_dec(v_head_1212_);
                                                    v___x_1218_ = lean_box(0);
                                                    return v___x_1218_;
                                                } else {
                                                    v_val_1219_ = lean_ctor_get(v___x_1217_, 0);
                                                    lean_inc(v_val_1219_);
                                                    lean_dec_ref_known(v___x_1217_, 1);
                                                    v___x_1220_ =
                                                        l_String_Slice_toNat_x3f(v_head_1212_);
                                                    lean_dec(v_head_1212_);
                                                    if lean_obj_tag(v___x_1220_) == 0 {
                                                        lean_dec(v_val_1219_);
                                                        lean_dec(v_val_1216_);
                                                        lean_dec(v_head_1213_);
                                                        v___x_1221_ = lean_box(0);
                                                        return v___x_1221_;
                                                    } else {
                                                        v_val_1222_ = lean_ctor_get(v___x_1220_, 0);
                                                        lean_inc(v_val_1222_);
                                                        lean_dec_ref_known(v___x_1220_, 1);
                                                        v___x_1223_ = l_Lake_Toml_Time_ofValid_x3f(
                                                            v_val_1216_,
                                                            v_val_1219_,
                                                            v_val_1222_,
                                                        );
                                                        if lean_obj_tag(v___x_1223_) == 0 {
                                                            lean_dec(v_head_1213_);
                                                            return v___x_1223_;
                                                        } else {
                                                            v_val_1224_ =
                                                                lean_ctor_get(v___x_1223_, 0);
                                                            lean_inc(v_val_1224_);
                                                            lean_dec_ref_known(v___x_1223_, 1);
                                                            v___x_1225_ = l_String_Slice_toNat_x3f(
                                                                v_head_1213_,
                                                            );
                                                            if lean_obj_tag(v___x_1225_) == 0 {
                                                                lean_dec(v_val_1224_);
                                                                lean_dec(v_head_1213_);
                                                                v___x_1226_ = lean_box(0);
                                                                return v___x_1226_;
                                                            } else {
                                                                v_val_1227_ =
                                                                    lean_ctor_get(v___x_1225_, 0);
                                                                v_isSharedCheck_1250_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_1225_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_1250_ == 0 {
                                                                    v___x_1229_ = v___x_1225_;
                                                                    v_isShared_1230_ =
                                                                        v_isSharedCheck_1250_;
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_val_1227_);
                                                                    lean_dec(v___x_1225_);
                                                                    v___x_1229_ = lean_box(0);
                                                                    v_isShared_1230_ =
                                                                        v_isSharedCheck_1250_;
                                                                    state = 1;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref_known(v_tail_1199_, 2);
                                            lean_dec_ref_known(v___x_1198_, 2);
                                            lean_dec(v_head_1194_);
                                            lean_dec(v_head_1193_);
                                            v___x_1251_ = lean_box(0);
                                            return v___x_1251_;
                                        }
                                    }
                                } else {
                                    lean_dec(v___x_1198_);
                                    lean_dec(v_head_1194_);
                                    lean_dec(v_head_1193_);
                                    v___x_1252_ = lean_box(0);
                                    return v___x_1252_;
                                }
                            } else {
                                lean_dec_ref_known(v_tail_1182_, 2);
                                lean_dec_ref_known(v_tail_1181_, 2);
                                lean_dec_ref_known(v___x_1180_, 2);
                                v___x_1253_ = lean_box(0);
                                return v___x_1253_;
                            }
                        }
                    } else {
                        lean_dec(v_tail_1181_);
                        lean_dec_ref_known(v___x_1180_, 2);
                        v___x_1254_ = lean_box(0);
                        return v___x_1254_;
                    }
                } else {
                    lean_dec(v___x_1180_);
                    v___x_1255_ = lean_box(0);
                    return v___x_1255_;
                }
            }
            1 => {
                v_hour_1231_ = lean_ctor_get(v_val_1224_, 0);
                v_minute_1232_ = lean_ctor_get(v_val_1224_, 1);
                v_second_1233_ = lean_ctor_get(v_val_1224_, 2);
                v_isSharedCheck_1247_ = (!lean_is_exclusive(v_val_1224_)) as u8;
                if v_isSharedCheck_1247_ == 0 {
                    v_unused_1248_ = lean_ctor_get(v_val_1224_, 4);
                    lean_dec(v_unused_1248_);
                    v_unused_1249_ = lean_ctor_get(v_val_1224_, 3);
                    lean_dec(v_unused_1249_);
                    v___x_1235_ = v_val_1224_;
                    v_isShared_1236_ = v_isSharedCheck_1247_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_second_1233_);
                    lean_inc(v_minute_1232_);
                    lean_inc(v_hour_1231_);
                    lean_dec(v_val_1224_);
                    v___x_1235_ = lean_box(0);
                    v_isShared_1236_ = v_isSharedCheck_1247_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1237_ = l_String_Slice_positions(v_head_1213_);
                v___x_1238_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(v_head_1213_, v___x_1237_, v___x_1174_);
                lean_dec(v_head_1213_);
                v___x_1239_ = lean_unsigned_to_nat(1);
                v___x_1240_ = lean_nat_sub(v___x_1238_, v___x_1239_);
                lean_dec(v___x_1238_);
                if v_isShared_1236_ == 0 {
                    lean_ctor_set(v___x_1235_, 4, v_val_1227_);
                    lean_ctor_set(v___x_1235_, 3, v___x_1240_);
                    v___x_1242_ = v___x_1235_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_hour_1231_);
                    lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_minute_1232_);
                    lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_second_1233_);
                    lean_ctor_set(v_reuseFailAlloc_1246_, 3, v___x_1240_);
                    lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_val_1227_);
                    v___x_1242_ = v_reuseFailAlloc_1246_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1230_ == 0 {
                    lean_ctor_set(v___x_1229_, 0, v___x_1242_);
                    v___x_1244_ = v___x_1229_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
                    v___x_1244_ = v_reuseFailAlloc_1245_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(
    mut v_t_1256_: *mut LeanObject,
    mut v___x_1257_: *mut LeanObject,
    mut v___x_1258_: *mut LeanObject,
    mut v_inst_1259_: *mut LeanObject,
    mut v_R_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
    mut v_b_1262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    v___x_1263_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___redArg(v_t_1256_, v___x_1257_, v___x_1258_, v_a_1261_, v_b_1262_);
    return v___x_1263_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1___boxed(
    mut v_t_1264_: *mut LeanObject,
    mut v___x_1265_: *mut LeanObject,
    mut v___x_1266_: *mut LeanObject,
    mut v_inst_1267_: *mut LeanObject,
    mut v_R_1268_: *mut LeanObject,
    mut v_a_1269_: *mut LeanObject,
    mut v_b_1270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1271_: *mut LeanObject = core::ptr::null_mut();
    v_res_1271_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__1(v_t_1264_, v___x_1265_, v___x_1266_, v_inst_1267_, v_R_1268_, v_a_1269_, v_b_1270_);
    lean_dec_ref(v___x_1265_);
    return v_res_1271_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(
    mut v_head_1272_: *mut LeanObject,
    mut v_inst_1273_: *mut LeanObject,
    mut v_R_1274_: *mut LeanObject,
    mut v_a_1275_: *mut LeanObject,
    mut v_b_1276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    v___x_1277_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___redArg(v_head_1272_, v_a_1275_, v_b_1276_);
    return v___x_1277_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3___boxed(
    mut v_head_1278_: *mut LeanObject,
    mut v_inst_1279_: *mut LeanObject,
    mut v_R_1280_: *mut LeanObject,
    mut v_a_1281_: *mut LeanObject,
    mut v_b_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1283_: *mut LeanObject = core::ptr::null_mut();
    v_res_1283_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_Time_ofString_x3f_spec__3(v_head_1278_, v_inst_1279_, v_R_1280_, v_a_1281_, v_b_1282_);
    lean_dec_ref(v_head_1278_);
    return v_res_1283_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(
    mut v_head_1284_: *mut LeanObject,
    mut v_inst_1285_: *mut LeanObject,
    mut v_R_1286_: *mut LeanObject,
    mut v_a_1287_: *mut LeanObject,
    mut v_b_1288_: *mut LeanObject,
    mut v_c_1289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
    v___x_1290_ =
        l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___redArg(
            v_head_1284_,
            v_a_1287_,
            v_b_1288_,
        );
    return v___x_1290_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4___boxed(
    mut v_head_1291_: *mut LeanObject,
    mut v_inst_1292_: *mut LeanObject,
    mut v_R_1293_: *mut LeanObject,
    mut v_a_1294_: *mut LeanObject,
    mut v_b_1295_: *mut LeanObject,
    mut v_c_1296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1297_: *mut LeanObject = core::ptr::null_mut();
    v_res_1297_ = l_WellFounded_opaqueFix_u2083___at___00Lake_Toml_Time_ofString_x3f_spec__4(
        v_head_1291_,
        v_inst_1292_,
        v_R_1293_,
        v_a_1294_,
        v_b_1295_,
        v_c_1296_,
    );
    lean_dec_ref(v_head_1291_);
    return v_res_1297_;
}
pub unsafe fn l_Lake_Toml_Time_toString(mut v_t_1300_: *mut LeanObject) -> *mut LeanObject {
    let mut v_hour_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_minute_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_second_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fracExponent_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fracMantissa_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: u8 = 0;
    v_hour_1301_ = lean_ctor_get(v_t_1300_, 0);
    lean_inc(v_hour_1301_);
    v_minute_1302_ = lean_ctor_get(v_t_1300_, 1);
    lean_inc(v_minute_1302_);
    v_second_1303_ = lean_ctor_get(v_t_1300_, 2);
    lean_inc(v_second_1303_);
    v_fracExponent_1304_ = lean_ctor_get(v_t_1300_, 3);
    lean_inc(v_fracExponent_1304_);
    v_fracMantissa_1305_ = lean_ctor_get(v_t_1300_, 4);
    lean_inc(v_fracMantissa_1305_);
    lean_dec_ref(v_t_1300_);
    v___x_1306_ = lean_unsigned_to_nat(2);
    v___x_1307_ = l_Lake_zpad(v_hour_1301_, v___x_1306_);
    v___x_1308_ = l_Lake_Toml_Time_toString___closed__0;
    v___x_1309_ = lean_string_append(v___x_1307_, v___x_1308_);
    v___x_1310_ = l_Lake_zpad(v_minute_1302_, v___x_1306_);
    v___x_1311_ = lean_string_append(v___x_1309_, v___x_1310_);
    lean_dec_ref(v___x_1310_);
    v___x_1312_ = lean_string_append(v___x_1311_, v___x_1308_);
    v___x_1313_ = l_Lake_zpad(v_second_1303_, v___x_1306_);
    v_s_1314_ = lean_string_append(v___x_1312_, v___x_1313_);
    lean_dec_ref(v___x_1313_);
    v___x_1315_ = lean_unsigned_to_nat(0);
    v___x_1316_ = lean_nat_dec_eq(v_fracMantissa_1305_, v___x_1315_);
    if v___x_1316_ == 0 {
        let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1320_: u32 = 0;
        let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
        v___x_1317_ = l_Lake_Toml_Time_toString___closed__1;
        v___x_1318_ = lean_string_append(v_s_1314_, v___x_1317_);
        v___x_1319_ = l_Lake_zpad(v_fracMantissa_1305_, v_fracExponent_1304_);
        lean_dec(v_fracExponent_1304_);
        v___x_1320_ = 48;
        v___x_1321_ = lean_unsigned_to_nat(3);
        v___x_1322_ = l_Lake_rpadAscii(v___x_1319_, v___x_1320_, v___x_1321_);
        v___x_1323_ = lean_string_append(v___x_1318_, v___x_1322_);
        lean_dec_ref(v___x_1322_);
        return v___x_1323_;
    } else {
        lean_dec(v_fracMantissa_1305_);
        lean_dec(v_fracExponent_1304_);
        return v_s_1314_;
    }
}
pub unsafe fn l_Lake_Toml_DateTime_ctorIdx(mut v_x_1326_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_x_1326_) {
        0 => {
            let mut v___x_1327_: *mut LeanObject = core::ptr::null_mut();
            v___x_1327_ = lean_unsigned_to_nat(0);
            return v___x_1327_;
        }
        1 => {
            let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
            v___x_1328_ = lean_unsigned_to_nat(1);
            return v___x_1328_;
        }
        2 => {
            let mut v___x_1329_: *mut LeanObject = core::ptr::null_mut();
            v___x_1329_ = lean_unsigned_to_nat(2);
            return v___x_1329_;
        }
        _ => {
            let mut v___x_1330_: *mut LeanObject = core::ptr::null_mut();
            v___x_1330_ = lean_unsigned_to_nat(3);
            return v___x_1330_;
        }
    }
}
pub unsafe fn l_Lake_Toml_DateTime_ctorIdx___boxed(
    mut v_x_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1332_: *mut LeanObject = core::ptr::null_mut();
    v_res_1332_ = l_Lake_Toml_DateTime_ctorIdx(v_x_1331_);
    lean_dec_ref(v_x_1331_);
    return v_res_1332_;
}
pub unsafe fn l_Lake_Toml_DateTime_ctorElim___redArg(
    mut v_t_1333_: *mut LeanObject,
    mut v_k_1334_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1333_) {
        0 => {
            let mut v_date_1335_: *mut LeanObject = core::ptr::null_mut();
            let mut v_time_1336_: *mut LeanObject = core::ptr::null_mut();
            let mut v_offset_x3f_1337_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
            v_date_1335_ = lean_ctor_get(v_t_1333_, 0);
            lean_inc_ref(v_date_1335_);
            v_time_1336_ = lean_ctor_get(v_t_1333_, 1);
            lean_inc_ref(v_time_1336_);
            v_offset_x3f_1337_ = lean_ctor_get(v_t_1333_, 2);
            lean_inc(v_offset_x3f_1337_);
            lean_dec_ref_known(v_t_1333_, 3);
            v___x_1338_ = lean_apply_3(v_k_1334_, v_date_1335_, v_time_1336_, v_offset_x3f_1337_);
            return v___x_1338_;
        }
        1 => {
            let mut v_date_1339_: *mut LeanObject = core::ptr::null_mut();
            let mut v_time_1340_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
            v_date_1339_ = lean_ctor_get(v_t_1333_, 0);
            lean_inc_ref(v_date_1339_);
            v_time_1340_ = lean_ctor_get(v_t_1333_, 1);
            lean_inc_ref(v_time_1340_);
            lean_dec_ref_known(v_t_1333_, 2);
            v___x_1341_ = lean_apply_2(v_k_1334_, v_date_1339_, v_time_1340_);
            return v___x_1341_;
        }
        _ => {
            let mut v_date_1342_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
            v_date_1342_ = lean_ctor_get(v_t_1333_, 0);
            lean_inc_ref(v_date_1342_);
            lean_dec_ref(v_t_1333_);
            v___x_1343_ = lean_apply_1(v_k_1334_, v_date_1342_);
            return v___x_1343_;
        }
    }
}
pub unsafe fn l_Lake_Toml_DateTime_ctorElim(
    mut v_motive_1344_: *mut LeanObject,
    mut v_ctorIdx_1345_: *mut LeanObject,
    mut v_t_1346_: *mut LeanObject,
    mut v_h_1347_: *mut LeanObject,
    mut v_k_1348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    v___x_1349_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_1346_, v_k_1348_);
    return v___x_1349_;
}
pub unsafe fn l_Lake_Toml_DateTime_ctorElim___boxed(
    mut v_motive_1350_: *mut LeanObject,
    mut v_ctorIdx_1351_: *mut LeanObject,
    mut v_t_1352_: *mut LeanObject,
    mut v_h_1353_: *mut LeanObject,
    mut v_k_1354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1355_: *mut LeanObject = core::ptr::null_mut();
    v_res_1355_ = l_Lake_Toml_DateTime_ctorElim(
        v_motive_1350_,
        v_ctorIdx_1351_,
        v_t_1352_,
        v_h_1353_,
        v_k_1354_,
    );
    lean_dec(v_ctorIdx_1351_);
    return v_res_1355_;
}
pub unsafe fn l_Lake_Toml_DateTime_offsetDateTime_elim___redArg(
    mut v_t_1356_: *mut LeanObject,
    mut v_offsetDateTime_1357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    v___x_1358_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_1356_, v_offsetDateTime_1357_);
    return v___x_1358_;
}
pub unsafe fn l_Lake_Toml_DateTime_offsetDateTime_elim(
    mut v_motive_1359_: *mut LeanObject,
    mut v_t_1360_: *mut LeanObject,
    mut v_h_1361_: *mut LeanObject,
    mut v_offsetDateTime_1362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    v___x_1363_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_1360_, v_offsetDateTime_1362_);
    return v___x_1363_;
}
pub unsafe fn l_Lake_Toml_DateTime_localDateTime_elim___redArg(
    mut v_t_1364_: *mut LeanObject,
    mut v_localDateTime_1365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    v___x_1366_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_1364_, v_localDateTime_1365_);
    return v___x_1366_;
}
pub unsafe fn l_Lake_Toml_DateTime_localDateTime_elim(
    mut v_motive_1367_: *mut LeanObject,
    mut v_t_1368_: *mut LeanObject,
    mut v_h_1369_: *mut LeanObject,
    mut v_localDateTime_1370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    v___x_1371_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_1368_, v_localDateTime_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Lake_Toml_DateTime_localDate_elim___redArg(
    mut v_t_1372_: *mut LeanObject,
    mut v_localDate_1373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    v___x_1374_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_1372_, v_localDate_1373_);
    return v___x_1374_;
}
pub unsafe fn l_Lake_Toml_DateTime_localDate_elim(
    mut v_motive_1375_: *mut LeanObject,
    mut v_t_1376_: *mut LeanObject,
    mut v_h_1377_: *mut LeanObject,
    mut v_localDate_1378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    v___x_1379_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_1376_, v_localDate_1378_);
    return v___x_1379_;
}
pub unsafe fn l_Lake_Toml_DateTime_localTime_elim___redArg(
    mut v_t_1380_: *mut LeanObject,
    mut v_localTime_1381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    v___x_1382_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_1380_, v_localTime_1381_);
    return v___x_1382_;
}
pub unsafe fn l_Lake_Toml_DateTime_localTime_elim(
    mut v_motive_1383_: *mut LeanObject,
    mut v_t_1384_: *mut LeanObject,
    mut v_h_1385_: *mut LeanObject,
    mut v_localTime_1386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1387_: *mut LeanObject = core::ptr::null_mut();
    v___x_1387_ = l_Lake_Toml_DateTime_ctorElim___redArg(v_t_1384_, v_localTime_1386_);
    return v___x_1387_;
}
pub unsafe fn _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0() -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    v___x_1388_ = lean_box(0);
    v___x_1389_ = l_Lake_Toml_instInhabitedTime_default;
    v___x_1390_ = l_Lake_instInhabitedDate_default;
    v___x_1391_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1391_, 0, v___x_1390_);
    lean_ctor_set(v___x_1391_, 1, v___x_1389_);
    lean_ctor_set(v___x_1391_, 2, v___x_1388_);
    return v___x_1391_;
}
pub unsafe fn _init_l_Lake_Toml_instInhabitedDateTime_default() -> *mut LeanObject {
    let mut v___x_1392_: *mut LeanObject = core::ptr::null_mut();
    v___x_1392_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_Toml_instInhabitedDateTime_default___closed__0),
        core::ptr::addr_of_mut!(l_Lake_Toml_instInhabitedDateTime_default___closed__0_once),
        _init_l_Lake_Toml_instInhabitedDateTime_default___closed__0,
    );
    return v___x_1392_;
}
pub unsafe fn _init_l_Lake_Toml_instInhabitedDateTime() -> *mut LeanObject {
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    v___x_1393_ = l_Lake_Toml_instInhabitedDateTime_default;
    return v___x_1393_;
}
pub unsafe fn l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(
    mut v___x_1394_: u8,
    mut v___y_1395_: u8,
    mut v___y_1396_: u8,
) -> u8 {
    if v___y_1395_ == 0 {
        if v___y_1396_ == 0 {
            return v___x_1394_;
        } else {
            return v___y_1395_;
        }
    } else {
        return v___y_1396_;
    }
}
pub unsafe fn l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed(
    mut v___x_1397_: *mut LeanObject,
    mut v___y_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_270__boxed_1400_: u8 = 0;
    let mut v___y_271__boxed_1401_: u8 = 0;
    let mut v___y_272__boxed_1402_: u8 = 0;
    let mut v_res_1403_: u8 = 0;
    let mut v_r_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_270__boxed_1400_ = (lean_unbox(v___x_1397_) as u8);
    v___y_271__boxed_1401_ = (lean_unbox(v___y_1398_) as u8);
    v___y_272__boxed_1402_ = (lean_unbox(v___y_1399_) as u8);
    v_res_1403_ = l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0(
        v___x_270__boxed_1400_,
        v___y_271__boxed_1401_,
        v___y_272__boxed_1402_,
    );
    v_r_1404_ = lean_box((v_res_1403_) as usize);
    return v_r_1404_;
}
pub unsafe fn l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(
    mut v___f_1405_: *mut LeanObject,
    mut v_a_1406_: *mut LeanObject,
    mut v_b_1407_: *mut LeanObject,
) -> u8 {
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: u8 = 0;
    v___x_1408_ = lean_alloc_closure(
        l_Lake_Toml_instDecidableEqTime___boxed as *mut core::ffi::c_void,
        2,
        0,
    );
    v___x_1409_ = l_instDecidableEqProd___redArg(v___f_1405_, v___x_1408_, v_a_1406_, v_b_1407_);
    return v___x_1409_;
}
pub unsafe fn l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed(
    mut v___f_1410_: *mut LeanObject,
    mut v_a_1411_: *mut LeanObject,
    mut v_b_1412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1413_: u8 = 0;
    let mut v_r_1414_: *mut LeanObject = core::ptr::null_mut();
    v_res_1413_ =
        l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1(v___f_1410_, v_a_1411_, v_b_1412_);
    v_r_1414_ = lean_box((v_res_1413_) as usize);
    return v_r_1414_;
}
pub unsafe fn l_Lake_Toml_instDecidableEqDateTime_decEq(
    mut v_x_1415_: *mut LeanObject,
    mut v_x_1416_: *mut LeanObject,
) -> u8 {
    match lean_obj_tag(v_x_1415_) {
        0 => {
            if lean_obj_tag(v_x_1416_) == 0 {
                let mut v_date_1417_: *mut LeanObject = core::ptr::null_mut();
                let mut v_time_1418_: *mut LeanObject = core::ptr::null_mut();
                let mut v_offset_x3f_1419_: *mut LeanObject = core::ptr::null_mut();
                let mut v_date_1420_: *mut LeanObject = core::ptr::null_mut();
                let mut v_time_1421_: *mut LeanObject = core::ptr::null_mut();
                let mut v_offset_x3f_1422_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1423_: u8 = 0;
                v_date_1417_ = lean_ctor_get(v_x_1415_, 0);
                lean_inc_ref(v_date_1417_);
                v_time_1418_ = lean_ctor_get(v_x_1415_, 1);
                lean_inc_ref(v_time_1418_);
                v_offset_x3f_1419_ = lean_ctor_get(v_x_1415_, 2);
                lean_inc(v_offset_x3f_1419_);
                lean_dec_ref_known(v_x_1415_, 3);
                v_date_1420_ = lean_ctor_get(v_x_1416_, 0);
                lean_inc_ref(v_date_1420_);
                v_time_1421_ = lean_ctor_get(v_x_1416_, 1);
                lean_inc_ref(v_time_1421_);
                v_offset_x3f_1422_ = lean_ctor_get(v_x_1416_, 2);
                lean_inc(v_offset_x3f_1422_);
                lean_dec_ref_known(v_x_1416_, 3);
                v___x_1423_ = l_Lake_instDecidableEqDate_decEq(v_date_1417_, v_date_1420_);
                lean_dec_ref(v_date_1420_);
                lean_dec_ref(v_date_1417_);
                if v___x_1423_ == 0 {
                    lean_dec(v_offset_x3f_1422_);
                    lean_dec_ref(v_time_1421_);
                    lean_dec(v_offset_x3f_1419_);
                    lean_dec_ref(v_time_1418_);
                    return v___x_1423_;
                } else {
                    let mut v___x_1424_: u8 = 0;
                    v___x_1424_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_1418_, v_time_1421_);
                    lean_dec_ref(v_time_1421_);
                    lean_dec_ref(v_time_1418_);
                    if v___x_1424_ == 0 {
                        lean_dec(v_offset_x3f_1422_);
                        lean_dec(v_offset_x3f_1419_);
                        return v___x_1424_;
                    } else {
                        let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___f_1426_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___f_1427_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_1428_: u8 = 0;
                        v___x_1425_ = lean_box((v___x_1424_) as usize);
                        v___f_1426_ = lean_alloc_closure(
                            l_Lake_Toml_instDecidableEqDateTime_decEq___lam__0___boxed
                                as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        lean_closure_set(v___f_1426_, 0, v___x_1425_);
                        v___f_1427_ = lean_alloc_closure(
                            l_Lake_Toml_instDecidableEqDateTime_decEq___lam__1___boxed
                                as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        lean_closure_set(v___f_1427_, 0, v___f_1426_);
                        v___x_1428_ = l_Option_instDecidableEq___redArg(
                            v___f_1427_,
                            v_offset_x3f_1419_,
                            v_offset_x3f_1422_,
                        );
                        return v___x_1428_;
                    }
                }
            } else {
                let mut v___x_1429_: u8 = 0;
                lean_dec_ref_known(v_x_1415_, 3);
                lean_dec_ref(v_x_1416_);
                v___x_1429_ = 0;
                return v___x_1429_;
            }
        }
        1 => {
            if lean_obj_tag(v_x_1416_) == 1 {
                let mut v_date_1430_: *mut LeanObject = core::ptr::null_mut();
                let mut v_time_1431_: *mut LeanObject = core::ptr::null_mut();
                let mut v_date_1432_: *mut LeanObject = core::ptr::null_mut();
                let mut v_time_1433_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1434_: u8 = 0;
                v_date_1430_ = lean_ctor_get(v_x_1415_, 0);
                lean_inc_ref(v_date_1430_);
                v_time_1431_ = lean_ctor_get(v_x_1415_, 1);
                lean_inc_ref(v_time_1431_);
                lean_dec_ref_known(v_x_1415_, 2);
                v_date_1432_ = lean_ctor_get(v_x_1416_, 0);
                lean_inc_ref(v_date_1432_);
                v_time_1433_ = lean_ctor_get(v_x_1416_, 1);
                lean_inc_ref(v_time_1433_);
                lean_dec_ref_known(v_x_1416_, 2);
                v___x_1434_ = l_Lake_instDecidableEqDate_decEq(v_date_1430_, v_date_1432_);
                lean_dec_ref(v_date_1432_);
                lean_dec_ref(v_date_1430_);
                if v___x_1434_ == 0 {
                    lean_dec_ref(v_time_1433_);
                    lean_dec_ref(v_time_1431_);
                    return v___x_1434_;
                } else {
                    let mut v___x_1435_: u8 = 0;
                    v___x_1435_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_1431_, v_time_1433_);
                    lean_dec_ref(v_time_1433_);
                    lean_dec_ref(v_time_1431_);
                    return v___x_1435_;
                }
            } else {
                let mut v___x_1436_: u8 = 0;
                lean_dec_ref_known(v_x_1415_, 2);
                lean_dec_ref(v_x_1416_);
                v___x_1436_ = 0;
                return v___x_1436_;
            }
        }
        2 => {
            if lean_obj_tag(v_x_1416_) == 2 {
                let mut v_date_1437_: *mut LeanObject = core::ptr::null_mut();
                let mut v_date_1438_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1439_: u8 = 0;
                v_date_1437_ = lean_ctor_get(v_x_1415_, 0);
                lean_inc_ref(v_date_1437_);
                lean_dec_ref_known(v_x_1415_, 1);
                v_date_1438_ = lean_ctor_get(v_x_1416_, 0);
                lean_inc_ref(v_date_1438_);
                lean_dec_ref_known(v_x_1416_, 1);
                v___x_1439_ = l_Lake_instDecidableEqDate_decEq(v_date_1437_, v_date_1438_);
                lean_dec_ref(v_date_1438_);
                lean_dec_ref(v_date_1437_);
                return v___x_1439_;
            } else {
                let mut v___x_1440_: u8 = 0;
                lean_dec_ref_known(v_x_1415_, 1);
                lean_dec_ref(v_x_1416_);
                v___x_1440_ = 0;
                return v___x_1440_;
            }
        }
        _ => {
            if lean_obj_tag(v_x_1416_) == 3 {
                let mut v_time_1441_: *mut LeanObject = core::ptr::null_mut();
                let mut v_time_1442_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1443_: u8 = 0;
                v_time_1441_ = lean_ctor_get(v_x_1415_, 0);
                lean_inc_ref(v_time_1441_);
                lean_dec_ref_known(v_x_1415_, 1);
                v_time_1442_ = lean_ctor_get(v_x_1416_, 0);
                lean_inc_ref(v_time_1442_);
                lean_dec_ref_known(v_x_1416_, 1);
                v___x_1443_ = l_Lake_Toml_instDecidableEqTime_decEq(v_time_1441_, v_time_1442_);
                lean_dec_ref(v_time_1442_);
                lean_dec_ref(v_time_1441_);
                return v___x_1443_;
            } else {
                let mut v___x_1444_: u8 = 0;
                lean_dec_ref_known(v_x_1415_, 1);
                lean_dec_ref(v_x_1416_);
                v___x_1444_ = 0;
                return v___x_1444_;
            }
        }
    }
}
pub unsafe fn l_Lake_Toml_instDecidableEqDateTime_decEq___boxed(
    mut v_x_1445_: *mut LeanObject,
    mut v_x_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1447_: u8 = 0;
    let mut v_r_1448_: *mut LeanObject = core::ptr::null_mut();
    v_res_1447_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_1445_, v_x_1446_);
    v_r_1448_ = lean_box((v_res_1447_) as usize);
    return v_r_1448_;
}
pub unsafe fn l_Lake_Toml_instDecidableEqDateTime(
    mut v_x_1449_: *mut LeanObject,
    mut v_x_1450_: *mut LeanObject,
) -> u8 {
    let mut v___x_1451_: u8 = 0;
    v___x_1451_ = l_Lake_Toml_instDecidableEqDateTime_decEq(v_x_1449_, v_x_1450_);
    return v___x_1451_;
}
pub unsafe fn l_Lake_Toml_instDecidableEqDateTime___boxed(
    mut v_x_1452_: *mut LeanObject,
    mut v_x_1453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1454_: u8 = 0;
    let mut v_r_1455_: *mut LeanObject = core::ptr::null_mut();
    v_res_1454_ = l_Lake_Toml_instDecidableEqDateTime(v_x_1452_, v_x_1453_);
    v_r_1455_ = lean_box((v_res_1454_) as usize);
    return v_r_1455_;
}
pub unsafe fn l_Lake_Toml_instCoeDateDateTime___lam__0(
    mut v_date_1456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = lean_alloc_ctor(2, 1, (0) as u32);
    lean_ctor_set(v___x_1457_, 0, v_date_1456_);
    return v___x_1457_;
}
pub unsafe fn l_Lake_Toml_instCoeTimeDateTime___lam__0(
    mut v_time_1460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    v___x_1461_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_1461_, 0, v_time_1460_);
    return v___x_1461_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(
    mut v_s_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1467_: *mut LeanObject = core::ptr::null_mut();
    v___x_1467_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___closed__0;
    return v___x_1467_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0___boxed(
    mut v_s_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1469_: *mut LeanObject = core::ptr::null_mut();
    v_res_1469_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(v_s_1468_);
    lean_dec_ref(v_s_1468_);
    return v_res_1469_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(
    mut v_s_1470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    v___x_1471_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0;
    return v___x_1471_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3___boxed(
    mut v_s_1472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1473_: *mut LeanObject = core::ptr::null_mut();
    v_res_1473_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(v_s_1472_);
    lean_dec_ref(v_s_1472_);
    return v_res_1473_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(
    mut v_s_1474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    v___x_1475_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_Time_ofString_x3f_spec__0___closed__0;
    return v___x_1475_;
}
pub unsafe fn l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5___boxed(
    mut v_s_1476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1477_: *mut LeanObject = core::ptr::null_mut();
    v_res_1477_ =
        l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(v_s_1476_);
    lean_dec_ref(v_s_1476_);
    return v_res_1477_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(
    mut v_head_1478_: *mut LeanObject,
    mut v_a_1479_: *mut LeanObject,
    mut v_b_1480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currPos_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1485_: u8 = 0;
    let mut v_str_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: u8 = 0;
    let mut v___x_1501_: u32 = 0;
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: u32 = 0;
    let mut v___x_1504_: u8 = 0;
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1479_) == 0 {
                    v_currPos_1481_ = lean_ctor_get(v_a_1479_, 0);
                    v_searcher_1482_ = lean_ctor_get(v_a_1479_, 1);
                    v_isSharedCheck_1521_ = (!lean_is_exclusive(v_a_1479_)) as u8;
                    if v_isSharedCheck_1521_ == 0 {
                        v___x_1484_ = v_a_1479_;
                        v_isShared_1485_ = v_isSharedCheck_1521_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_searcher_1482_);
                        lean_inc(v_currPos_1481_);
                        lean_dec(v_a_1479_);
                        v___x_1484_ = lean_box(0);
                        v_isShared_1485_ = v_isSharedCheck_1521_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1480_;
                }
            }
            1 => {
                v_str_1486_ = lean_ctor_get(v_head_1478_, 0);
                v_startInclusive_1487_ = lean_ctor_get(v_head_1478_, 1);
                v_endExclusive_1488_ = lean_ctor_get(v_head_1478_, 2);
                v___x_1499_ = lean_nat_sub(v_endExclusive_1488_, v_startInclusive_1487_);
                v___x_1500_ = lean_nat_dec_eq(v_searcher_1482_, v___x_1499_);
                if v___x_1500_ == 0 {
                    lean_dec(v___x_1499_);
                    v___x_1501_ = 43;
                    v___x_1502_ = lean_nat_add(v_startInclusive_1487_, v_searcher_1482_);
                    v___x_1503_ = lean_string_utf8_get_fast(v_str_1486_, v___x_1502_);
                    v___x_1504_ = lean_uint32_dec_eq(v___x_1503_, v___x_1501_);
                    if v___x_1504_ == 0 {
                        lean_dec(v_searcher_1482_);
                        v___x_1505_ = lean_string_utf8_next_fast(v_str_1486_, v___x_1502_);
                        lean_dec(v___x_1502_);
                        v___x_1506_ = lean_nat_sub(v___x_1505_, v_startInclusive_1487_);
                        if v_isShared_1485_ == 0 {
                            lean_ctor_set(v___x_1484_, 1, v___x_1506_);
                            v___x_1508_ = v___x_1484_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_currPos_1481_);
                            lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1506_);
                            v___x_1508_ = v_reuseFailAlloc_1510_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1511_ = lean_string_utf8_next_fast(v_str_1486_, v___x_1502_);
                        v___x_1512_ = lean_nat_sub(v___x_1511_, v___x_1502_);
                        lean_dec(v___x_1502_);
                        v___x_1513_ = lean_nat_add(v_searcher_1482_, v___x_1512_);
                        lean_dec(v___x_1512_);
                        v_slice_1514_ = l_String_Slice_subslice_x21(
                            v_head_1478_,
                            v_currPos_1481_,
                            v_searcher_1482_,
                        );
                        lean_inc(v___x_1513_);
                        if v_isShared_1485_ == 0 {
                            lean_ctor_set(v___x_1484_, 1, v___x_1513_);
                            lean_ctor_set(v___x_1484_, 0, v___x_1513_);
                            v_nextIt_1516_ = v___x_1484_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1519_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1519_, 0, v___x_1513_);
                            lean_ctor_set(v_reuseFailAlloc_1519_, 1, v___x_1513_);
                            v_nextIt_1516_ = v_reuseFailAlloc_1519_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1484_);
                    lean_dec(v_searcher_1482_);
                    v___x_1520_ = lean_box(1);
                    v_it_1490_ = v___x_1520_;
                    v_startInclusive_1491_ = v_currPos_1481_;
                    v_endExclusive_1492_ = v___x_1499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1493_ = lean_nat_add(v_startInclusive_1487_, v_startInclusive_1491_);
                lean_dec(v_startInclusive_1491_);
                v___x_1494_ = lean_nat_add(v_startInclusive_1487_, v_endExclusive_1492_);
                lean_dec(v_endExclusive_1492_);
                lean_inc_ref(v_str_1486_);
                v___x_1495_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1495_, 0, v_str_1486_);
                lean_ctor_set(v___x_1495_, 1, v___x_1493_);
                lean_ctor_set(v___x_1495_, 2, v___x_1494_);
                v___x_1496_ = l_String_Slice_toString(v___x_1495_);
                lean_dec_ref_known(v___x_1495_, 3);
                v___x_1497_ = lean_array_push(v_b_1480_, v___x_1496_);
                v_a_1479_ = v_it_1490_;
                v_b_1480_ = v___x_1497_;
                state = 0;
                continue;
            }
            3 => {
                v_a_1479_ = v___x_1508_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1517_ = lean_ctor_get(v_slice_1514_, 0);
                lean_inc(v_startInclusive_1517_);
                v_endExclusive_1518_ = lean_ctor_get(v_slice_1514_, 1);
                lean_inc(v_endExclusive_1518_);
                lean_dec_ref(v_slice_1514_);
                v_it_1490_ = v_nextIt_1516_;
                v_startInclusive_1491_ = v_startInclusive_1517_;
                v_endExclusive_1492_ = v_endExclusive_1518_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg___boxed(
    mut v_head_1522_: *mut LeanObject,
    mut v_a_1523_: *mut LeanObject,
    mut v_b_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1525_: *mut LeanObject = core::ptr::null_mut();
    v_res_1525_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_1522_, v_a_1523_, v_b_1524_);
    lean_dec_ref(v_head_1522_);
    return v_res_1525_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(
    mut v_dt_1526_: *mut LeanObject,
    mut v___x_1527_: *mut LeanObject,
    mut v___x_1528_: *mut LeanObject,
    mut v_a_1529_: *mut LeanObject,
    mut v_b_1530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_it_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currPos_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1557_: u32 = 0;
    let mut v___y_1559_: u8 = 0;
    let mut v___x_1560_: u32 = 0;
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: u32 = 0;
    let mut v___x_1566_: u8 = 0;
    let mut v___x_1567_: u32 = 0;
    let mut v___x_1568_: u8 = 0;
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1529_) == 0 {
                    v_currPos_1538_ = lean_ctor_get(v_a_1529_, 0);
                    v_searcher_1539_ = lean_ctor_get(v_a_1529_, 1);
                    v_isSharedCheck_1570_ = (!lean_is_exclusive(v_a_1529_)) as u8;
                    if v_isSharedCheck_1570_ == 0 {
                        v___x_1541_ = v_a_1529_;
                        v_isShared_1542_ = v_isSharedCheck_1570_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_searcher_1539_);
                        lean_inc(v_currPos_1538_);
                        lean_dec(v_a_1529_);
                        v___x_1541_ = lean_box(0);
                        v_isShared_1542_ = v_isSharedCheck_1570_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1528_);
                    lean_dec_ref(v_dt_1526_);
                    return v_b_1530_;
                }
            }
            1 => {
                lean_inc_ref(v_dt_1526_);
                v___x_1535_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1535_, 0, v_dt_1526_);
                lean_ctor_set(v___x_1535_, 1, v_startInclusive_1533_);
                lean_ctor_set(v___x_1535_, 2, v_endExclusive_1534_);
                v___x_1536_ = lean_array_push(v_b_1530_, v___x_1535_);
                v_a_1529_ = v_it_1532_;
                v_b_1530_ = v___x_1536_;
                state = 0;
                continue;
            }
            2 => {
                v_startInclusive_1553_ = lean_ctor_get(v___x_1527_, 1);
                v_endExclusive_1554_ = lean_ctor_get(v___x_1527_, 2);
                v___x_1555_ = lean_nat_sub(v_endExclusive_1554_, v_startInclusive_1553_);
                v___x_1556_ = lean_nat_dec_eq(v_searcher_1539_, v___x_1555_);
                lean_dec(v___x_1555_);
                if v___x_1556_ == 0 {
                    v___x_1557_ = lean_string_utf8_get_fast(v_dt_1526_, v_searcher_1539_);
                    v___x_1565_ = 84;
                    v___x_1566_ = lean_uint32_dec_eq(v___x_1557_, v___x_1565_);
                    if v___x_1566_ == 0 {
                        v___x_1567_ = 116;
                        v___x_1568_ = lean_uint32_dec_eq(v___x_1557_, v___x_1567_);
                        v___y_1559_ = v___x_1568_;
                        state = 5;
                        continue;
                    } else {
                        v___y_1559_ = v___x_1566_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1541_);
                    lean_dec(v_searcher_1539_);
                    v___x_1569_ = lean_box(1);
                    lean_inc(v___x_1528_);
                    v_it_1532_ = v___x_1569_;
                    v_startInclusive_1533_ = v_currPos_1538_;
                    v_endExclusive_1534_ = v___x_1528_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_1544_ = lean_string_utf8_next_fast(v_dt_1526_, v_searcher_1539_);
                v___x_1545_ = lean_nat_sub(v___x_1544_, v_searcher_1539_);
                v___x_1546_ = lean_nat_add(v_searcher_1539_, v___x_1545_);
                lean_dec(v___x_1545_);
                v_slice_1547_ =
                    l_String_Slice_subslice_x21(v___x_1527_, v_currPos_1538_, v_searcher_1539_);
                lean_inc(v___x_1546_);
                if v_isShared_1542_ == 0 {
                    lean_ctor_set(v___x_1541_, 1, v___x_1546_);
                    lean_ctor_set(v___x_1541_, 0, v___x_1546_);
                    v_nextIt_1549_ = v___x_1541_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1546_);
                    lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1546_);
                    v_nextIt_1549_ = v_reuseFailAlloc_1552_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_startInclusive_1550_ = lean_ctor_get(v_slice_1547_, 0);
                lean_inc(v_startInclusive_1550_);
                v_endExclusive_1551_ = lean_ctor_get(v_slice_1547_, 1);
                lean_inc(v_endExclusive_1551_);
                lean_dec_ref(v_slice_1547_);
                v_it_1532_ = v_nextIt_1549_;
                v_startInclusive_1533_ = v_startInclusive_1550_;
                v_endExclusive_1534_ = v_endExclusive_1551_;
                state = 1;
                continue;
            }
            5 => {
                if v___y_1559_ == 0 {
                    v___x_1560_ = 32;
                    v___x_1561_ = lean_uint32_dec_eq(v___x_1557_, v___x_1560_);
                    if v___x_1561_ == 0 {
                        lean_del_object(v___x_1541_);
                        v___x_1562_ = lean_string_utf8_next_fast(v_dt_1526_, v_searcher_1539_);
                        lean_dec(v_searcher_1539_);
                        v___x_1563_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1563_, 0, v_currPos_1538_);
                        lean_ctor_set(v___x_1563_, 1, v___x_1562_);
                        v_a_1529_ = v___x_1563_;
                        state = 0;
                        continue;
                    } else {
                        state = 3;
                        continue;
                    }
                } else {
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg___boxed(
    mut v_dt_1571_: *mut LeanObject,
    mut v___x_1572_: *mut LeanObject,
    mut v___x_1573_: *mut LeanObject,
    mut v_a_1574_: *mut LeanObject,
    mut v_b_1575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1576_: *mut LeanObject = core::ptr::null_mut();
    v_res_1576_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_1571_, v___x_1572_, v___x_1573_, v_a_1574_, v_b_1575_);
    lean_dec_ref(v___x_1572_);
    return v_res_1576_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(
    mut v_head_1577_: *mut LeanObject,
    mut v_a_1578_: *mut LeanObject,
    mut v_b_1579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_currPos_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_searcher_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v_str_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_it_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    let mut v___x_1600_: u32 = 0;
    let mut v___x_1601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: u32 = 0;
    let mut v___x_1603_: u8 = 0;
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_slice_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextIt_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1578_) == 0 {
                    v_currPos_1580_ = lean_ctor_get(v_a_1578_, 0);
                    v_searcher_1581_ = lean_ctor_get(v_a_1578_, 1);
                    v_isSharedCheck_1620_ = (!lean_is_exclusive(v_a_1578_)) as u8;
                    if v_isSharedCheck_1620_ == 0 {
                        v___x_1583_ = v_a_1578_;
                        v_isShared_1584_ = v_isSharedCheck_1620_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_searcher_1581_);
                        lean_inc(v_currPos_1580_);
                        lean_dec(v_a_1578_);
                        v___x_1583_ = lean_box(0);
                        v_isShared_1584_ = v_isSharedCheck_1620_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_1579_;
                }
            }
            1 => {
                v_str_1585_ = lean_ctor_get(v_head_1577_, 0);
                v_startInclusive_1586_ = lean_ctor_get(v_head_1577_, 1);
                v_endExclusive_1587_ = lean_ctor_get(v_head_1577_, 2);
                v___x_1598_ = lean_nat_sub(v_endExclusive_1587_, v_startInclusive_1586_);
                v___x_1599_ = lean_nat_dec_eq(v_searcher_1581_, v___x_1598_);
                if v___x_1599_ == 0 {
                    lean_dec(v___x_1598_);
                    v___x_1600_ = 45;
                    v___x_1601_ = lean_nat_add(v_startInclusive_1586_, v_searcher_1581_);
                    v___x_1602_ = lean_string_utf8_get_fast(v_str_1585_, v___x_1601_);
                    v___x_1603_ = lean_uint32_dec_eq(v___x_1602_, v___x_1600_);
                    if v___x_1603_ == 0 {
                        lean_dec(v_searcher_1581_);
                        v___x_1604_ = lean_string_utf8_next_fast(v_str_1585_, v___x_1601_);
                        lean_dec(v___x_1601_);
                        v___x_1605_ = lean_nat_sub(v___x_1604_, v_startInclusive_1586_);
                        if v_isShared_1584_ == 0 {
                            lean_ctor_set(v___x_1583_, 1, v___x_1605_);
                            v___x_1607_ = v___x_1583_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1609_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_currPos_1580_);
                            lean_ctor_set(v_reuseFailAlloc_1609_, 1, v___x_1605_);
                            v___x_1607_ = v_reuseFailAlloc_1609_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1610_ = lean_string_utf8_next_fast(v_str_1585_, v___x_1601_);
                        v___x_1611_ = lean_nat_sub(v___x_1610_, v___x_1601_);
                        lean_dec(v___x_1601_);
                        v___x_1612_ = lean_nat_add(v_searcher_1581_, v___x_1611_);
                        lean_dec(v___x_1611_);
                        v_slice_1613_ = l_String_Slice_subslice_x21(
                            v_head_1577_,
                            v_currPos_1580_,
                            v_searcher_1581_,
                        );
                        lean_inc(v___x_1612_);
                        if v_isShared_1584_ == 0 {
                            lean_ctor_set(v___x_1583_, 1, v___x_1612_);
                            lean_ctor_set(v___x_1583_, 0, v___x_1612_);
                            v_nextIt_1615_ = v___x_1583_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1612_);
                            lean_ctor_set(v_reuseFailAlloc_1618_, 1, v___x_1612_);
                            v_nextIt_1615_ = v_reuseFailAlloc_1618_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1583_);
                    lean_dec(v_searcher_1581_);
                    v___x_1619_ = lean_box(1);
                    v_it_1589_ = v___x_1619_;
                    v_startInclusive_1590_ = v_currPos_1580_;
                    v_endExclusive_1591_ = v___x_1598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1592_ = lean_nat_add(v_startInclusive_1586_, v_startInclusive_1590_);
                lean_dec(v_startInclusive_1590_);
                v___x_1593_ = lean_nat_add(v_startInclusive_1586_, v_endExclusive_1591_);
                lean_dec(v_endExclusive_1591_);
                lean_inc_ref(v_str_1585_);
                v___x_1594_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1594_, 0, v_str_1585_);
                lean_ctor_set(v___x_1594_, 1, v___x_1592_);
                lean_ctor_set(v___x_1594_, 2, v___x_1593_);
                v___x_1595_ = l_String_Slice_toString(v___x_1594_);
                lean_dec_ref_known(v___x_1594_, 3);
                v___x_1596_ = lean_array_push(v_b_1579_, v___x_1595_);
                v_a_1578_ = v_it_1589_;
                v_b_1579_ = v___x_1596_;
                state = 0;
                continue;
            }
            3 => {
                v_a_1578_ = v___x_1607_;
                state = 0;
                continue;
            }
            4 => {
                v_startInclusive_1616_ = lean_ctor_get(v_slice_1613_, 0);
                lean_inc(v_startInclusive_1616_);
                v_endExclusive_1617_ = lean_ctor_get(v_slice_1613_, 1);
                lean_inc(v_endExclusive_1617_);
                lean_dec_ref(v_slice_1613_);
                v_it_1589_ = v_nextIt_1615_;
                v_startInclusive_1590_ = v_startInclusive_1616_;
                v_endExclusive_1591_ = v_endExclusive_1617_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg___boxed(
    mut v_head_1621_: *mut LeanObject,
    mut v_a_1622_: *mut LeanObject,
    mut v_b_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1624_: *mut LeanObject = core::ptr::null_mut();
    v_res_1624_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_1621_, v_a_1622_, v_b_1623_);
    lean_dec_ref(v_head_1621_);
    return v_res_1624_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(
    mut v_s_1625_: *mut LeanObject,
    mut v_a_1626_: *mut LeanObject,
    mut v_b_1627_: u8,
) -> u8 {
    let mut v_str_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: u8 = 0;
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: u32 = 0;
    let mut v___x_1635_: u32 = 0;
    let mut v___x_1636_: u8 = 0;
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1628_ = lean_ctor_get(v_s_1625_, 0);
                v_startInclusive_1629_ = lean_ctor_get(v_s_1625_, 1);
                v_endExclusive_1630_ = lean_ctor_get(v_s_1625_, 2);
                v___x_1631_ = lean_nat_sub(v_endExclusive_1630_, v_startInclusive_1629_);
                v___x_1632_ = lean_nat_dec_eq(v_a_1626_, v___x_1631_);
                lean_dec(v___x_1631_);
                if v___x_1632_ == 0 {
                    v___x_1633_ = lean_nat_add(v_startInclusive_1629_, v_a_1626_);
                    lean_dec(v_a_1626_);
                    v___x_1634_ = lean_string_utf8_get_fast(v_str_1628_, v___x_1633_);
                    v___x_1635_ = 58;
                    v___x_1636_ = lean_uint32_dec_eq(v___x_1634_, v___x_1635_);
                    if v___x_1636_ == 0 {
                        v___x_1637_ = lean_string_utf8_next_fast(v_str_1628_, v___x_1633_);
                        lean_dec(v___x_1633_);
                        v___x_1638_ = lean_nat_sub(v___x_1637_, v_startInclusive_1629_);
                        v_a_1626_ = v___x_1638_;
                        v_b_1627_ = v___x_1636_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_1633_);
                        return v___x_1636_;
                    }
                } else {
                    lean_dec(v_a_1626_);
                    return v_b_1627_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg___boxed(
    mut v_s_1640_: *mut LeanObject,
    mut v_a_1641_: *mut LeanObject,
    mut v_b_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_1643_: u8 = 0;
    let mut v_res_1644_: u8 = 0;
    let mut v_r_1645_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_1643_ = (lean_unbox(v_b_1642_) as u8);
    v_res_1644_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_1640_, v_a_1641_, v_b_boxed_1643_);
    lean_dec_ref(v_s_1640_);
    v_r_1645_ = lean_box((v_res_1644_) as usize);
    return v_r_1645_;
}
pub unsafe fn l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(
    mut v_s_1646_: *mut LeanObject,
) -> u8 {
    let mut v_searcher_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v___x_1649_: u8 = 0;
    v_searcher_1647_ = lean_unsigned_to_nat(0);
    v___x_1648_ = 0;
    v___x_1649_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_1646_, v_searcher_1647_, v___x_1648_);
    return v___x_1649_;
}
pub unsafe fn l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2___boxed(
    mut v_s_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1651_: u8 = 0;
    let mut v_r_1652_: *mut LeanObject = core::ptr::null_mut();
    v_res_1651_ =
        l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_s_1650_);
    lean_dec_ref(v_s_1650_);
    v_r_1652_ = lean_box((v_res_1651_) as usize);
    return v_r_1652_;
}
pub unsafe fn l_Lake_Toml_DateTime_ofString_x3f(
    mut v_dt_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: u8 = 0;
    let mut v_str_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1673_: u8 = 0;
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1678_: u8 = 0;
    let mut v_str_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1688_: u8 = 0;
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1693_: u8 = 0;
    let mut v_tail_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v_str_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1717_: u8 = 0;
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1724_: u8 = 0;
    let mut v___y_1726_: u8 = 0;
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1745_: u8 = 0;
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1751_: u8 = 0;
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1765_: u8 = 0;
    let mut v_isSharedCheck_1766_: u8 = 0;
    let mut v_isSharedCheck_1767_: u8 = 0;
    let mut v_unused_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut v_unused_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1774_: u8 = 0;
    let mut v___x_1775_: u8 = 0;
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v_head_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1788_: u8 = 0;
    let mut v___x_1789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1794_: u8 = 0;
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1814_: u8 = 0;
    let mut v_isSharedCheck_1815_: u8 = 0;
    let mut v_isSharedCheck_1816_: u8 = 0;
    let mut v_unused_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1818_: u8 = 0;
    let mut v_unused_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1835_: u8 = 0;
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1843_: u8 = 0;
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_unused_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1849_: u32 = 0;
    let mut v___x_1850_: u32 = 0;
    let mut v___x_1851_: u8 = 0;
    let mut v___y_1853_: u32 = 0;
    let mut v___x_1854_: u32 = 0;
    let mut v___x_1855_: u8 = 0;
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: u32 = 0;
    let mut v_val_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: u32 = 0;
    let mut v_val_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: u32 = 0;
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: u32 = 0;
    let mut v_val_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u32 = 0;
    let mut v_val_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u32 = 0;
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v_unused_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1654_ = lean_unsigned_to_nat(0);
                v___x_1655_ = lean_string_utf8_byte_size(v_dt_1653_);
                lean_inc_ref(v_dt_1653_);
                v___x_1656_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1656_, 0, v_dt_1653_);
                lean_ctor_set(v___x_1656_, 1, v___x_1654_);
                lean_ctor_set(v___x_1656_, 2, v___x_1655_);
                v___x_1657_ =
                    l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__0(
                        v___x_1656_,
                    );
                v___x_1658_ = l_Lake_Toml_Time_ofString_x3f___closed__0;
                v___x_1659_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_1653_, v___x_1656_, v___x_1655_, v___x_1657_, v___x_1658_);
                lean_dec_ref_known(v___x_1656_, 3);
                v___x_1660_ = lean_array_to_list(v___x_1659_);
                if lean_obj_tag(v___x_1660_) == 1 {
                    v_tail_1661_ = lean_ctor_get(v___x_1660_, 1);
                    lean_inc(v_tail_1661_);
                    if lean_obj_tag(v_tail_1661_) == 0 {
                        v_head_1662_ = lean_ctor_get(v___x_1660_, 0);
                        lean_inc(v_head_1662_);
                        lean_dec_ref_known(v___x_1660_, 2);
                        v___x_1663_ = l_String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2(v_head_1662_);
                        if v___x_1663_ == 0 {
                            v_str_1664_ = lean_ctor_get(v_head_1662_, 0);
                            lean_inc_ref(v_str_1664_);
                            v_startInclusive_1665_ = lean_ctor_get(v_head_1662_, 1);
                            lean_inc(v_startInclusive_1665_);
                            v_endExclusive_1666_ = lean_ctor_get(v_head_1662_, 2);
                            lean_inc(v_endExclusive_1666_);
                            lean_dec(v_head_1662_);
                            v___x_1667_ = lean_string_utf8_extract(
                                v_str_1664_,
                                v_startInclusive_1665_,
                                v_endExclusive_1666_,
                            );
                            lean_dec(v_endExclusive_1666_);
                            lean_dec(v_startInclusive_1665_);
                            lean_dec_ref(v_str_1664_);
                            v___x_1668_ = l_Lake_Date_ofString_x3f(v___x_1667_);
                            if lean_obj_tag(v___x_1668_) == 0 {
                                v___x_1669_ = lean_box(0);
                                return v___x_1669_;
                            } else {
                                v_val_1670_ = lean_ctor_get(v___x_1668_, 0);
                                v_isSharedCheck_1678_ = (!lean_is_exclusive(v___x_1668_)) as u8;
                                if v_isSharedCheck_1678_ == 0 {
                                    v___x_1672_ = v___x_1668_;
                                    v_isShared_1673_ = v_isSharedCheck_1678_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1670_);
                                    lean_dec(v___x_1668_);
                                    v___x_1672_ = lean_box(0);
                                    v_isShared_1673_ = v_isSharedCheck_1678_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_str_1679_ = lean_ctor_get(v_head_1662_, 0);
                            lean_inc_ref(v_str_1679_);
                            v_startInclusive_1680_ = lean_ctor_get(v_head_1662_, 1);
                            lean_inc(v_startInclusive_1680_);
                            v_endExclusive_1681_ = lean_ctor_get(v_head_1662_, 2);
                            lean_inc(v_endExclusive_1681_);
                            lean_dec(v_head_1662_);
                            v___x_1682_ = lean_string_utf8_extract(
                                v_str_1679_,
                                v_startInclusive_1680_,
                                v_endExclusive_1681_,
                            );
                            lean_dec(v_endExclusive_1681_);
                            lean_dec(v_startInclusive_1680_);
                            lean_dec_ref(v_str_1679_);
                            v___x_1683_ = l_Lake_Toml_Time_ofString_x3f(v___x_1682_);
                            if lean_obj_tag(v___x_1683_) == 0 {
                                v___x_1684_ = lean_box(0);
                                return v___x_1684_;
                            } else {
                                v_val_1685_ = lean_ctor_get(v___x_1683_, 0);
                                v_isSharedCheck_1693_ = (!lean_is_exclusive(v___x_1683_)) as u8;
                                if v_isSharedCheck_1693_ == 0 {
                                    v___x_1687_ = v___x_1683_;
                                    v_isShared_1688_ = v_isSharedCheck_1693_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_val_1685_);
                                    lean_dec(v___x_1683_);
                                    v___x_1687_ = lean_box(0);
                                    v_isShared_1688_ = v_isSharedCheck_1693_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_tail_1694_ = lean_ctor_get(v_tail_1661_, 1);
                        if lean_obj_tag(v_tail_1694_) == 0 {
                            v_head_1695_ = lean_ctor_get(v___x_1660_, 0);
                            lean_inc(v_head_1695_);
                            lean_dec_ref_known(v___x_1660_, 2);
                            v_head_1696_ = lean_ctor_get(v_tail_1661_, 0);
                            v_isSharedCheck_1872_ = (!lean_is_exclusive(v_tail_1661_)) as u8;
                            if v_isSharedCheck_1872_ == 0 {
                                v_unused_1873_ = lean_ctor_get(v_tail_1661_, 1);
                                lean_dec(v_unused_1873_);
                                v___x_1698_ = v_tail_1661_;
                                v_isShared_1699_ = v_isSharedCheck_1872_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_head_1696_);
                                lean_dec(v_tail_1661_);
                                v___x_1698_ = lean_box(0);
                                v_isShared_1699_ = v_isSharedCheck_1872_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_tail_1661_, 2);
                            lean_dec_ref_known(v___x_1660_, 2);
                            v___x_1874_ = lean_box(0);
                            return v___x_1874_;
                        }
                    }
                } else {
                    lean_dec(v___x_1660_);
                    v___x_1875_ = lean_box(0);
                    return v___x_1875_;
                }
            }
            1 => {
                v___x_1674_ = lean_alloc_ctor(2, 1, (0) as u32);
                lean_ctor_set(v___x_1674_, 0, v_val_1670_);
                if v_isShared_1673_ == 0 {
                    lean_ctor_set(v___x_1672_, 0, v___x_1674_);
                    v___x_1676_ = v___x_1672_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1677_, 0, v___x_1674_);
                    v___x_1676_ = v_reuseFailAlloc_1677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1676_;
            }
            3 => {
                v___x_1689_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_1689_, 0, v_val_1685_);
                if v_isShared_1688_ == 0 {
                    lean_ctor_set(v___x_1687_, 0, v___x_1689_);
                    v___x_1691_ = v___x_1687_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1692_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1689_);
                    v___x_1691_ = v_reuseFailAlloc_1692_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1691_;
            }
            5 => {
                v_str_1700_ = lean_ctor_get(v_head_1695_, 0);
                lean_inc_ref(v_str_1700_);
                v_startInclusive_1701_ = lean_ctor_get(v_head_1695_, 1);
                lean_inc(v_startInclusive_1701_);
                v_endExclusive_1702_ = lean_ctor_get(v_head_1695_, 2);
                lean_inc(v_endExclusive_1702_);
                lean_dec(v_head_1695_);
                v___x_1703_ = lean_string_utf8_extract(
                    v_str_1700_,
                    v_startInclusive_1701_,
                    v_endExclusive_1702_,
                );
                lean_dec(v_endExclusive_1702_);
                lean_dec(v_startInclusive_1701_);
                lean_dec_ref(v_str_1700_);
                v___x_1704_ = l_Lake_Date_ofString_x3f(v___x_1703_);
                if lean_obj_tag(v___x_1704_) == 0 {
                    lean_del_object(v___x_1698_);
                    lean_dec(v_head_1696_);
                    v___x_1705_ = lean_box(0);
                    return v___x_1705_;
                } else {
                    v_val_1706_ = lean_ctor_get(v___x_1704_, 0);
                    lean_inc(v_val_1706_);
                    lean_dec_ref_known(v___x_1704_, 1);
                    v_str_1707_ = lean_ctor_get(v_head_1696_, 0);
                    v_startInclusive_1708_ = lean_ctor_get(v_head_1696_, 1);
                    v_endExclusive_1709_ = lean_ctor_get(v_head_1696_, 2);
                    v___x_1864_ = lean_nat_sub(v_endExclusive_1709_, v_startInclusive_1708_);
                    v___x_1865_ = l_String_Slice_Pos_prev_x3f(v_head_1696_, v___x_1864_);
                    lean_dec(v___x_1864_);
                    if lean_obj_tag(v___x_1865_) == 0 {
                        v___x_1866_ = 65;
                        v___y_1853_ = v___x_1866_;
                        state = 33;
                        continue;
                    } else {
                        v_val_1867_ = lean_ctor_get(v___x_1865_, 0);
                        lean_inc(v_val_1867_);
                        lean_dec_ref_known(v___x_1865_, 1);
                        v___x_1868_ = l_String_Slice_Pos_get_x3f(v_head_1696_, v_val_1867_);
                        lean_dec(v_val_1867_);
                        if lean_obj_tag(v___x_1868_) == 0 {
                            v___x_1869_ = 65;
                            v___y_1853_ = v___x_1869_;
                            state = 33;
                            continue;
                        } else {
                            v_val_1870_ = lean_ctor_get(v___x_1868_, 0);
                            lean_inc(v_val_1870_);
                            lean_dec_ref_known(v___x_1868_, 1);
                            v___x_1871_ = lean_unbox_uint32(v_val_1870_);
                            lean_dec(v_val_1870_);
                            v___y_1853_ = v___x_1871_;
                            state = 33;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v___x_1711_ = lean_string_utf8_extract(
                    v_str_1707_,
                    v_startInclusive_1708_,
                    v_endExclusive_1709_,
                );
                lean_dec(v_endExclusive_1709_);
                lean_dec(v_startInclusive_1708_);
                lean_dec_ref(v_str_1707_);
                v___x_1712_ = l_Lake_Toml_Time_ofString_x3f(v___x_1711_);
                if lean_obj_tag(v___x_1712_) == 0 {
                    lean_dec(v_val_1706_);
                    lean_del_object(v___x_1698_);
                    v___x_1713_ = lean_box(0);
                    return v___x_1713_;
                } else {
                    v_val_1714_ = lean_ctor_get(v___x_1712_, 0);
                    v_isSharedCheck_1724_ = (!lean_is_exclusive(v___x_1712_)) as u8;
                    if v_isSharedCheck_1724_ == 0 {
                        v___x_1716_ = v___x_1712_;
                        v_isShared_1717_ = v_isSharedCheck_1724_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_1714_);
                        lean_dec(v___x_1712_);
                        v___x_1716_ = lean_box(0);
                        v_isShared_1717_ = v_isSharedCheck_1724_;
                        state = 7;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_1699_ == 0 {
                    lean_ctor_set(v___x_1698_, 1, v_val_1714_);
                    lean_ctor_set(v___x_1698_, 0, v_val_1706_);
                    v___x_1719_ = v___x_1698_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1723_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_val_1706_);
                    lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_val_1714_);
                    v___x_1719_ = v_reuseFailAlloc_1723_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1717_ == 0 {
                    lean_ctor_set(v___x_1716_, 0, v___x_1719_);
                    v___x_1721_ = v___x_1716_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
                    v___x_1721_ = v_reuseFailAlloc_1722_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1721_;
            }
            10 => {
                v___x_1727_ =
                    l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__3(
                        v_head_1696_,
                    );
                v___x_1728_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_1696_, v___x_1727_, v___x_1658_);
                v_isSharedCheck_1769_ = (!lean_is_exclusive(v_head_1696_)) as u8;
                if v_isSharedCheck_1769_ == 0 {
                    v_unused_1770_ = lean_ctor_get(v_head_1696_, 2);
                    lean_dec(v_unused_1770_);
                    v_unused_1771_ = lean_ctor_get(v_head_1696_, 1);
                    lean_dec(v_unused_1771_);
                    v_unused_1772_ = lean_ctor_get(v_head_1696_, 0);
                    lean_dec(v_unused_1772_);
                    v___x_1730_ = v_head_1696_;
                    v_isShared_1731_ = v_isSharedCheck_1769_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_head_1696_);
                    v___x_1730_ = lean_box(0);
                    v_isShared_1731_ = v_isSharedCheck_1769_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_1732_ = lean_array_to_list(v___x_1728_);
                if lean_obj_tag(v___x_1732_) == 1 {
                    v_tail_1733_ = lean_ctor_get(v___x_1732_, 1);
                    lean_inc(v_tail_1733_);
                    if lean_obj_tag(v_tail_1733_) == 1 {
                        v_tail_1734_ = lean_ctor_get(v_tail_1733_, 1);
                        if lean_obj_tag(v_tail_1734_) == 0 {
                            lean_dec(v_endExclusive_1709_);
                            lean_dec(v_startInclusive_1708_);
                            lean_dec_ref(v_str_1707_);
                            lean_del_object(v___x_1698_);
                            v_head_1735_ = lean_ctor_get(v___x_1732_, 0);
                            lean_inc(v_head_1735_);
                            lean_dec_ref_known(v___x_1732_, 2);
                            v_head_1736_ = lean_ctor_get(v_tail_1733_, 0);
                            v_isSharedCheck_1767_ = (!lean_is_exclusive(v_tail_1733_)) as u8;
                            if v_isSharedCheck_1767_ == 0 {
                                v_unused_1768_ = lean_ctor_get(v_tail_1733_, 1);
                                lean_dec(v_unused_1768_);
                                v___x_1738_ = v_tail_1733_;
                                v_isShared_1739_ = v_isSharedCheck_1767_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_head_1736_);
                                lean_dec(v_tail_1733_);
                                v___x_1738_ = lean_box(0);
                                v_isShared_1739_ = v_isSharedCheck_1767_;
                                state = 12;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_tail_1733_, 2);
                            lean_dec_ref_known(v___x_1732_, 2);
                            lean_del_object(v___x_1730_);
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_1732_, 2);
                        lean_dec(v_tail_1733_);
                        lean_del_object(v___x_1730_);
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1732_);
                    lean_del_object(v___x_1730_);
                    state = 6;
                    continue;
                }
            }
            12 => {
                v___x_1740_ = l_Lake_Toml_Time_ofString_x3f(v_head_1735_);
                if lean_obj_tag(v___x_1740_) == 0 {
                    lean_del_object(v___x_1738_);
                    lean_dec(v_head_1736_);
                    lean_del_object(v___x_1730_);
                    lean_dec(v_val_1706_);
                    v___x_1741_ = lean_box(0);
                    return v___x_1741_;
                } else {
                    v_val_1742_ = lean_ctor_get(v___x_1740_, 0);
                    v_isSharedCheck_1766_ = (!lean_is_exclusive(v___x_1740_)) as u8;
                    if v_isSharedCheck_1766_ == 0 {
                        v___x_1744_ = v___x_1740_;
                        v_isShared_1745_ = v_isSharedCheck_1766_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_val_1742_);
                        lean_dec(v___x_1740_);
                        v___x_1744_ = lean_box(0);
                        v_isShared_1745_ = v_isSharedCheck_1766_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                v___x_1746_ = l_Lake_Toml_Time_ofString_x3f(v_head_1736_);
                if lean_obj_tag(v___x_1746_) == 0 {
                    lean_del_object(v___x_1744_);
                    lean_dec(v_val_1742_);
                    lean_del_object(v___x_1738_);
                    lean_del_object(v___x_1730_);
                    lean_dec(v_val_1706_);
                    v___x_1747_ = lean_box(0);
                    return v___x_1747_;
                } else {
                    v_val_1748_ = lean_ctor_get(v___x_1746_, 0);
                    v_isSharedCheck_1765_ = (!lean_is_exclusive(v___x_1746_)) as u8;
                    if v_isSharedCheck_1765_ == 0 {
                        v___x_1750_ = v___x_1746_;
                        v_isShared_1751_ = v_isSharedCheck_1765_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_val_1748_);
                        lean_dec(v___x_1746_);
                        v___x_1750_ = lean_box(0);
                        v_isShared_1751_ = v_isSharedCheck_1765_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                v___x_1752_ = lean_box((v___y_1726_) as usize);
                if v_isShared_1739_ == 0 {
                    lean_ctor_set_tag(v___x_1738_, 0);
                    lean_ctor_set(v___x_1738_, 1, v_val_1748_);
                    lean_ctor_set(v___x_1738_, 0, v___x_1752_);
                    v___x_1754_ = v___x_1738_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1752_);
                    lean_ctor_set(v_reuseFailAlloc_1764_, 1, v_val_1748_);
                    v___x_1754_ = v_reuseFailAlloc_1764_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1751_ == 0 {
                    lean_ctor_set(v___x_1750_, 0, v___x_1754_);
                    v___x_1756_ = v___x_1750_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1754_);
                    v___x_1756_ = v_reuseFailAlloc_1763_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1731_ == 0 {
                    lean_ctor_set(v___x_1730_, 2, v___x_1756_);
                    lean_ctor_set(v___x_1730_, 1, v_val_1742_);
                    lean_ctor_set(v___x_1730_, 0, v_val_1706_);
                    v___x_1758_ = v___x_1730_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_val_1706_);
                    lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_val_1742_);
                    lean_ctor_set(v_reuseFailAlloc_1762_, 2, v___x_1756_);
                    v___x_1758_ = v_reuseFailAlloc_1762_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_1745_ == 0 {
                    lean_ctor_set(v___x_1744_, 0, v___x_1758_);
                    v___x_1760_ = v___x_1744_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1758_);
                    v___x_1760_ = v_reuseFailAlloc_1761_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_1760_;
            }
            19 => {
                if v___y_1774_ == 0 {
                    v___x_1775_ = 1;
                    v___x_1776_ = l_String_Slice_splitToSubslice___at___00Lake_Toml_DateTime_ofString_x3f_spec__5(v_head_1696_);
                    v___x_1777_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_1696_, v___x_1776_, v___x_1658_);
                    v___x_1778_ = lean_array_to_list(v___x_1777_);
                    if lean_obj_tag(v___x_1778_) == 1 {
                        v_tail_1779_ = lean_ctor_get(v___x_1778_, 1);
                        lean_inc(v_tail_1779_);
                        if lean_obj_tag(v_tail_1779_) == 1 {
                            v_tail_1780_ = lean_ctor_get(v_tail_1779_, 1);
                            if lean_obj_tag(v_tail_1780_) == 0 {
                                lean_del_object(v___x_1698_);
                                v_isSharedCheck_1818_ = (!lean_is_exclusive(v_head_1696_)) as u8;
                                if v_isSharedCheck_1818_ == 0 {
                                    v_unused_1819_ = lean_ctor_get(v_head_1696_, 2);
                                    lean_dec(v_unused_1819_);
                                    v_unused_1820_ = lean_ctor_get(v_head_1696_, 1);
                                    lean_dec(v_unused_1820_);
                                    v_unused_1821_ = lean_ctor_get(v_head_1696_, 0);
                                    lean_dec(v_unused_1821_);
                                    v___x_1782_ = v_head_1696_;
                                    v_isShared_1783_ = v_isSharedCheck_1818_;
                                    state = 20;
                                    continue;
                                } else {
                                    lean_dec(v_head_1696_);
                                    v___x_1782_ = lean_box(0);
                                    v_isShared_1783_ = v_isSharedCheck_1818_;
                                    state = 20;
                                    continue;
                                }
                            } else {
                                lean_inc(v_endExclusive_1709_);
                                lean_inc(v_startInclusive_1708_);
                                lean_inc_ref(v_str_1707_);
                                lean_dec_ref_known(v_tail_1779_, 2);
                                lean_dec_ref_known(v___x_1778_, 2);
                                v___y_1726_ = v___x_1775_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_inc(v_endExclusive_1709_);
                            lean_inc(v_startInclusive_1708_);
                            lean_inc_ref(v_str_1707_);
                            lean_dec_ref_known(v___x_1778_, 2);
                            lean_dec(v_tail_1779_);
                            v___y_1726_ = v___x_1775_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_inc(v_endExclusive_1709_);
                        lean_inc(v_startInclusive_1708_);
                        lean_inc_ref(v_str_1707_);
                        lean_dec(v___x_1778_);
                        v___y_1726_ = v___x_1775_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_inc(v_startInclusive_1708_);
                    lean_inc_ref(v_str_1707_);
                    lean_del_object(v___x_1698_);
                    v___x_1822_ = lean_unsigned_to_nat(1);
                    v___x_1823_ = lean_nat_sub(v_endExclusive_1709_, v_startInclusive_1708_);
                    v___x_1824_ = l_String_Slice_Pos_prevn(v_head_1696_, v___x_1823_, v___x_1822_);
                    v_isSharedCheck_1844_ = (!lean_is_exclusive(v_head_1696_)) as u8;
                    if v_isSharedCheck_1844_ == 0 {
                        v_unused_1845_ = lean_ctor_get(v_head_1696_, 2);
                        lean_dec(v_unused_1845_);
                        v_unused_1846_ = lean_ctor_get(v_head_1696_, 1);
                        lean_dec(v_unused_1846_);
                        v_unused_1847_ = lean_ctor_get(v_head_1696_, 0);
                        lean_dec(v_unused_1847_);
                        v___x_1826_ = v_head_1696_;
                        v_isShared_1827_ = v_isSharedCheck_1844_;
                        state = 28;
                        continue;
                    } else {
                        lean_dec(v_head_1696_);
                        v___x_1826_ = lean_box(0);
                        v_isShared_1827_ = v_isSharedCheck_1844_;
                        state = 28;
                        continue;
                    }
                }
            }
            20 => {
                v_head_1784_ = lean_ctor_get(v___x_1778_, 0);
                lean_inc(v_head_1784_);
                lean_dec_ref_known(v___x_1778_, 2);
                v_head_1785_ = lean_ctor_get(v_tail_1779_, 0);
                v_isSharedCheck_1816_ = (!lean_is_exclusive(v_tail_1779_)) as u8;
                if v_isSharedCheck_1816_ == 0 {
                    v_unused_1817_ = lean_ctor_get(v_tail_1779_, 1);
                    lean_dec(v_unused_1817_);
                    v___x_1787_ = v_tail_1779_;
                    v_isShared_1788_ = v_isSharedCheck_1816_;
                    state = 21;
                    continue;
                } else {
                    lean_inc(v_head_1785_);
                    lean_dec(v_tail_1779_);
                    v___x_1787_ = lean_box(0);
                    v_isShared_1788_ = v_isSharedCheck_1816_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1789_ = l_Lake_Toml_Time_ofString_x3f(v_head_1784_);
                if lean_obj_tag(v___x_1789_) == 0 {
                    lean_del_object(v___x_1787_);
                    lean_dec(v_head_1785_);
                    lean_del_object(v___x_1782_);
                    lean_dec(v_val_1706_);
                    v___x_1790_ = lean_box(0);
                    return v___x_1790_;
                } else {
                    v_val_1791_ = lean_ctor_get(v___x_1789_, 0);
                    v_isSharedCheck_1815_ = (!lean_is_exclusive(v___x_1789_)) as u8;
                    if v_isSharedCheck_1815_ == 0 {
                        v___x_1793_ = v___x_1789_;
                        v_isShared_1794_ = v_isSharedCheck_1815_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_val_1791_);
                        lean_dec(v___x_1789_);
                        v___x_1793_ = lean_box(0);
                        v_isShared_1794_ = v_isSharedCheck_1815_;
                        state = 22;
                        continue;
                    }
                }
            }
            22 => {
                v___x_1795_ = l_Lake_Toml_Time_ofString_x3f(v_head_1785_);
                if lean_obj_tag(v___x_1795_) == 0 {
                    lean_del_object(v___x_1793_);
                    lean_dec(v_val_1791_);
                    lean_del_object(v___x_1787_);
                    lean_del_object(v___x_1782_);
                    lean_dec(v_val_1706_);
                    v___x_1796_ = lean_box(0);
                    return v___x_1796_;
                } else {
                    v_val_1797_ = lean_ctor_get(v___x_1795_, 0);
                    v_isSharedCheck_1814_ = (!lean_is_exclusive(v___x_1795_)) as u8;
                    if v_isSharedCheck_1814_ == 0 {
                        v___x_1799_ = v___x_1795_;
                        v_isShared_1800_ = v_isSharedCheck_1814_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_val_1797_);
                        lean_dec(v___x_1795_);
                        v___x_1799_ = lean_box(0);
                        v_isShared_1800_ = v_isSharedCheck_1814_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                v___x_1801_ = lean_box((v___y_1774_) as usize);
                if v_isShared_1788_ == 0 {
                    lean_ctor_set_tag(v___x_1787_, 0);
                    lean_ctor_set(v___x_1787_, 1, v_val_1797_);
                    lean_ctor_set(v___x_1787_, 0, v___x_1801_);
                    v___x_1803_ = v___x_1787_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1813_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1813_, 0, v___x_1801_);
                    lean_ctor_set(v_reuseFailAlloc_1813_, 1, v_val_1797_);
                    v___x_1803_ = v_reuseFailAlloc_1813_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_1800_ == 0 {
                    lean_ctor_set(v___x_1799_, 0, v___x_1803_);
                    v___x_1805_ = v___x_1799_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_1812_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1812_, 0, v___x_1803_);
                    v___x_1805_ = v_reuseFailAlloc_1812_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_1783_ == 0 {
                    lean_ctor_set(v___x_1782_, 2, v___x_1805_);
                    lean_ctor_set(v___x_1782_, 1, v_val_1791_);
                    lean_ctor_set(v___x_1782_, 0, v_val_1706_);
                    v___x_1807_ = v___x_1782_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_val_1706_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 1, v_val_1791_);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 2, v___x_1805_);
                    v___x_1807_ = v_reuseFailAlloc_1811_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_1794_ == 0 {
                    lean_ctor_set(v___x_1793_, 0, v___x_1807_);
                    v___x_1809_ = v___x_1793_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1810_, 0, v___x_1807_);
                    v___x_1809_ = v_reuseFailAlloc_1810_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_1809_;
            }
            28 => {
                v___x_1828_ = lean_nat_add(v_startInclusive_1708_, v___x_1824_);
                lean_dec(v___x_1824_);
                v___x_1829_ =
                    lean_string_utf8_extract(v_str_1707_, v_startInclusive_1708_, v___x_1828_);
                lean_dec(v___x_1828_);
                lean_dec(v_startInclusive_1708_);
                lean_dec_ref(v_str_1707_);
                v___x_1830_ = l_Lake_Toml_Time_ofString_x3f(v___x_1829_);
                if lean_obj_tag(v___x_1830_) == 0 {
                    lean_del_object(v___x_1826_);
                    lean_dec(v_val_1706_);
                    v___x_1831_ = lean_box(0);
                    return v___x_1831_;
                } else {
                    v_val_1832_ = lean_ctor_get(v___x_1830_, 0);
                    v_isSharedCheck_1843_ = (!lean_is_exclusive(v___x_1830_)) as u8;
                    if v_isSharedCheck_1843_ == 0 {
                        v___x_1834_ = v___x_1830_;
                        v_isShared_1835_ = v_isSharedCheck_1843_;
                        state = 29;
                        continue;
                    } else {
                        lean_inc(v_val_1832_);
                        lean_dec(v___x_1830_);
                        v___x_1834_ = lean_box(0);
                        v_isShared_1835_ = v_isSharedCheck_1843_;
                        state = 29;
                        continue;
                    }
                }
            }
            29 => {
                v___x_1836_ = lean_box(0);
                if v_isShared_1827_ == 0 {
                    lean_ctor_set(v___x_1826_, 2, v___x_1836_);
                    lean_ctor_set(v___x_1826_, 1, v_val_1832_);
                    lean_ctor_set(v___x_1826_, 0, v_val_1706_);
                    v___x_1838_ = v___x_1826_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1842_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1842_, 0, v_val_1706_);
                    lean_ctor_set(v_reuseFailAlloc_1842_, 1, v_val_1832_);
                    lean_ctor_set(v_reuseFailAlloc_1842_, 2, v___x_1836_);
                    v___x_1838_ = v_reuseFailAlloc_1842_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_1835_ == 0 {
                    lean_ctor_set(v___x_1834_, 0, v___x_1838_);
                    v___x_1840_ = v___x_1834_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1841_, 0, v___x_1838_);
                    v___x_1840_ = v_reuseFailAlloc_1841_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1840_;
            }
            32 => {
                v___x_1850_ = 122;
                v___x_1851_ = lean_uint32_dec_eq(v___y_1849_, v___x_1850_);
                v___y_1774_ = v___x_1851_;
                state = 19;
                continue;
            }
            33 => {
                v___x_1854_ = 90;
                v___x_1855_ = lean_uint32_dec_eq(v___y_1853_, v___x_1854_);
                if v___x_1855_ == 0 {
                    v___x_1856_ = lean_nat_sub(v_endExclusive_1709_, v_startInclusive_1708_);
                    v___x_1857_ = l_String_Slice_Pos_prev_x3f(v_head_1696_, v___x_1856_);
                    lean_dec(v___x_1856_);
                    if lean_obj_tag(v___x_1857_) == 0 {
                        v___x_1858_ = 65;
                        v___y_1849_ = v___x_1858_;
                        state = 32;
                        continue;
                    } else {
                        v_val_1859_ = lean_ctor_get(v___x_1857_, 0);
                        lean_inc(v_val_1859_);
                        lean_dec_ref_known(v___x_1857_, 1);
                        v___x_1860_ = l_String_Slice_Pos_get_x3f(v_head_1696_, v_val_1859_);
                        lean_dec(v_val_1859_);
                        if lean_obj_tag(v___x_1860_) == 0 {
                            v___x_1861_ = 65;
                            v___y_1849_ = v___x_1861_;
                            state = 32;
                            continue;
                        } else {
                            v_val_1862_ = lean_ctor_get(v___x_1860_, 0);
                            lean_inc(v_val_1862_);
                            lean_dec_ref_known(v___x_1860_, 1);
                            v___x_1863_ = lean_unbox_uint32(v_val_1862_);
                            lean_dec(v_val_1862_);
                            v___y_1849_ = v___x_1863_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    v___y_1774_ = v___x_1855_;
                    state = 19;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(
    mut v_dt_1876_: *mut LeanObject,
    mut v___x_1877_: *mut LeanObject,
    mut v___x_1878_: *mut LeanObject,
    mut v_inst_1879_: *mut LeanObject,
    mut v_R_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
    mut v_b_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___x_1883_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___redArg(v_dt_1876_, v___x_1877_, v___x_1878_, v_a_1881_, v_b_1882_);
    return v___x_1883_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1___boxed(
    mut v_dt_1884_: *mut LeanObject,
    mut v___x_1885_: *mut LeanObject,
    mut v___x_1886_: *mut LeanObject,
    mut v_inst_1887_: *mut LeanObject,
    mut v_R_1888_: *mut LeanObject,
    mut v_a_1889_: *mut LeanObject,
    mut v_b_1890_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1891_: *mut LeanObject = core::ptr::null_mut();
    v_res_1891_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__1(v_dt_1884_, v___x_1885_, v___x_1886_, v_inst_1887_, v_R_1888_, v_a_1889_, v_b_1890_);
    lean_dec_ref(v___x_1885_);
    return v_res_1891_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(
    mut v_head_1892_: *mut LeanObject,
    mut v_inst_1893_: *mut LeanObject,
    mut v_R_1894_: *mut LeanObject,
    mut v_a_1895_: *mut LeanObject,
    mut v_b_1896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    v___x_1897_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___redArg(v_head_1892_, v_a_1895_, v_b_1896_);
    return v___x_1897_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4___boxed(
    mut v_head_1898_: *mut LeanObject,
    mut v_inst_1899_: *mut LeanObject,
    mut v_R_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
    mut v_b_1902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1903_: *mut LeanObject = core::ptr::null_mut();
    v_res_1903_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__4(v_head_1898_, v_inst_1899_, v_R_1900_, v_a_1901_, v_b_1902_);
    lean_dec_ref(v_head_1898_);
    return v_res_1903_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(
    mut v_head_1904_: *mut LeanObject,
    mut v_inst_1905_: *mut LeanObject,
    mut v_R_1906_: *mut LeanObject,
    mut v_a_1907_: *mut LeanObject,
    mut v_b_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    v___x_1909_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___redArg(v_head_1904_, v_a_1907_, v_b_1908_);
    return v___x_1909_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6___boxed(
    mut v_head_1910_: *mut LeanObject,
    mut v_inst_1911_: *mut LeanObject,
    mut v_R_1912_: *mut LeanObject,
    mut v_a_1913_: *mut LeanObject,
    mut v_b_1914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1915_: *mut LeanObject = core::ptr::null_mut();
    v_res_1915_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lake_Toml_DateTime_ofString_x3f_spec__6(v_head_1910_, v_inst_1911_, v_R_1912_, v_a_1913_, v_b_1914_);
    lean_dec_ref(v_head_1910_);
    return v_res_1915_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(
    mut v_s_1916_: *mut LeanObject,
    mut v_inst_1917_: *mut LeanObject,
    mut v_R_1918_: *mut LeanObject,
    mut v_a_1919_: *mut LeanObject,
    mut v_b_1920_: u8,
    mut v_c_1921_: *mut LeanObject,
) -> u8 {
    let mut v___x_1922_: u8 = 0;
    v___x_1922_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___redArg(v_s_1916_, v_a_1919_, v_b_1920_);
    return v___x_1922_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2___boxed(
    mut v_s_1923_: *mut LeanObject,
    mut v_inst_1924_: *mut LeanObject,
    mut v_R_1925_: *mut LeanObject,
    mut v_a_1926_: *mut LeanObject,
    mut v_b_1927_: *mut LeanObject,
    mut v_c_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_boxed_1929_: u8 = 0;
    let mut v_res_1930_: u8 = 0;
    let mut v_r_1931_: *mut LeanObject = core::ptr::null_mut();
    v_b_boxed_1929_ = (lean_unbox(v_b_1927_) as u8);
    v_res_1930_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lake_Toml_DateTime_ofString_x3f_spec__2_spec__2(v_s_1923_, v_inst_1924_, v_R_1925_, v_a_1926_, v_b_boxed_1929_, v_c_1928_);
    lean_dec_ref(v_s_1923_);
    v_r_1931_ = lean_box((v_res_1930_) as usize);
    return v_r_1931_;
}
pub unsafe fn l_Lake_Toml_DateTime_toString(mut v_dt_1936_: *mut LeanObject) -> *mut LeanObject {
    match lean_obj_tag(v_dt_1936_) {
        0 => {
            let mut v_offset_x3f_1937_: *mut LeanObject = core::ptr::null_mut();
            v_offset_x3f_1937_ = lean_ctor_get(v_dt_1936_, 2);
            if lean_obj_tag(v_offset_x3f_1937_) == 1 {
                let mut v_val_1938_: *mut LeanObject = core::ptr::null_mut();
                let mut v_fst_1939_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1940_: u8 = 0;
                v_val_1938_ = lean_ctor_get(v_offset_x3f_1937_, 0);
                v_fst_1939_ = lean_ctor_get(v_val_1938_, 0);
                v___x_1940_ = (lean_unbox(v_fst_1939_) as u8);
                if v___x_1940_ == 0 {
                    let mut v_snd_1941_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_date_1942_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_time_1943_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_hour_1944_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_minute_1945_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
                    v_snd_1941_ = lean_ctor_get(v_val_1938_, 1);
                    lean_inc(v_snd_1941_);
                    v_date_1942_ = lean_ctor_get(v_dt_1936_, 0);
                    lean_inc_ref(v_date_1942_);
                    v_time_1943_ = lean_ctor_get(v_dt_1936_, 1);
                    lean_inc_ref(v_time_1943_);
                    lean_dec_ref_known(v_dt_1936_, 3);
                    v_hour_1944_ = lean_ctor_get(v_snd_1941_, 0);
                    lean_inc(v_hour_1944_);
                    v_minute_1945_ = lean_ctor_get(v_snd_1941_, 1);
                    lean_inc(v_minute_1945_);
                    lean_dec(v_snd_1941_);
                    v___x_1946_ = l_Lake_Date_toString(v_date_1942_);
                    v___x_1947_ = l_Lake_Toml_DateTime_toString___closed__0;
                    v___x_1948_ = lean_string_append(v___x_1946_, v___x_1947_);
                    v___x_1949_ = l_Lake_Toml_Time_toString(v_time_1943_);
                    v___x_1950_ = lean_string_append(v___x_1948_, v___x_1949_);
                    lean_dec_ref(v___x_1949_);
                    v___x_1951_ = l_Lake_Toml_DateTime_toString___closed__1;
                    v___x_1952_ = lean_string_append(v___x_1950_, v___x_1951_);
                    v___x_1953_ = lean_unsigned_to_nat(2);
                    v___x_1954_ = l_Lake_zpad(v_hour_1944_, v___x_1953_);
                    v___x_1955_ = lean_string_append(v___x_1952_, v___x_1954_);
                    lean_dec_ref(v___x_1954_);
                    v___x_1956_ = l_Lake_Toml_Time_toString___closed__0;
                    v___x_1957_ = lean_string_append(v___x_1955_, v___x_1956_);
                    v___x_1958_ = l_Lake_zpad(v_minute_1945_, v___x_1953_);
                    v___x_1959_ = lean_string_append(v___x_1957_, v___x_1958_);
                    lean_dec_ref(v___x_1958_);
                    return v___x_1959_;
                } else {
                    let mut v_snd_1960_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_date_1961_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_time_1962_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_hour_1963_: *mut LeanObject = core::ptr::null_mut();
                    let mut v_minute_1964_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1969_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1970_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
                    v_snd_1960_ = lean_ctor_get(v_val_1938_, 1);
                    lean_inc(v_snd_1960_);
                    v_date_1961_ = lean_ctor_get(v_dt_1936_, 0);
                    lean_inc_ref(v_date_1961_);
                    v_time_1962_ = lean_ctor_get(v_dt_1936_, 1);
                    lean_inc_ref(v_time_1962_);
                    lean_dec_ref_known(v_dt_1936_, 3);
                    v_hour_1963_ = lean_ctor_get(v_snd_1960_, 0);
                    lean_inc(v_hour_1963_);
                    v_minute_1964_ = lean_ctor_get(v_snd_1960_, 1);
                    lean_inc(v_minute_1964_);
                    lean_dec(v_snd_1960_);
                    v___x_1965_ = l_Lake_Date_toString(v_date_1961_);
                    v___x_1966_ = l_Lake_Toml_DateTime_toString___closed__0;
                    v___x_1967_ = lean_string_append(v___x_1965_, v___x_1966_);
                    v___x_1968_ = l_Lake_Toml_Time_toString(v_time_1962_);
                    v___x_1969_ = lean_string_append(v___x_1967_, v___x_1968_);
                    lean_dec_ref(v___x_1968_);
                    v___x_1970_ = l_Lake_Toml_DateTime_toString___closed__2;
                    v___x_1971_ = lean_string_append(v___x_1969_, v___x_1970_);
                    v___x_1972_ = lean_unsigned_to_nat(2);
                    v___x_1973_ = l_Lake_zpad(v_hour_1963_, v___x_1972_);
                    v___x_1974_ = lean_string_append(v___x_1971_, v___x_1973_);
                    lean_dec_ref(v___x_1973_);
                    v___x_1975_ = l_Lake_Toml_Time_toString___closed__0;
                    v___x_1976_ = lean_string_append(v___x_1974_, v___x_1975_);
                    v___x_1977_ = l_Lake_zpad(v_minute_1964_, v___x_1972_);
                    v___x_1978_ = lean_string_append(v___x_1976_, v___x_1977_);
                    lean_dec_ref(v___x_1977_);
                    return v___x_1978_;
                }
            } else {
                let mut v_date_1979_: *mut LeanObject = core::ptr::null_mut();
                let mut v_time_1980_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1986_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
                v_date_1979_ = lean_ctor_get(v_dt_1936_, 0);
                lean_inc_ref(v_date_1979_);
                v_time_1980_ = lean_ctor_get(v_dt_1936_, 1);
                lean_inc_ref(v_time_1980_);
                lean_dec_ref_known(v_dt_1936_, 3);
                v___x_1981_ = l_Lake_Date_toString(v_date_1979_);
                v___x_1982_ = l_Lake_Toml_DateTime_toString___closed__0;
                v___x_1983_ = lean_string_append(v___x_1981_, v___x_1982_);
                v___x_1984_ = l_Lake_Toml_Time_toString(v_time_1980_);
                v___x_1985_ = lean_string_append(v___x_1983_, v___x_1984_);
                lean_dec_ref(v___x_1984_);
                v___x_1986_ = l_Lake_Toml_DateTime_toString___closed__3;
                v___x_1987_ = lean_string_append(v___x_1985_, v___x_1986_);
                return v___x_1987_;
            }
        }
        1 => {
            let mut v_date_1988_: *mut LeanObject = core::ptr::null_mut();
            let mut v_time_1989_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
            v_date_1988_ = lean_ctor_get(v_dt_1936_, 0);
            lean_inc_ref(v_date_1988_);
            v_time_1989_ = lean_ctor_get(v_dt_1936_, 1);
            lean_inc_ref(v_time_1989_);
            lean_dec_ref_known(v_dt_1936_, 2);
            v___x_1990_ = l_Lake_Date_toString(v_date_1988_);
            v___x_1991_ = l_Lake_Toml_DateTime_toString___closed__0;
            v___x_1992_ = lean_string_append(v___x_1990_, v___x_1991_);
            v___x_1993_ = l_Lake_Toml_Time_toString(v_time_1989_);
            v___x_1994_ = lean_string_append(v___x_1992_, v___x_1993_);
            lean_dec_ref(v___x_1993_);
            return v___x_1994_;
        }
        2 => {
            let mut v_date_1995_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
            v_date_1995_ = lean_ctor_get(v_dt_1936_, 0);
            lean_inc_ref(v_date_1995_);
            lean_dec_ref_known(v_dt_1936_, 1);
            v___x_1996_ = l_Lake_Date_toString(v_date_1995_);
            return v___x_1996_;
        }
        _ => {
            let mut v_time_1997_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
            v_time_1997_ = lean_ctor_get(v_dt_1936_, 0);
            lean_inc_ref(v_time_1997_);
            lean_dec_ref_known(v_dt_1936_, 1);
            v___x_1998_ = l_Lake_Toml_Time_toString(v_time_1997_);
            return v___x_1998_;
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Toml_Data_DateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_Date(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lake_Toml_instInhabitedDateTime_default = _init_l_Lake_Toml_instInhabitedDateTime_default();
    lean_mark_persistent(l_Lake_Toml_instInhabitedDateTime_default);
    l_Lake_Toml_instInhabitedDateTime = _init_l_Lake_Toml_instInhabitedDateTime();
    lean_mark_persistent(l_Lake_Toml_instInhabitedDateTime);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Toml_Data_DateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Toml_Data_DateTime(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_Date(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Util_String(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Toml_Data_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Toml_Data_DateTime(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Toml_Data_DateTime(builtin);
}
