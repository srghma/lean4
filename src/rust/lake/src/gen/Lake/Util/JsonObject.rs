// Lean compiler output
// Module: Lake.Util.JsonObject
// Imports: Lean.Data.Json
use crate::ffi::{
    lean_nat_add, lean_nat_dec_lt, lean_nat_mul, lean_panic_fn_borrowed, lean_string_append,
    lean_string_compare,
};
use crate::r#gen::Init::Data::Ord::String::l_String_compare___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Json::Basic::l_Lean_Json_getObj_x3f;
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::l_Option_fromJson_x3f___redArg;
use crate::r#gen::Lean::Data::Json::{
    initialize_Lean_Data_Json, runtime_initialize_Lean_Data_Json,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg,
    l_Std_DTreeMap_Internal_Impl_minView_x21___redArg,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_contains___redArg;
pub static mut l_Lake_JsonObject_empty: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_JsonObject_instCoeJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_JsonObject_instCoeJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JsonObject_instCoeJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instCoeJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_JsonObject_instCoeJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instCoeJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_JsonObject_instToJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_JsonObject_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JsonObject_instToJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_JsonObject_instToJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instToJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_JsonObject_instFromJson___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_JsonObject_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JsonObject_instFromJson___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lake_JsonObject_instFromJson: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instFromJson___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_JsonObject_contains___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_String_compare___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JsonObject_contains___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_contains___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__5_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6_value: crate::leanh::LeanStringObject<33> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_JsonObject_get___redArg___closed__0_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 0,
        ],
    };
static mut l_Lake_JsonObject_get___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_get___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_JsonObject_get___redArg___closed__1_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [58, 32, 0],
    };
static mut l_Lake_JsonObject_get___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_get___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_JsonObject_get_x3f___redArg___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lake_JsonObject_get_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_get_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_JsonObject_mk(
    mut v_val_1401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_val_1401_);
    return v_val_1401_;
}
pub unsafe fn l_Lake_JsonObject_mk___boxed(
    mut v_val_1402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lake_JsonObject_mk(v_val_1402_);
    crate::leanh::lean_dec(v_val_1402_);
    return v_res_1403_;
}
pub unsafe fn _init_l_Lake_JsonObject_empty() -> *mut crate::leanh::LeanObject {
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = crate::leanh::lean_box(1);
    return v___x_1404_;
}
pub unsafe fn l_Lake_JsonObject_toJson(
    mut v_obj_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1406_, 0, v_obj_1405_);
    return v___x_1406_;
}
pub unsafe fn l_Lake_JsonObject_instCoeJson___lam__0(
    mut v_kvPairs_1407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1408_, 0, v_kvPairs_1407_);
    return v___x_1408_;
}
pub unsafe fn l_Lake_JsonObject_fromJson_x3f(
    mut v_json_1413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = l_Lean_Json_getObj_x3f(v_json_1413_);
    return v___x_1414_;
}
pub unsafe fn l_Lake_JsonObject_contains(
    mut v_obj_1418_: *mut crate::leanh::LeanObject,
    mut v_prop_1419_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: u8 = 0;
    v___x_1420_ = l_Lake_JsonObject_contains___closed__0;
    v___x_1421_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_1420_, v_prop_1419_, v_obj_1418_);
    return v___x_1421_;
}
pub unsafe fn l_Lake_JsonObject_contains___boxed(
    mut v_obj_1422_: *mut crate::leanh::LeanObject,
    mut v_prop_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1424_: u8 = 0;
    let mut v_r_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Lake_JsonObject_contains(v_obj_1422_, v_prop_1423_);
    v_r_1425_ = crate::leanh::lean_box((v_res_1424_) as usize);
    return v_r_1425_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(
    mut v_msg_1426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1427_ = crate::leanh::lean_box(1);
    v___x_1428_ = lean_panic_fn_borrowed(v___x_1427_, v_msg_1426_);
    return v___x_1428_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2;
    v___x_1433_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_1434_ = crate::leanh::lean_unsigned_to_nat(182);
    v___x_1435_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__1;
    v___x_1436_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0;
    v___x_1437_ = l_mkPanicMessageWithDecl(
        v___x_1436_,
        v___x_1435_,
        v___x_1434_,
        v___x_1433_,
        v___x_1432_,
    );
    return v___x_1437_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2;
    v___x_1439_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_1440_ = crate::leanh::lean_unsigned_to_nat(183);
    v___x_1441_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__1;
    v___x_1442_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0;
    v___x_1443_ = l_mkPanicMessageWithDecl(
        v___x_1442_,
        v___x_1441_,
        v___x_1440_,
        v___x_1439_,
        v___x_1438_,
    );
    return v___x_1443_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6;
    v___x_1447_ = crate::leanh::lean_unsigned_to_nat(35);
    v___x_1448_ = crate::leanh::lean_unsigned_to_nat(276);
    v___x_1449_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__5;
    v___x_1450_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0;
    v___x_1451_ = l_mkPanicMessageWithDecl(
        v___x_1450_,
        v___x_1449_,
        v___x_1448_,
        v___x_1447_,
        v___x_1446_,
    );
    return v___x_1451_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6;
    v___x_1453_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_1454_ = crate::leanh::lean_unsigned_to_nat(277);
    v___x_1455_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__5;
    v___x_1456_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0;
    v___x_1457_ = l_mkPanicMessageWithDecl(
        v___x_1456_,
        v___x_1455_,
        v___x_1454_,
        v___x_1453_,
        v___x_1452_,
    );
    return v___x_1457_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(
    mut v_k_1458_: *mut crate::leanh::LeanObject,
    mut v_v_1459_: *mut crate::leanh::LeanObject,
    mut v_t_1460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v_size_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1500_: u8 = 0;
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut v_unused_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_unused_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1557_: u8 = 0;
    let mut v_unused_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v_size_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_unused_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v_k_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1617_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v_unused_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v_unused_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1666_: u8 = 0;
    let mut v_size_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1704_: u8 = 0;
    let mut v_unused_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1722_: u8 = 0;
    let mut v_unused_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut v_unused_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1752_: u8 = 0;
    let mut v_size_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v_unused_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1770_: u8 = 0;
    let mut v_k_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1787_: u8 = 0;
    let mut v_unused_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_unused_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v_unused_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1460_) == 0 {
                    v_size_1461_ = crate::leanh::lean_ctor_get(v_t_1460_, 0);
                    v_k_1462_ = crate::leanh::lean_ctor_get(v_t_1460_, 1);
                    v_v_1463_ = crate::leanh::lean_ctor_get(v_t_1460_, 2);
                    v_l_1464_ = crate::leanh::lean_ctor_get(v_t_1460_, 3);
                    v_r_1465_ = crate::leanh::lean_ctor_get(v_t_1460_, 4);
                    v_isSharedCheck_1821_ = (!crate::leanh::lean_is_exclusive(v_t_1460_)) as u8;
                    if v_isSharedCheck_1821_ == 0 {
                        v___x_1467_ = v_t_1460_;
                        v_isShared_1468_ = v_isSharedCheck_1821_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1465_);
                        crate::leanh::lean_inc(v_l_1464_);
                        crate::leanh::lean_inc(v_v_1463_);
                        crate::leanh::lean_inc(v_k_1462_);
                        crate::leanh::lean_inc(v_size_1461_);
                        crate::leanh::lean_dec(v_t_1460_);
                        v___x_1467_ = crate::leanh::lean_box(0);
                        v_isShared_1468_ = v_isSharedCheck_1821_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1822_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1823_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1823_, 0, v___x_1822_);
                    crate::leanh::lean_ctor_set(v___x_1823_, 1, v_k_1458_);
                    crate::leanh::lean_ctor_set(v___x_1823_, 2, v_v_1459_);
                    crate::leanh::lean_ctor_set(v___x_1823_, 3, v_t_1460_);
                    crate::leanh::lean_ctor_set(v___x_1823_, 4, v_t_1460_);
                    return v___x_1823_;
                }
            }
            1 => {
                v___x_1469_ = lean_string_compare(v_k_1458_, v_k_1462_);
                match v___x_1469_ {
                    0 => {
                        crate::leanh::lean_dec(v_size_1461_);
                        v___x_1470_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_k_1458_, v_v_1459_, v_l_1464_);
                        if crate::leanh::lean_obj_tag(v_r_1465_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_1470_) == 0 {
                                v_size_1471_ = crate::leanh::lean_ctor_get(v_r_1465_, 0);
                                v_size_1472_ = crate::leanh::lean_ctor_get(v___x_1470_, 0);
                                crate::leanh::lean_inc(v_size_1472_);
                                v_k_1473_ = crate::leanh::lean_ctor_get(v___x_1470_, 1);
                                crate::leanh::lean_inc(v_k_1473_);
                                v_v_1474_ = crate::leanh::lean_ctor_get(v___x_1470_, 2);
                                crate::leanh::lean_inc(v_v_1474_);
                                v_l_1475_ = crate::leanh::lean_ctor_get(v___x_1470_, 3);
                                crate::leanh::lean_inc(v_l_1475_);
                                v_r_1476_ = crate::leanh::lean_ctor_get(v___x_1470_, 4);
                                crate::leanh::lean_inc(v_r_1476_);
                                v___x_1477_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_1478_ = lean_nat_mul(v___x_1477_, v_size_1471_);
                                v___x_1479_ = lean_nat_dec_lt(v___x_1478_, v_size_1472_);
                                crate::leanh::lean_dec(v___x_1478_);
                                if v___x_1479_ == 0 {
                                    crate::leanh::lean_dec(v_r_1476_);
                                    crate::leanh::lean_dec(v_l_1475_);
                                    crate::leanh::lean_dec(v_v_1474_);
                                    crate::leanh::lean_dec(v_k_1473_);
                                    v___x_1480_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1481_ = lean_nat_add(v___x_1480_, v_size_1472_);
                                    crate::leanh::lean_dec(v_size_1472_);
                                    v___x_1482_ = lean_nat_add(v___x_1481_, v_size_1471_);
                                    crate::leanh::lean_dec(v___x_1481_);
                                    if v_isShared_1468_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1467_, 3, v___x_1470_);
                                        crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1482_);
                                        v___x_1484_ = v___x_1467_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1485_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1485_,
                                            0,
                                            v___x_1482_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1485_,
                                            1,
                                            v_k_1462_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1485_,
                                            2,
                                            v_v_1463_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1485_,
                                            3,
                                            v___x_1470_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1485_,
                                            4,
                                            v_r_1465_,
                                        );
                                        v___x_1484_ = v_reuseFailAlloc_1485_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_1557_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1470_)) as u8;
                                    if v_isSharedCheck_1557_ == 0 {
                                        v_unused_1558_ =
                                            crate::leanh::lean_ctor_get(v___x_1470_, 4);
                                        crate::leanh::lean_dec(v_unused_1558_);
                                        v_unused_1559_ =
                                            crate::leanh::lean_ctor_get(v___x_1470_, 3);
                                        crate::leanh::lean_dec(v_unused_1559_);
                                        v_unused_1560_ =
                                            crate::leanh::lean_ctor_get(v___x_1470_, 2);
                                        crate::leanh::lean_dec(v_unused_1560_);
                                        v_unused_1561_ =
                                            crate::leanh::lean_ctor_get(v___x_1470_, 1);
                                        crate::leanh::lean_dec(v_unused_1561_);
                                        v_unused_1562_ =
                                            crate::leanh::lean_ctor_get(v___x_1470_, 0);
                                        crate::leanh::lean_dec(v_unused_1562_);
                                        v___x_1487_ = v___x_1470_;
                                        v_isShared_1488_ = v_isSharedCheck_1557_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1470_);
                                        v___x_1487_ = crate::leanh::lean_box(0);
                                        v_isShared_1488_ = v_isSharedCheck_1557_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1563_ = crate::leanh::lean_ctor_get(v_r_1465_, 0);
                                v___x_1564_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1565_ = lean_nat_add(v___x_1564_, v_size_1563_);
                                if v_isShared_1468_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v___x_1470_);
                                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1565_);
                                    v___x_1567_ = v___x_1467_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1568_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1568_,
                                        0,
                                        v___x_1565_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1568_,
                                        1,
                                        v_k_1462_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1568_,
                                        2,
                                        v_v_1463_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1568_,
                                        3,
                                        v___x_1470_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1568_,
                                        4,
                                        v_r_1465_,
                                    );
                                    v___x_1567_ = v_reuseFailAlloc_1568_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1470_) == 0 {
                                v_l_1569_ = crate::leanh::lean_ctor_get(v___x_1470_, 3);
                                crate::leanh::lean_inc(v_l_1569_);
                                if crate::leanh::lean_obj_tag(v_l_1569_) == 0 {
                                    v_r_1570_ = crate::leanh::lean_ctor_get(v___x_1470_, 4);
                                    crate::leanh::lean_inc(v_r_1570_);
                                    if crate::leanh::lean_obj_tag(v_r_1570_) == 0 {
                                        v_size_1571_ = crate::leanh::lean_ctor_get(v___x_1470_, 0);
                                        v_k_1572_ = crate::leanh::lean_ctor_get(v___x_1470_, 1);
                                        v_v_1573_ = crate::leanh::lean_ctor_get(v___x_1470_, 2);
                                        v_isSharedCheck_1587_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1470_)) as u8;
                                        if v_isSharedCheck_1587_ == 0 {
                                            v_unused_1588_ =
                                                crate::leanh::lean_ctor_get(v___x_1470_, 4);
                                            crate::leanh::lean_dec(v_unused_1588_);
                                            v_unused_1589_ =
                                                crate::leanh::lean_ctor_get(v___x_1470_, 3);
                                            crate::leanh::lean_dec(v_unused_1589_);
                                            v___x_1575_ = v___x_1470_;
                                            v_isShared_1576_ = v_isSharedCheck_1587_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1573_);
                                            crate::leanh::lean_inc(v_k_1572_);
                                            crate::leanh::lean_inc(v_size_1571_);
                                            crate::leanh::lean_dec(v___x_1470_);
                                            v___x_1575_ = crate::leanh::lean_box(0);
                                            v_isShared_1576_ = v_isSharedCheck_1587_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1590_ = crate::leanh::lean_ctor_get(v___x_1470_, 1);
                                        v_v_1591_ = crate::leanh::lean_ctor_get(v___x_1470_, 2);
                                        v_isSharedCheck_1603_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1470_)) as u8;
                                        if v_isSharedCheck_1603_ == 0 {
                                            v_unused_1604_ =
                                                crate::leanh::lean_ctor_get(v___x_1470_, 4);
                                            crate::leanh::lean_dec(v_unused_1604_);
                                            v_unused_1605_ =
                                                crate::leanh::lean_ctor_get(v___x_1470_, 3);
                                            crate::leanh::lean_dec(v_unused_1605_);
                                            v_unused_1606_ =
                                                crate::leanh::lean_ctor_get(v___x_1470_, 0);
                                            crate::leanh::lean_dec(v_unused_1606_);
                                            v___x_1593_ = v___x_1470_;
                                            v_isShared_1594_ = v_isSharedCheck_1603_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1591_);
                                            crate::leanh::lean_inc(v_k_1590_);
                                            crate::leanh::lean_dec(v___x_1470_);
                                            v___x_1593_ = crate::leanh::lean_box(0);
                                            v_isShared_1594_ = v_isSharedCheck_1603_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1607_ = crate::leanh::lean_ctor_get(v___x_1470_, 4);
                                    crate::leanh::lean_inc(v_r_1607_);
                                    if crate::leanh::lean_obj_tag(v_r_1607_) == 0 {
                                        v_k_1608_ = crate::leanh::lean_ctor_get(v___x_1470_, 1);
                                        v_v_1609_ = crate::leanh::lean_ctor_get(v___x_1470_, 2);
                                        v_isSharedCheck_1633_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1470_)) as u8;
                                        if v_isSharedCheck_1633_ == 0 {
                                            v_unused_1634_ =
                                                crate::leanh::lean_ctor_get(v___x_1470_, 4);
                                            crate::leanh::lean_dec(v_unused_1634_);
                                            v_unused_1635_ =
                                                crate::leanh::lean_ctor_get(v___x_1470_, 3);
                                            crate::leanh::lean_dec(v_unused_1635_);
                                            v_unused_1636_ =
                                                crate::leanh::lean_ctor_get(v___x_1470_, 0);
                                            crate::leanh::lean_dec(v_unused_1636_);
                                            v___x_1611_ = v___x_1470_;
                                            v_isShared_1612_ = v_isSharedCheck_1633_;
                                            state = 20;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1609_);
                                            crate::leanh::lean_inc(v_k_1608_);
                                            crate::leanh::lean_dec(v___x_1470_);
                                            v___x_1611_ = crate::leanh::lean_box(0);
                                            v_isShared_1612_ = v_isSharedCheck_1633_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_1637_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1468_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_1467_, 4, v_r_1607_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1467_,
                                                3,
                                                v___x_1470_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_1467_,
                                                0,
                                                v___x_1637_,
                                            );
                                            v___x_1639_ = v___x_1467_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1640_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1640_,
                                                0,
                                                v___x_1637_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1640_,
                                                1,
                                                v_k_1462_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1640_,
                                                2,
                                                v_v_1463_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1640_,
                                                3,
                                                v___x_1470_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1640_,
                                                4,
                                                v_r_1607_,
                                            );
                                            v___x_1639_ = v_reuseFailAlloc_1640_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_1641_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1468_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v___x_1470_);
                                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v___x_1470_);
                                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1641_);
                                    v___x_1643_ = v___x_1467_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1644_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1644_,
                                        0,
                                        v___x_1641_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1644_,
                                        1,
                                        v_k_1462_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1644_,
                                        2,
                                        v_v_1463_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1644_,
                                        3,
                                        v___x_1470_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1644_,
                                        4,
                                        v___x_1470_,
                                    );
                                    v___x_1643_ = v_reuseFailAlloc_1644_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_dec(v_v_1463_);
                        crate::leanh::lean_dec(v_k_1462_);
                        if v_isShared_1468_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1467_, 2, v_v_1459_);
                            crate::leanh::lean_ctor_set(v___x_1467_, 1, v_k_1458_);
                            v___x_1646_ = v___x_1467_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_1647_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_size_1461_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1458_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1459_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_l_1464_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_r_1465_);
                            v___x_1646_ = v_reuseFailAlloc_1647_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        crate::leanh::lean_dec(v_size_1461_);
                        v___x_1648_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_k_1458_, v_v_1459_, v_r_1465_);
                        if crate::leanh::lean_obj_tag(v_l_1464_) == 0 {
                            if crate::leanh::lean_obj_tag(v___x_1648_) == 0 {
                                v_size_1649_ = crate::leanh::lean_ctor_get(v_l_1464_, 0);
                                v_size_1650_ = crate::leanh::lean_ctor_get(v___x_1648_, 0);
                                crate::leanh::lean_inc(v_size_1650_);
                                v_k_1651_ = crate::leanh::lean_ctor_get(v___x_1648_, 1);
                                crate::leanh::lean_inc(v_k_1651_);
                                v_v_1652_ = crate::leanh::lean_ctor_get(v___x_1648_, 2);
                                crate::leanh::lean_inc(v_v_1652_);
                                v_l_1653_ = crate::leanh::lean_ctor_get(v___x_1648_, 3);
                                crate::leanh::lean_inc(v_l_1653_);
                                v_r_1654_ = crate::leanh::lean_ctor_get(v___x_1648_, 4);
                                crate::leanh::lean_inc(v_r_1654_);
                                v___x_1655_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_1656_ = lean_nat_mul(v___x_1655_, v_size_1649_);
                                v___x_1657_ = lean_nat_dec_lt(v___x_1656_, v_size_1650_);
                                crate::leanh::lean_dec(v___x_1656_);
                                if v___x_1657_ == 0 {
                                    crate::leanh::lean_dec(v_r_1654_);
                                    crate::leanh::lean_dec(v_l_1653_);
                                    crate::leanh::lean_dec(v_v_1652_);
                                    crate::leanh::lean_dec(v_k_1651_);
                                    v___x_1658_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1659_ = lean_nat_add(v___x_1658_, v_size_1649_);
                                    v___x_1660_ = lean_nat_add(v___x_1659_, v_size_1650_);
                                    crate::leanh::lean_dec(v_size_1650_);
                                    crate::leanh::lean_dec(v___x_1659_);
                                    if v_isShared_1468_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1467_, 4, v___x_1648_);
                                        crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1660_);
                                        v___x_1662_ = v___x_1467_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1663_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1663_,
                                            0,
                                            v___x_1660_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1663_,
                                            1,
                                            v_k_1462_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1663_,
                                            2,
                                            v_v_1463_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1663_,
                                            3,
                                            v_l_1464_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1663_,
                                            4,
                                            v___x_1648_,
                                        );
                                        v___x_1662_ = v_reuseFailAlloc_1663_;
                                        state = 28;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_1733_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1648_)) as u8;
                                    if v_isSharedCheck_1733_ == 0 {
                                        v_unused_1734_ =
                                            crate::leanh::lean_ctor_get(v___x_1648_, 4);
                                        crate::leanh::lean_dec(v_unused_1734_);
                                        v_unused_1735_ =
                                            crate::leanh::lean_ctor_get(v___x_1648_, 3);
                                        crate::leanh::lean_dec(v_unused_1735_);
                                        v_unused_1736_ =
                                            crate::leanh::lean_ctor_get(v___x_1648_, 2);
                                        crate::leanh::lean_dec(v_unused_1736_);
                                        v_unused_1737_ =
                                            crate::leanh::lean_ctor_get(v___x_1648_, 1);
                                        crate::leanh::lean_dec(v_unused_1737_);
                                        v_unused_1738_ =
                                            crate::leanh::lean_ctor_get(v___x_1648_, 0);
                                        crate::leanh::lean_dec(v_unused_1738_);
                                        v___x_1665_ = v___x_1648_;
                                        v_isShared_1666_ = v_isSharedCheck_1733_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_1648_);
                                        v___x_1665_ = crate::leanh::lean_box(0);
                                        v_isShared_1666_ = v_isSharedCheck_1733_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1739_ = crate::leanh::lean_ctor_get(v_l_1464_, 0);
                                v___x_1740_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1741_ = lean_nat_add(v___x_1740_, v_size_1739_);
                                if v_isShared_1468_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v___x_1648_);
                                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1741_);
                                    v___x_1743_ = v___x_1467_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1744_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1744_,
                                        0,
                                        v___x_1741_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1744_,
                                        1,
                                        v_k_1462_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1744_,
                                        2,
                                        v_v_1463_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1744_,
                                        3,
                                        v_l_1464_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1744_,
                                        4,
                                        v___x_1648_,
                                    );
                                    v___x_1743_ = v_reuseFailAlloc_1744_;
                                    state = 39;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v___x_1648_) == 0 {
                                v_l_1745_ = crate::leanh::lean_ctor_get(v___x_1648_, 3);
                                crate::leanh::lean_inc(v_l_1745_);
                                if crate::leanh::lean_obj_tag(v_l_1745_) == 0 {
                                    v_r_1746_ = crate::leanh::lean_ctor_get(v___x_1648_, 4);
                                    crate::leanh::lean_inc(v_r_1746_);
                                    if crate::leanh::lean_obj_tag(v_r_1746_) == 0 {
                                        v_size_1747_ = crate::leanh::lean_ctor_get(v___x_1648_, 0);
                                        v_k_1748_ = crate::leanh::lean_ctor_get(v___x_1648_, 1);
                                        v_v_1749_ = crate::leanh::lean_ctor_get(v___x_1648_, 2);
                                        v_isSharedCheck_1763_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1648_)) as u8;
                                        if v_isSharedCheck_1763_ == 0 {
                                            v_unused_1764_ =
                                                crate::leanh::lean_ctor_get(v___x_1648_, 4);
                                            crate::leanh::lean_dec(v_unused_1764_);
                                            v_unused_1765_ =
                                                crate::leanh::lean_ctor_get(v___x_1648_, 3);
                                            crate::leanh::lean_dec(v_unused_1765_);
                                            v___x_1751_ = v___x_1648_;
                                            v_isShared_1752_ = v_isSharedCheck_1763_;
                                            state = 40;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1749_);
                                            crate::leanh::lean_inc(v_k_1748_);
                                            crate::leanh::lean_inc(v_size_1747_);
                                            crate::leanh::lean_dec(v___x_1648_);
                                            v___x_1751_ = crate::leanh::lean_box(0);
                                            v_isShared_1752_ = v_isSharedCheck_1763_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_1766_ = crate::leanh::lean_ctor_get(v___x_1648_, 1);
                                        v_v_1767_ = crate::leanh::lean_ctor_get(v___x_1648_, 2);
                                        v_isSharedCheck_1791_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1648_)) as u8;
                                        if v_isSharedCheck_1791_ == 0 {
                                            v_unused_1792_ =
                                                crate::leanh::lean_ctor_get(v___x_1648_, 4);
                                            crate::leanh::lean_dec(v_unused_1792_);
                                            v_unused_1793_ =
                                                crate::leanh::lean_ctor_get(v___x_1648_, 3);
                                            crate::leanh::lean_dec(v_unused_1793_);
                                            v_unused_1794_ =
                                                crate::leanh::lean_ctor_get(v___x_1648_, 0);
                                            crate::leanh::lean_dec(v_unused_1794_);
                                            v___x_1769_ = v___x_1648_;
                                            v_isShared_1770_ = v_isSharedCheck_1791_;
                                            state = 43;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1767_);
                                            crate::leanh::lean_inc(v_k_1766_);
                                            crate::leanh::lean_dec(v___x_1648_);
                                            v___x_1769_ = crate::leanh::lean_box(0);
                                            v_isShared_1770_ = v_isSharedCheck_1791_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1795_ = crate::leanh::lean_ctor_get(v___x_1648_, 4);
                                    crate::leanh::lean_inc(v_r_1795_);
                                    if crate::leanh::lean_obj_tag(v_r_1795_) == 0 {
                                        v_k_1796_ = crate::leanh::lean_ctor_get(v___x_1648_, 1);
                                        v_v_1797_ = crate::leanh::lean_ctor_get(v___x_1648_, 2);
                                        v_isSharedCheck_1809_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1648_)) as u8;
                                        if v_isSharedCheck_1809_ == 0 {
                                            v_unused_1810_ =
                                                crate::leanh::lean_ctor_get(v___x_1648_, 4);
                                            crate::leanh::lean_dec(v_unused_1810_);
                                            v_unused_1811_ =
                                                crate::leanh::lean_ctor_get(v___x_1648_, 3);
                                            crate::leanh::lean_dec(v_unused_1811_);
                                            v_unused_1812_ =
                                                crate::leanh::lean_ctor_get(v___x_1648_, 0);
                                            crate::leanh::lean_dec(v_unused_1812_);
                                            v___x_1799_ = v___x_1648_;
                                            v_isShared_1800_ = v_isSharedCheck_1809_;
                                            state = 48;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1797_);
                                            crate::leanh::lean_inc(v_k_1796_);
                                            crate::leanh::lean_dec(v___x_1648_);
                                            v___x_1799_ = crate::leanh::lean_box(0);
                                            v_isShared_1800_ = v_isSharedCheck_1809_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_1813_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1468_ == 0 {
                                            crate::leanh::lean_ctor_set(
                                                v___x_1467_,
                                                4,
                                                v___x_1648_,
                                            );
                                            crate::leanh::lean_ctor_set(v___x_1467_, 3, v_r_1795_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1467_,
                                                0,
                                                v___x_1813_,
                                            );
                                            v___x_1815_ = v___x_1467_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1816_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1816_,
                                                0,
                                                v___x_1813_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1816_,
                                                1,
                                                v_k_1462_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1816_,
                                                2,
                                                v_v_1463_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1816_,
                                                3,
                                                v_r_1795_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1816_,
                                                4,
                                                v___x_1648_,
                                            );
                                            v___x_1815_ = v_reuseFailAlloc_1816_;
                                            state = 51;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_1817_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1468_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v___x_1648_);
                                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v___x_1648_);
                                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1817_);
                                    v___x_1819_ = v___x_1467_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1820_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1820_,
                                        0,
                                        v___x_1817_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1820_,
                                        1,
                                        v_k_1462_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1820_,
                                        2,
                                        v_v_1463_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1820_,
                                        3,
                                        v___x_1648_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1820_,
                                        4,
                                        v___x_1648_,
                                    );
                                    v___x_1819_ = v_reuseFailAlloc_1820_;
                                    state = 52;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1484_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_l_1475_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_1476_) == 0 {
                        v_size_1489_ = crate::leanh::lean_ctor_get(v_l_1475_, 0);
                        v_size_1490_ = crate::leanh::lean_ctor_get(v_r_1476_, 0);
                        v_k_1491_ = crate::leanh::lean_ctor_get(v_r_1476_, 1);
                        v_v_1492_ = crate::leanh::lean_ctor_get(v_r_1476_, 2);
                        v_l_1493_ = crate::leanh::lean_ctor_get(v_r_1476_, 3);
                        v_r_1494_ = crate::leanh::lean_ctor_get(v_r_1476_, 4);
                        v___x_1495_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1496_ = lean_nat_mul(v___x_1495_, v_size_1489_);
                        v___x_1497_ = lean_nat_dec_lt(v_size_1490_, v___x_1496_);
                        crate::leanh::lean_dec(v___x_1496_);
                        if v___x_1497_ == 0 {
                            crate::leanh::lean_inc(v_r_1494_);
                            crate::leanh::lean_inc(v_l_1493_);
                            crate::leanh::lean_inc(v_v_1492_);
                            crate::leanh::lean_inc(v_k_1491_);
                            v_isSharedCheck_1527_ =
                                (!crate::leanh::lean_is_exclusive(v_r_1476_)) as u8;
                            if v_isSharedCheck_1527_ == 0 {
                                v_unused_1528_ = crate::leanh::lean_ctor_get(v_r_1476_, 4);
                                crate::leanh::lean_dec(v_unused_1528_);
                                v_unused_1529_ = crate::leanh::lean_ctor_get(v_r_1476_, 3);
                                crate::leanh::lean_dec(v_unused_1529_);
                                v_unused_1530_ = crate::leanh::lean_ctor_get(v_r_1476_, 2);
                                crate::leanh::lean_dec(v_unused_1530_);
                                v_unused_1531_ = crate::leanh::lean_ctor_get(v_r_1476_, 1);
                                crate::leanh::lean_dec(v_unused_1531_);
                                v_unused_1532_ = crate::leanh::lean_ctor_get(v_r_1476_, 0);
                                crate::leanh::lean_dec(v_unused_1532_);
                                v___x_1499_ = v_r_1476_;
                                v_isShared_1500_ = v_isSharedCheck_1527_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_r_1476_);
                                v___x_1499_ = crate::leanh::lean_box(0);
                                v_isShared_1500_ = v_isSharedCheck_1527_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1467_);
                            v___x_1533_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1534_ = lean_nat_add(v___x_1533_, v_size_1472_);
                            crate::leanh::lean_dec(v_size_1472_);
                            v___x_1535_ = lean_nat_add(v___x_1534_, v_size_1471_);
                            crate::leanh::lean_dec(v___x_1534_);
                            v___x_1536_ = lean_nat_add(v___x_1533_, v_size_1471_);
                            v___x_1537_ = lean_nat_add(v___x_1536_, v_size_1490_);
                            crate::leanh::lean_dec(v___x_1536_);
                            crate::leanh::lean_inc_ref(v_r_1465_);
                            if v_isShared_1488_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1487_, 4, v_r_1465_);
                                crate::leanh::lean_ctor_set(v___x_1487_, 3, v_r_1476_);
                                crate::leanh::lean_ctor_set(v___x_1487_, 2, v_v_1463_);
                                crate::leanh::lean_ctor_set(v___x_1487_, 1, v_k_1462_);
                                crate::leanh::lean_ctor_set(v___x_1487_, 0, v___x_1537_);
                                v___x_1539_ = v___x_1487_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1552_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1537_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_k_1462_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_v_1463_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_r_1476_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_r_1465_);
                                v___x_1539_ = v_reuseFailAlloc_1552_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_1475_, 5);
                        crate::leanh::lean_del_object(v___x_1487_);
                        crate::leanh::lean_dec(v_v_1474_);
                        crate::leanh::lean_dec(v_k_1473_);
                        crate::leanh::lean_dec(v_size_1472_);
                        crate::leanh::lean_dec_ref_known(v_r_1465_, 5);
                        crate::leanh::lean_del_object(v___x_1467_);
                        crate::leanh::lean_dec(v_v_1463_);
                        crate::leanh::lean_dec(v_k_1462_);
                        v___x_1553_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3);
                        v___x_1554_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1553_);
                        return v___x_1554_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1487_);
                    crate::leanh::lean_dec(v_r_1476_);
                    crate::leanh::lean_dec(v_v_1474_);
                    crate::leanh::lean_dec(v_k_1473_);
                    crate::leanh::lean_dec(v_size_1472_);
                    crate::leanh::lean_dec_ref_known(v_r_1465_, 5);
                    crate::leanh::lean_del_object(v___x_1467_);
                    crate::leanh::lean_dec(v_v_1463_);
                    crate::leanh::lean_dec(v_k_1462_);
                    v___x_1555_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4);
                    v___x_1556_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1555_);
                    return v___x_1556_;
                }
            }
            4 => {
                v___x_1501_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1502_ = lean_nat_add(v___x_1501_, v_size_1472_);
                crate::leanh::lean_dec(v_size_1472_);
                v___x_1503_ = lean_nat_add(v___x_1502_, v_size_1471_);
                crate::leanh::lean_dec(v___x_1502_);
                v___x_1515_ = lean_nat_add(v___x_1501_, v_size_1489_);
                if crate::leanh::lean_obj_tag(v_l_1493_) == 0 {
                    v_size_1525_ = crate::leanh::lean_ctor_get(v_l_1493_, 0);
                    crate::leanh::lean_inc(v_size_1525_);
                    v___y_1517_ = v_size_1525_;
                    state = 8;
                    continue;
                } else {
                    v___x_1526_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1517_ = v___x_1526_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1508_ = lean_nat_add(v___y_1505_, v___y_1507_);
                crate::leanh::lean_dec(v___y_1507_);
                crate::leanh::lean_dec(v___y_1505_);
                if v_isShared_1500_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1499_, 4, v_r_1465_);
                    crate::leanh::lean_ctor_set(v___x_1499_, 3, v_r_1494_);
                    crate::leanh::lean_ctor_set(v___x_1499_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v___x_1499_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v___x_1499_, 0, v___x_1508_);
                    v___x_1510_ = v___x_1499_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_r_1494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1465_);
                    v___x_1510_ = v_reuseFailAlloc_1514_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1487_, 4, v___x_1510_);
                    crate::leanh::lean_ctor_set(v___x_1487_, 3, v___y_1506_);
                    crate::leanh::lean_ctor_set(v___x_1487_, 2, v_v_1492_);
                    crate::leanh::lean_ctor_set(v___x_1487_, 1, v_k_1491_);
                    crate::leanh::lean_ctor_set(v___x_1487_, 0, v___x_1503_);
                    v___x_1512_ = v___x_1487_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1513_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_k_1491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 3, v___y_1506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 4, v___x_1510_);
                    v___x_1512_ = v_reuseFailAlloc_1513_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1512_;
            }
            8 => {
                v___x_1518_ = lean_nat_add(v___x_1515_, v___y_1517_);
                crate::leanh::lean_dec(v___y_1517_);
                crate::leanh::lean_dec(v___x_1515_);
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v_l_1493_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v_l_1475_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 2, v_v_1474_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 1, v_k_1473_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1518_);
                    v___x_1520_ = v___x_1467_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_l_1475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_l_1493_);
                    v___x_1520_ = v_reuseFailAlloc_1524_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1521_ = lean_nat_add(v___x_1501_, v_size_1471_);
                if crate::leanh::lean_obj_tag(v_r_1494_) == 0 {
                    v_size_1522_ = crate::leanh::lean_ctor_get(v_r_1494_, 0);
                    crate::leanh::lean_inc(v_size_1522_);
                    v___y_1505_ = v___x_1521_;
                    v___y_1506_ = v___x_1520_;
                    v___y_1507_ = v_size_1522_;
                    state = 5;
                    continue;
                } else {
                    v___x_1523_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1505_ = v___x_1521_;
                    v___y_1506_ = v___x_1520_;
                    v___y_1507_ = v___x_1523_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1546_ = (!crate::leanh::lean_is_exclusive(v_r_1465_)) as u8;
                if v_isSharedCheck_1546_ == 0 {
                    v_unused_1547_ = crate::leanh::lean_ctor_get(v_r_1465_, 4);
                    crate::leanh::lean_dec(v_unused_1547_);
                    v_unused_1548_ = crate::leanh::lean_ctor_get(v_r_1465_, 3);
                    crate::leanh::lean_dec(v_unused_1548_);
                    v_unused_1549_ = crate::leanh::lean_ctor_get(v_r_1465_, 2);
                    crate::leanh::lean_dec(v_unused_1549_);
                    v_unused_1550_ = crate::leanh::lean_ctor_get(v_r_1465_, 1);
                    crate::leanh::lean_dec(v_unused_1550_);
                    v_unused_1551_ = crate::leanh::lean_ctor_get(v_r_1465_, 0);
                    crate::leanh::lean_dec(v_unused_1551_);
                    v___x_1541_ = v_r_1465_;
                    v_isShared_1542_ = v_isSharedCheck_1546_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1465_);
                    v___x_1541_ = crate::leanh::lean_box(0);
                    v_isShared_1542_ = v_isSharedCheck_1546_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1542_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1541_, 4, v___x_1539_);
                    crate::leanh::lean_ctor_set(v___x_1541_, 3, v_l_1475_);
                    crate::leanh::lean_ctor_set(v___x_1541_, 2, v_v_1474_);
                    crate::leanh::lean_ctor_set(v___x_1541_, 1, v_k_1473_);
                    crate::leanh::lean_ctor_set(v___x_1541_, 0, v___x_1535_);
                    v___x_1544_ = v___x_1541_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1535_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_k_1473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_v_1474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_l_1475_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 4, v___x_1539_);
                    v___x_1544_ = v_reuseFailAlloc_1545_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1544_;
            }
            13 => {
                return v___x_1567_;
            }
            14 => {
                v_size_1577_ = crate::leanh::lean_ctor_get(v_r_1570_, 0);
                v___x_1578_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1579_ = lean_nat_add(v___x_1578_, v_size_1571_);
                crate::leanh::lean_dec(v_size_1571_);
                v___x_1580_ = lean_nat_add(v___x_1578_, v_size_1577_);
                if v_isShared_1576_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1575_, 4, v_r_1465_);
                    crate::leanh::lean_ctor_set(v___x_1575_, 3, v_r_1570_);
                    crate::leanh::lean_ctor_set(v___x_1575_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v___x_1575_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1580_);
                    v___x_1582_ = v___x_1575_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1580_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_r_1570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_r_1465_);
                    v___x_1582_ = v_reuseFailAlloc_1586_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v___x_1582_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v_l_1569_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 2, v_v_1573_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 1, v_k_1572_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1579_);
                    v___x_1584_ = v___x_1467_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1585_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_l_1569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 4, v___x_1582_);
                    v___x_1584_ = v_reuseFailAlloc_1585_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1584_;
            }
            17 => {
                v___x_1595_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1596_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_1594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1593_, 3, v_r_1570_);
                    crate::leanh::lean_ctor_set(v___x_1593_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v___x_1593_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v___x_1593_, 0, v___x_1596_);
                    v___x_1598_ = v___x_1593_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_r_1570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_r_1570_);
                    v___x_1598_ = v_reuseFailAlloc_1602_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v___x_1598_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v_l_1569_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 2, v_v_1591_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 1, v_k_1590_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1595_);
                    v___x_1600_ = v___x_1467_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1590_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_l_1569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 4, v___x_1598_);
                    v___x_1600_ = v_reuseFailAlloc_1601_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1600_;
            }
            20 => {
                v_k_1613_ = crate::leanh::lean_ctor_get(v_r_1607_, 1);
                v_v_1614_ = crate::leanh::lean_ctor_get(v_r_1607_, 2);
                v_isSharedCheck_1629_ = (!crate::leanh::lean_is_exclusive(v_r_1607_)) as u8;
                if v_isSharedCheck_1629_ == 0 {
                    v_unused_1630_ = crate::leanh::lean_ctor_get(v_r_1607_, 4);
                    crate::leanh::lean_dec(v_unused_1630_);
                    v_unused_1631_ = crate::leanh::lean_ctor_get(v_r_1607_, 3);
                    crate::leanh::lean_dec(v_unused_1631_);
                    v_unused_1632_ = crate::leanh::lean_ctor_get(v_r_1607_, 0);
                    crate::leanh::lean_dec(v_unused_1632_);
                    v___x_1616_ = v_r_1607_;
                    v_isShared_1617_ = v_isSharedCheck_1629_;
                    state = 21;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1614_);
                    crate::leanh::lean_inc(v_k_1613_);
                    crate::leanh::lean_dec(v_r_1607_);
                    v___x_1616_ = crate::leanh::lean_box(0);
                    v_isShared_1617_ = v_isSharedCheck_1629_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1618_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1619_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_1617_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1616_, 4, v_l_1569_);
                    crate::leanh::lean_ctor_set(v___x_1616_, 3, v_l_1569_);
                    crate::leanh::lean_ctor_set(v___x_1616_, 2, v_v_1609_);
                    crate::leanh::lean_ctor_set(v___x_1616_, 1, v_k_1608_);
                    crate::leanh::lean_ctor_set(v___x_1616_, 0, v___x_1619_);
                    v___x_1621_ = v___x_1616_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1628_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_k_1608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_v_1609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_l_1569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 4, v_l_1569_);
                    v___x_1621_ = v_reuseFailAlloc_1628_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_1612_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1611_, 4, v_l_1569_);
                    crate::leanh::lean_ctor_set(v___x_1611_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v___x_1611_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v___x_1611_, 0, v___x_1619_);
                    v___x_1623_ = v___x_1611_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_l_1569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 4, v_l_1569_);
                    v___x_1623_ = v_reuseFailAlloc_1627_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v___x_1623_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v___x_1621_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 2, v_v_1614_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 1, v_k_1613_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1618_);
                    v___x_1625_ = v___x_1467_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_k_1613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_v_1614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 3, v___x_1621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 4, v___x_1623_);
                    v___x_1625_ = v_reuseFailAlloc_1626_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1625_;
            }
            25 => {
                return v___x_1639_;
            }
            26 => {
                return v___x_1643_;
            }
            27 => {
                return v___x_1646_;
            }
            28 => {
                return v___x_1662_;
            }
            29 => {
                if crate::leanh::lean_obj_tag(v_l_1653_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_1654_) == 0 {
                        v_size_1667_ = crate::leanh::lean_ctor_get(v_l_1653_, 0);
                        v_k_1668_ = crate::leanh::lean_ctor_get(v_l_1653_, 1);
                        v_v_1669_ = crate::leanh::lean_ctor_get(v_l_1653_, 2);
                        v_l_1670_ = crate::leanh::lean_ctor_get(v_l_1653_, 3);
                        v_r_1671_ = crate::leanh::lean_ctor_get(v_l_1653_, 4);
                        v_size_1672_ = crate::leanh::lean_ctor_get(v_r_1654_, 0);
                        v___x_1673_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1674_ = lean_nat_mul(v___x_1673_, v_size_1672_);
                        v___x_1675_ = lean_nat_dec_lt(v_size_1667_, v___x_1674_);
                        crate::leanh::lean_dec(v___x_1674_);
                        if v___x_1675_ == 0 {
                            crate::leanh::lean_inc(v_r_1671_);
                            crate::leanh::lean_inc(v_l_1670_);
                            crate::leanh::lean_inc(v_v_1669_);
                            crate::leanh::lean_inc(v_k_1668_);
                            v_isSharedCheck_1704_ =
                                (!crate::leanh::lean_is_exclusive(v_l_1653_)) as u8;
                            if v_isSharedCheck_1704_ == 0 {
                                v_unused_1705_ = crate::leanh::lean_ctor_get(v_l_1653_, 4);
                                crate::leanh::lean_dec(v_unused_1705_);
                                v_unused_1706_ = crate::leanh::lean_ctor_get(v_l_1653_, 3);
                                crate::leanh::lean_dec(v_unused_1706_);
                                v_unused_1707_ = crate::leanh::lean_ctor_get(v_l_1653_, 2);
                                crate::leanh::lean_dec(v_unused_1707_);
                                v_unused_1708_ = crate::leanh::lean_ctor_get(v_l_1653_, 1);
                                crate::leanh::lean_dec(v_unused_1708_);
                                v_unused_1709_ = crate::leanh::lean_ctor_get(v_l_1653_, 0);
                                crate::leanh::lean_dec(v_unused_1709_);
                                v___x_1677_ = v_l_1653_;
                                v_isShared_1678_ = v_isSharedCheck_1704_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_1653_);
                                v___x_1677_ = crate::leanh::lean_box(0);
                                v_isShared_1678_ = v_isSharedCheck_1704_;
                                state = 30;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1467_);
                            v___x_1710_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1711_ = lean_nat_add(v___x_1710_, v_size_1649_);
                            v___x_1712_ = lean_nat_add(v___x_1711_, v_size_1650_);
                            crate::leanh::lean_dec(v_size_1650_);
                            v___x_1713_ = lean_nat_add(v___x_1711_, v_size_1667_);
                            crate::leanh::lean_dec(v___x_1711_);
                            crate::leanh::lean_inc_ref(v_l_1464_);
                            if v_isShared_1666_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1665_, 4, v_l_1653_);
                                crate::leanh::lean_ctor_set(v___x_1665_, 3, v_l_1464_);
                                crate::leanh::lean_ctor_set(v___x_1665_, 2, v_v_1463_);
                                crate::leanh::lean_ctor_set(v___x_1665_, 1, v_k_1462_);
                                crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1713_);
                                v___x_1715_ = v___x_1665_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_1728_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1713_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_k_1462_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_v_1463_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 3, v_l_1464_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 4, v_l_1653_);
                                v___x_1715_ = v_reuseFailAlloc_1728_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_1653_, 5);
                        crate::leanh::lean_del_object(v___x_1665_);
                        crate::leanh::lean_dec(v_v_1652_);
                        crate::leanh::lean_dec(v_k_1651_);
                        crate::leanh::lean_dec(v_size_1650_);
                        crate::leanh::lean_dec_ref_known(v_l_1464_, 5);
                        crate::leanh::lean_del_object(v___x_1467_);
                        crate::leanh::lean_dec(v_v_1463_);
                        crate::leanh::lean_dec(v_k_1462_);
                        v___x_1729_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7);
                        v___x_1730_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1729_);
                        return v___x_1730_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1665_);
                    crate::leanh::lean_dec(v_r_1654_);
                    crate::leanh::lean_dec(v_v_1652_);
                    crate::leanh::lean_dec(v_k_1651_);
                    crate::leanh::lean_dec(v_size_1650_);
                    crate::leanh::lean_dec_ref_known(v_l_1464_, 5);
                    crate::leanh::lean_del_object(v___x_1467_);
                    crate::leanh::lean_dec(v_v_1463_);
                    crate::leanh::lean_dec(v_k_1462_);
                    v___x_1731_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8);
                    v___x_1732_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1731_);
                    return v___x_1732_;
                }
            }
            30 => {
                v___x_1679_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1680_ = lean_nat_add(v___x_1679_, v_size_1649_);
                v___x_1681_ = lean_nat_add(v___x_1680_, v_size_1650_);
                crate::leanh::lean_dec(v_size_1650_);
                if crate::leanh::lean_obj_tag(v_l_1670_) == 0 {
                    v_size_1702_ = crate::leanh::lean_ctor_get(v_l_1670_, 0);
                    crate::leanh::lean_inc(v_size_1702_);
                    v___y_1694_ = v_size_1702_;
                    state = 34;
                    continue;
                } else {
                    v___x_1703_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1694_ = v___x_1703_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_1686_ = lean_nat_add(v___y_1683_, v___y_1685_);
                crate::leanh::lean_dec(v___y_1685_);
                crate::leanh::lean_dec(v___y_1683_);
                if v_isShared_1678_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1677_, 4, v_r_1654_);
                    crate::leanh::lean_ctor_set(v___x_1677_, 3, v_r_1671_);
                    crate::leanh::lean_ctor_set(v___x_1677_, 2, v_v_1652_);
                    crate::leanh::lean_ctor_set(v___x_1677_, 1, v_k_1651_);
                    crate::leanh::lean_ctor_set(v___x_1677_, 0, v___x_1686_);
                    v___x_1688_ = v___x_1677_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1692_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_k_1651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 2, v_v_1652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 3, v_r_1671_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 4, v_r_1654_);
                    v___x_1688_ = v_reuseFailAlloc_1692_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1666_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1665_, 4, v___x_1688_);
                    crate::leanh::lean_ctor_set(v___x_1665_, 3, v___y_1684_);
                    crate::leanh::lean_ctor_set(v___x_1665_, 2, v_v_1669_);
                    crate::leanh::lean_ctor_set(v___x_1665_, 1, v_k_1668_);
                    crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1681_);
                    v___x_1690_ = v___x_1665_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1691_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1681_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_k_1668_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_v_1669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 3, v___y_1684_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 4, v___x_1688_);
                    v___x_1690_ = v_reuseFailAlloc_1691_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1690_;
            }
            34 => {
                v___x_1695_ = lean_nat_add(v___x_1680_, v___y_1694_);
                crate::leanh::lean_dec(v___y_1694_);
                crate::leanh::lean_dec(v___x_1680_);
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v_l_1670_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1695_);
                    v___x_1697_ = v___x_1467_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_l_1464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 4, v_l_1670_);
                    v___x_1697_ = v_reuseFailAlloc_1701_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1698_ = lean_nat_add(v___x_1679_, v_size_1672_);
                if crate::leanh::lean_obj_tag(v_r_1671_) == 0 {
                    v_size_1699_ = crate::leanh::lean_ctor_get(v_r_1671_, 0);
                    crate::leanh::lean_inc(v_size_1699_);
                    v___y_1683_ = v___x_1698_;
                    v___y_1684_ = v___x_1697_;
                    v___y_1685_ = v_size_1699_;
                    state = 31;
                    continue;
                } else {
                    v___x_1700_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1683_ = v___x_1698_;
                    v___y_1684_ = v___x_1697_;
                    v___y_1685_ = v___x_1700_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_1722_ = (!crate::leanh::lean_is_exclusive(v_l_1464_)) as u8;
                if v_isSharedCheck_1722_ == 0 {
                    v_unused_1723_ = crate::leanh::lean_ctor_get(v_l_1464_, 4);
                    crate::leanh::lean_dec(v_unused_1723_);
                    v_unused_1724_ = crate::leanh::lean_ctor_get(v_l_1464_, 3);
                    crate::leanh::lean_dec(v_unused_1724_);
                    v_unused_1725_ = crate::leanh::lean_ctor_get(v_l_1464_, 2);
                    crate::leanh::lean_dec(v_unused_1725_);
                    v_unused_1726_ = crate::leanh::lean_ctor_get(v_l_1464_, 1);
                    crate::leanh::lean_dec(v_unused_1726_);
                    v_unused_1727_ = crate::leanh::lean_ctor_get(v_l_1464_, 0);
                    crate::leanh::lean_dec(v_unused_1727_);
                    v___x_1717_ = v_l_1464_;
                    v_isShared_1718_ = v_isSharedCheck_1722_;
                    state = 37;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1464_);
                    v___x_1717_ = crate::leanh::lean_box(0);
                    v_isShared_1718_ = v_isSharedCheck_1722_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1718_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1717_, 4, v_r_1654_);
                    crate::leanh::lean_ctor_set(v___x_1717_, 3, v___x_1715_);
                    crate::leanh::lean_ctor_set(v___x_1717_, 2, v_v_1652_);
                    crate::leanh::lean_ctor_set(v___x_1717_, 1, v_k_1651_);
                    crate::leanh::lean_ctor_set(v___x_1717_, 0, v___x_1712_);
                    v___x_1720_ = v___x_1717_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1721_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_k_1651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_v_1652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 3, v___x_1715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 4, v_r_1654_);
                    v___x_1720_ = v_reuseFailAlloc_1721_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_1720_;
            }
            39 => {
                return v___x_1743_;
            }
            40 => {
                v_size_1753_ = crate::leanh::lean_ctor_get(v_l_1745_, 0);
                v___x_1754_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1755_ = lean_nat_add(v___x_1754_, v_size_1747_);
                crate::leanh::lean_dec(v_size_1747_);
                v___x_1756_ = lean_nat_add(v___x_1754_, v_size_1753_);
                if v_isShared_1752_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1751_, 4, v_l_1745_);
                    crate::leanh::lean_ctor_set(v___x_1751_, 3, v_l_1464_);
                    crate::leanh::lean_ctor_set(v___x_1751_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v___x_1751_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v___x_1751_, 0, v___x_1756_);
                    v___x_1758_ = v___x_1751_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_l_1464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_l_1745_);
                    v___x_1758_ = v_reuseFailAlloc_1762_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v_r_1746_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v___x_1758_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 2, v_v_1749_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 1, v_k_1748_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1755_);
                    v___x_1760_ = v___x_1467_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_1761_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1755_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_k_1748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_v_1749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 3, v___x_1758_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_r_1746_);
                    v___x_1760_ = v_reuseFailAlloc_1761_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_1760_;
            }
            43 => {
                v_k_1771_ = crate::leanh::lean_ctor_get(v_l_1745_, 1);
                v_v_1772_ = crate::leanh::lean_ctor_get(v_l_1745_, 2);
                v_isSharedCheck_1787_ = (!crate::leanh::lean_is_exclusive(v_l_1745_)) as u8;
                if v_isSharedCheck_1787_ == 0 {
                    v_unused_1788_ = crate::leanh::lean_ctor_get(v_l_1745_, 4);
                    crate::leanh::lean_dec(v_unused_1788_);
                    v_unused_1789_ = crate::leanh::lean_ctor_get(v_l_1745_, 3);
                    crate::leanh::lean_dec(v_unused_1789_);
                    v_unused_1790_ = crate::leanh::lean_ctor_get(v_l_1745_, 0);
                    crate::leanh::lean_dec(v_unused_1790_);
                    v___x_1774_ = v_l_1745_;
                    v_isShared_1775_ = v_isSharedCheck_1787_;
                    state = 44;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1772_);
                    crate::leanh::lean_inc(v_k_1771_);
                    crate::leanh::lean_dec(v_l_1745_);
                    v___x_1774_ = crate::leanh::lean_box(0);
                    v_isShared_1775_ = v_isSharedCheck_1787_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_1776_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1777_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_1775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1774_, 4, v_r_1746_);
                    crate::leanh::lean_ctor_set(v___x_1774_, 3, v_r_1746_);
                    crate::leanh::lean_ctor_set(v___x_1774_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v___x_1774_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v___x_1774_, 0, v___x_1777_);
                    v___x_1779_ = v___x_1774_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1786_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_r_1746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 4, v_r_1746_);
                    v___x_1779_ = v_reuseFailAlloc_1786_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1770_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1769_, 3, v_r_1746_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 0, v___x_1777_);
                    v___x_1781_ = v___x_1769_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1777_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_k_1766_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_v_1767_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_r_1746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 4, v_r_1746_);
                    v___x_1781_ = v_reuseFailAlloc_1785_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v___x_1781_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v___x_1779_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 2, v_v_1772_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 1, v_k_1771_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1776_);
                    v___x_1783_ = v___x_1467_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1776_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_k_1771_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_v_1772_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 3, v___x_1779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 4, v___x_1781_);
                    v___x_1783_ = v_reuseFailAlloc_1784_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1783_;
            }
            48 => {
                v___x_1801_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_1802_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_1800_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1799_, 4, v_l_1745_);
                    crate::leanh::lean_ctor_set(v___x_1799_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v___x_1799_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v___x_1799_, 0, v___x_1802_);
                    v___x_1804_ = v___x_1799_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_k_1462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_v_1463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_l_1745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_l_1745_);
                    v___x_1804_ = v_reuseFailAlloc_1808_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_1468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1467_, 4, v_r_1795_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 3, v___x_1804_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 2, v_v_1797_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 1, v_k_1796_);
                    crate::leanh::lean_ctor_set(v___x_1467_, 0, v___x_1801_);
                    v___x_1806_ = v___x_1467_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_k_1796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_v_1797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 3, v___x_1804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_r_1795_);
                    v___x_1806_ = v_reuseFailAlloc_1807_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_1806_;
            }
            51 => {
                return v___x_1815_;
            }
            52 => {
                return v___x_1819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JsonObject_insertJson(
    mut v_obj_1824_: *mut crate::leanh::LeanObject,
    mut v_prop_1825_: *mut crate::leanh::LeanObject,
    mut v_val_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1825_, v_val_1826_, v_obj_1824_);
    return v___x_1827_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0(
    mut v_00_u03b2_1828_: *mut crate::leanh::LeanObject,
    mut v_msg_1829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v_msg_1829_);
    return v___x_1830_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0(
    mut v_00_u03b2_1831_: *mut crate::leanh::LeanObject,
    mut v_k_1832_: *mut crate::leanh::LeanObject,
    mut v_v_1833_: *mut crate::leanh::LeanObject,
    mut v_t_1834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_k_1832_, v_v_1833_, v_t_1834_);
    return v___x_1835_;
}
pub unsafe fn l_Lake_JsonObject_insert___redArg(
    mut v_inst_1836_: *mut crate::leanh::LeanObject,
    mut v_obj_1837_: *mut crate::leanh::LeanObject,
    mut v_prop_1838_: *mut crate::leanh::LeanObject,
    mut v_val_1839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ = crate::leanh::lean_apply_1(v_inst_1836_, v_val_1839_);
    v___x_1841_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1838_, v___x_1840_, v_obj_1837_);
    return v___x_1841_;
}
pub unsafe fn l_Lake_JsonObject_insert(
    mut v_00_u03b1_1842_: *mut crate::leanh::LeanObject,
    mut v_inst_1843_: *mut crate::leanh::LeanObject,
    mut v_obj_1844_: *mut crate::leanh::LeanObject,
    mut v_prop_1845_: *mut crate::leanh::LeanObject,
    mut v_val_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = crate::leanh::lean_apply_1(v_inst_1843_, v_val_1846_);
    v___x_1848_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1845_, v___x_1847_, v_obj_1844_);
    return v___x_1848_;
}
pub unsafe fn l_Lake_JsonObject_insertSome___redArg(
    mut v_inst_1849_: *mut crate::leanh::LeanObject,
    mut v_obj_1850_: *mut crate::leanh::LeanObject,
    mut v_prop_1851_: *mut crate::leanh::LeanObject,
    mut v_val_x3f_1852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_val_x3f_1852_) == 1 {
        let mut v_val_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1853_ = crate::leanh::lean_ctor_get(v_val_x3f_1852_, 0);
        crate::leanh::lean_inc(v_val_1853_);
        crate::leanh::lean_dec_ref_known(v_val_x3f_1852_, 1);
        v___x_1854_ = crate::leanh::lean_apply_1(v_inst_1849_, v_val_1853_);
        v___x_1855_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1851_, v___x_1854_, v_obj_1850_);
        return v___x_1855_;
    } else {
        crate::leanh::lean_dec(v_val_x3f_1852_);
        crate::leanh::lean_dec_ref(v_prop_1851_);
        crate::leanh::lean_dec_ref(v_inst_1849_);
        return v_obj_1850_;
    }
}
pub unsafe fn l_Lake_JsonObject_insertSome(
    mut v_00_u03b1_1856_: *mut crate::leanh::LeanObject,
    mut v_inst_1857_: *mut crate::leanh::LeanObject,
    mut v_obj_1858_: *mut crate::leanh::LeanObject,
    mut v_prop_1859_: *mut crate::leanh::LeanObject,
    mut v_val_x3f_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_val_x3f_1860_) == 1 {
        let mut v_val_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1861_ = crate::leanh::lean_ctor_get(v_val_x3f_1860_, 0);
        crate::leanh::lean_inc(v_val_1861_);
        crate::leanh::lean_dec_ref_known(v_val_x3f_1860_, 1);
        v___x_1862_ = crate::leanh::lean_apply_1(v_inst_1857_, v_val_1861_);
        v___x_1863_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1859_, v___x_1862_, v_obj_1858_);
        return v___x_1863_;
    } else {
        crate::leanh::lean_dec(v_val_x3f_1860_);
        crate::leanh::lean_dec_ref(v_prop_1859_);
        crate::leanh::lean_dec_ref(v_inst_1857_);
        return v_obj_1858_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(
    mut v_k_1864_: *mut crate::leanh::LeanObject,
    mut v_t_1865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1872_: u8 = 0;
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v_size_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut v_unused_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v_unused_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_unused_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v_size_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut v_unused_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v_k_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2013_: u8 = 0;
    let mut v_unused_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_unused_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v_unused_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2060_: u8 = 0;
    let mut v_d_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v_size_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: u8 = 0;
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2089_: u8 = 0;
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2115_: u8 = 0;
    let mut v_unused_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_unused_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v_k_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2174_: u8 = 0;
    let mut v_unused_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut v_unused_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v_k_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_unused_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v_unused_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v_d_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v_size_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2259_: u8 = 0;
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v_unused_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2282_: u8 = 0;
    let mut v_unused_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_unused_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v_k_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut v_unused_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v_k_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut v_unused_2362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2365_: u8 = 0;
    let mut v_unused_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut v_unused_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: u8 = 0;
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2401_: u8 = 0;
    let mut v_size_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut v_unused_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_unused_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut v_unused_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v_size_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut v_unused_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2516_: u8 = 0;
    let mut v_unused_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v_k_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2542_: u8 = 0;
    let mut v_unused_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_unused_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v_unused_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1865_) == 0 {
                    v_k_1866_ = crate::leanh::lean_ctor_get(v_t_1865_, 1);
                    v_v_1867_ = crate::leanh::lean_ctor_get(v_t_1865_, 2);
                    v_l_1868_ = crate::leanh::lean_ctor_get(v_t_1865_, 3);
                    v_r_1869_ = crate::leanh::lean_ctor_get(v_t_1865_, 4);
                    v_isSharedCheck_2558_ = (!crate::leanh::lean_is_exclusive(v_t_1865_)) as u8;
                    if v_isSharedCheck_2558_ == 0 {
                        v_unused_2559_ = crate::leanh::lean_ctor_get(v_t_1865_, 0);
                        crate::leanh::lean_dec(v_unused_2559_);
                        v___x_1871_ = v_t_1865_;
                        v_isShared_1872_ = v_isSharedCheck_2558_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1869_);
                        crate::leanh::lean_inc(v_l_1868_);
                        crate::leanh::lean_inc(v_v_1867_);
                        crate::leanh::lean_inc(v_k_1866_);
                        crate::leanh::lean_dec(v_t_1865_);
                        v___x_1871_ = crate::leanh::lean_box(0);
                        v_isShared_1872_ = v_isSharedCheck_2558_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_1865_;
                }
            }
            1 => {
                v___x_1873_ = lean_string_compare(v_k_1864_, v_k_1866_);
                match v___x_1873_ {
                    0 => {
                        v___x_1874_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(v_k_1864_, v_l_1868_);
                        if crate::leanh::lean_obj_tag(v___x_1874_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_1869_) == 0 {
                                v_size_1875_ = crate::leanh::lean_ctor_get(v___x_1874_, 0);
                                crate::leanh::lean_inc(v_size_1875_);
                                v_size_1876_ = crate::leanh::lean_ctor_get(v_r_1869_, 0);
                                v_k_1877_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                                v_v_1878_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                                v_l_1879_ = crate::leanh::lean_ctor_get(v_r_1869_, 3);
                                crate::leanh::lean_inc(v_l_1879_);
                                v_r_1880_ = crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                v___x_1881_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_1882_ = lean_nat_mul(v___x_1881_, v_size_1875_);
                                v___x_1883_ = lean_nat_dec_lt(v___x_1882_, v_size_1876_);
                                crate::leanh::lean_dec(v___x_1882_);
                                if v___x_1883_ == 0 {
                                    crate::leanh::lean_dec(v_l_1879_);
                                    v___x_1884_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_1885_ = lean_nat_add(v___x_1884_, v_size_1875_);
                                    crate::leanh::lean_dec(v_size_1875_);
                                    v___x_1886_ = lean_nat_add(v___x_1885_, v_size_1876_);
                                    crate::leanh::lean_dec(v___x_1885_);
                                    if v_isShared_1872_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1871_, 3, v___x_1874_);
                                        crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1886_);
                                        v___x_1888_ = v___x_1871_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1889_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            0,
                                            v___x_1886_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            1,
                                            v_k_1866_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            2,
                                            v_v_1867_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            3,
                                            v___x_1874_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            4,
                                            v_r_1869_,
                                        );
                                        v___x_1888_ = v_reuseFailAlloc_1889_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_1880_);
                                    crate::leanh::lean_inc(v_v_1878_);
                                    crate::leanh::lean_inc(v_k_1877_);
                                    crate::leanh::lean_inc(v_size_1876_);
                                    v_isSharedCheck_1959_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                    if v_isSharedCheck_1959_ == 0 {
                                        v_unused_1960_ = crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                        crate::leanh::lean_dec(v_unused_1960_);
                                        v_unused_1961_ = crate::leanh::lean_ctor_get(v_r_1869_, 3);
                                        crate::leanh::lean_dec(v_unused_1961_);
                                        v_unused_1962_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                                        crate::leanh::lean_dec(v_unused_1962_);
                                        v_unused_1963_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                                        crate::leanh::lean_dec(v_unused_1963_);
                                        v_unused_1964_ = crate::leanh::lean_ctor_get(v_r_1869_, 0);
                                        crate::leanh::lean_dec(v_unused_1964_);
                                        v___x_1891_ = v_r_1869_;
                                        v_isShared_1892_ = v_isSharedCheck_1959_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_1869_);
                                        v___x_1891_ = crate::leanh::lean_box(0);
                                        v_isShared_1892_ = v_isSharedCheck_1959_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1965_ = crate::leanh::lean_ctor_get(v___x_1874_, 0);
                                crate::leanh::lean_inc(v_size_1965_);
                                v___x_1966_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_1967_ = lean_nat_add(v___x_1966_, v_size_1965_);
                                crate::leanh::lean_dec(v_size_1965_);
                                if v_isShared_1872_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v___x_1874_);
                                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1967_);
                                    v___x_1969_ = v___x_1871_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1970_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1970_,
                                        0,
                                        v___x_1967_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1970_,
                                        1,
                                        v_k_1866_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1970_,
                                        2,
                                        v_v_1867_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1970_,
                                        3,
                                        v___x_1874_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1970_,
                                        4,
                                        v_r_1869_,
                                    );
                                    v___x_1969_ = v_reuseFailAlloc_1970_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_r_1869_) == 0 {
                                v_l_1971_ = crate::leanh::lean_ctor_get(v_r_1869_, 3);
                                crate::leanh::lean_inc(v_l_1971_);
                                if crate::leanh::lean_obj_tag(v_l_1971_) == 0 {
                                    v_r_1972_ = crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                    crate::leanh::lean_inc(v_r_1972_);
                                    if crate::leanh::lean_obj_tag(v_r_1972_) == 0 {
                                        v_size_1973_ = crate::leanh::lean_ctor_get(v_r_1869_, 0);
                                        v_k_1974_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                                        v_v_1975_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                                        v_isSharedCheck_1989_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                        if v_isSharedCheck_1989_ == 0 {
                                            v_unused_1990_ =
                                                crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                            crate::leanh::lean_dec(v_unused_1990_);
                                            v_unused_1991_ =
                                                crate::leanh::lean_ctor_get(v_r_1869_, 3);
                                            crate::leanh::lean_dec(v_unused_1991_);
                                            v___x_1977_ = v_r_1869_;
                                            v_isShared_1978_ = v_isSharedCheck_1989_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1975_);
                                            crate::leanh::lean_inc(v_k_1974_);
                                            crate::leanh::lean_inc(v_size_1973_);
                                            crate::leanh::lean_dec(v_r_1869_);
                                            v___x_1977_ = crate::leanh::lean_box(0);
                                            v_isShared_1978_ = v_isSharedCheck_1989_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1992_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                                        v_v_1993_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                                        v_isSharedCheck_2017_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                        if v_isSharedCheck_2017_ == 0 {
                                            v_unused_2018_ =
                                                crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                            crate::leanh::lean_dec(v_unused_2018_);
                                            v_unused_2019_ =
                                                crate::leanh::lean_ctor_get(v_r_1869_, 3);
                                            crate::leanh::lean_dec(v_unused_2019_);
                                            v_unused_2020_ =
                                                crate::leanh::lean_ctor_get(v_r_1869_, 0);
                                            crate::leanh::lean_dec(v_unused_2020_);
                                            v___x_1995_ = v_r_1869_;
                                            v_isShared_1996_ = v_isSharedCheck_2017_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_1993_);
                                            crate::leanh::lean_inc(v_k_1992_);
                                            crate::leanh::lean_dec(v_r_1869_);
                                            v___x_1995_ = crate::leanh::lean_box(0);
                                            v_isShared_1996_ = v_isSharedCheck_2017_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2021_ = crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                    crate::leanh::lean_inc(v_r_2021_);
                                    if crate::leanh::lean_obj_tag(v_r_2021_) == 0 {
                                        v_k_2022_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                                        v_v_2023_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                                        v_isSharedCheck_2035_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                        if v_isSharedCheck_2035_ == 0 {
                                            v_unused_2036_ =
                                                crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                            crate::leanh::lean_dec(v_unused_2036_);
                                            v_unused_2037_ =
                                                crate::leanh::lean_ctor_get(v_r_1869_, 3);
                                            crate::leanh::lean_dec(v_unused_2037_);
                                            v_unused_2038_ =
                                                crate::leanh::lean_ctor_get(v_r_1869_, 0);
                                            crate::leanh::lean_dec(v_unused_2038_);
                                            v___x_2025_ = v_r_1869_;
                                            v_isShared_2026_ = v_isSharedCheck_2035_;
                                            state = 22;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2023_);
                                            crate::leanh::lean_inc(v_k_2022_);
                                            crate::leanh::lean_dec(v_r_1869_);
                                            v___x_2025_ = crate::leanh::lean_box(0);
                                            v_isShared_2026_ = v_isSharedCheck_2035_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v___x_2039_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1872_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_1871_, 3, v_r_2021_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1871_,
                                                0,
                                                v___x_2039_,
                                            );
                                            v___x_2041_ = v___x_1871_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2042_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2042_,
                                                0,
                                                v___x_2039_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2042_,
                                                1,
                                                v_k_1866_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2042_,
                                                2,
                                                v_v_1867_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2042_,
                                                3,
                                                v_r_2021_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2042_,
                                                4,
                                                v_r_1869_,
                                            );
                                            v___x_2041_ = v_reuseFailAlloc_2042_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_2043_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1872_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v_r_1869_);
                                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2043_);
                                    v___x_2045_ = v___x_1871_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2046_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2046_,
                                        0,
                                        v___x_2043_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2046_,
                                        1,
                                        v_k_1866_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2046_,
                                        2,
                                        v_v_1867_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2046_,
                                        3,
                                        v_r_1869_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2046_,
                                        4,
                                        v_r_1869_,
                                    );
                                    v___x_2045_ = v_reuseFailAlloc_2046_;
                                    state = 26;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_1871_);
                        crate::leanh::lean_dec(v_v_1867_);
                        crate::leanh::lean_dec(v_k_1866_);
                        if crate::leanh::lean_obj_tag(v_l_1868_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_1869_) == 0 {
                                v_size_2047_ = crate::leanh::lean_ctor_get(v_l_1868_, 0);
                                v_k_2048_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                                v_v_2049_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                                v_l_2050_ = crate::leanh::lean_ctor_get(v_l_1868_, 3);
                                v_r_2051_ = crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                crate::leanh::lean_inc(v_r_2051_);
                                v_size_2052_ = crate::leanh::lean_ctor_get(v_r_1869_, 0);
                                v_k_2053_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                                v_v_2054_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                                v_l_2055_ = crate::leanh::lean_ctor_get(v_r_1869_, 3);
                                crate::leanh::lean_inc(v_l_2055_);
                                v_r_2056_ = crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                v___x_2057_ = lean_nat_dec_lt(v_size_2047_, v_size_2052_);
                                if v___x_2057_ == 0 {
                                    crate::leanh::lean_inc(v_l_2050_);
                                    crate::leanh::lean_inc(v_v_2049_);
                                    crate::leanh::lean_inc(v_k_2048_);
                                    v_isSharedCheck_2209_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                    if v_isSharedCheck_2209_ == 0 {
                                        v_unused_2210_ = crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                        crate::leanh::lean_dec(v_unused_2210_);
                                        v_unused_2211_ = crate::leanh::lean_ctor_get(v_l_1868_, 3);
                                        crate::leanh::lean_dec(v_unused_2211_);
                                        v_unused_2212_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                                        crate::leanh::lean_dec(v_unused_2212_);
                                        v_unused_2213_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                                        crate::leanh::lean_dec(v_unused_2213_);
                                        v_unused_2214_ = crate::leanh::lean_ctor_get(v_l_1868_, 0);
                                        crate::leanh::lean_dec(v_unused_2214_);
                                        v___x_2059_ = v_l_1868_;
                                        v_isShared_2060_ = v_isSharedCheck_2209_;
                                        state = 27;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_1868_);
                                        v___x_2059_ = crate::leanh::lean_box(0);
                                        v_isShared_2060_ = v_isSharedCheck_2209_;
                                        state = 27;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_2056_);
                                    crate::leanh::lean_inc(v_v_2054_);
                                    crate::leanh::lean_inc(v_k_2053_);
                                    v_isSharedCheck_2377_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                    if v_isSharedCheck_2377_ == 0 {
                                        v_unused_2378_ = crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                        crate::leanh::lean_dec(v_unused_2378_);
                                        v_unused_2379_ = crate::leanh::lean_ctor_get(v_r_1869_, 3);
                                        crate::leanh::lean_dec(v_unused_2379_);
                                        v_unused_2380_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                                        crate::leanh::lean_dec(v_unused_2380_);
                                        v_unused_2381_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                                        crate::leanh::lean_dec(v_unused_2381_);
                                        v_unused_2382_ = crate::leanh::lean_ctor_get(v_r_1869_, 0);
                                        crate::leanh::lean_dec(v_unused_2382_);
                                        v___x_2216_ = v_r_1869_;
                                        v_isShared_2217_ = v_isSharedCheck_2377_;
                                        state = 49;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_1869_);
                                        v___x_2216_ = crate::leanh::lean_box(0);
                                        v_isShared_2217_ = v_isSharedCheck_2377_;
                                        state = 49;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_1868_;
                            }
                        } else {
                            return v_r_1869_;
                        }
                    }
                    _ => {
                        v___x_2383_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(v_k_1864_, v_r_1869_);
                        if crate::leanh::lean_obj_tag(v___x_2383_) == 0 {
                            if crate::leanh::lean_obj_tag(v_l_1868_) == 0 {
                                v_size_2384_ = crate::leanh::lean_ctor_get(v___x_2383_, 0);
                                crate::leanh::lean_inc(v_size_2384_);
                                v_size_2385_ = crate::leanh::lean_ctor_get(v_l_1868_, 0);
                                v_k_2386_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                                v_v_2387_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                                v_l_2388_ = crate::leanh::lean_ctor_get(v_l_1868_, 3);
                                v_r_2389_ = crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                crate::leanh::lean_inc(v_r_2389_);
                                v___x_2390_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_2391_ = lean_nat_mul(v___x_2390_, v_size_2384_);
                                v___x_2392_ = lean_nat_dec_lt(v___x_2391_, v_size_2385_);
                                crate::leanh::lean_dec(v___x_2391_);
                                if v___x_2392_ == 0 {
                                    crate::leanh::lean_dec(v_r_2389_);
                                    v___x_2393_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_2394_ = lean_nat_add(v___x_2393_, v_size_2385_);
                                    v___x_2395_ = lean_nat_add(v___x_2394_, v_size_2384_);
                                    crate::leanh::lean_dec(v_size_2384_);
                                    crate::leanh::lean_dec(v___x_2394_);
                                    if v_isShared_1872_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1871_, 4, v___x_2383_);
                                        crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2395_);
                                        v___x_2397_ = v___x_1871_;
                                        state = 72;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2398_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            0,
                                            v___x_2395_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            1,
                                            v_k_1866_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            2,
                                            v_v_1867_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            3,
                                            v_l_1868_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            4,
                                            v___x_2383_,
                                        );
                                        v___x_2397_ = v_reuseFailAlloc_2398_;
                                        state = 72;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_l_2388_);
                                    crate::leanh::lean_inc(v_v_2387_);
                                    crate::leanh::lean_inc(v_k_2386_);
                                    crate::leanh::lean_inc(v_size_2385_);
                                    v_isSharedCheck_2470_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                    if v_isSharedCheck_2470_ == 0 {
                                        v_unused_2471_ = crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                        crate::leanh::lean_dec(v_unused_2471_);
                                        v_unused_2472_ = crate::leanh::lean_ctor_get(v_l_1868_, 3);
                                        crate::leanh::lean_dec(v_unused_2472_);
                                        v_unused_2473_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                                        crate::leanh::lean_dec(v_unused_2473_);
                                        v_unused_2474_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                                        crate::leanh::lean_dec(v_unused_2474_);
                                        v_unused_2475_ = crate::leanh::lean_ctor_get(v_l_1868_, 0);
                                        crate::leanh::lean_dec(v_unused_2475_);
                                        v___x_2400_ = v_l_1868_;
                                        v_isShared_2401_ = v_isSharedCheck_2470_;
                                        state = 73;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_1868_);
                                        v___x_2400_ = crate::leanh::lean_box(0);
                                        v_isShared_2401_ = v_isSharedCheck_2470_;
                                        state = 73;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2476_ = crate::leanh::lean_ctor_get(v___x_2383_, 0);
                                crate::leanh::lean_inc(v_size_2476_);
                                v___x_2477_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_2478_ = lean_nat_add(v___x_2477_, v_size_2476_);
                                crate::leanh::lean_dec(v_size_2476_);
                                if v_isShared_1872_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v___x_2383_);
                                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2478_);
                                    v___x_2480_ = v___x_1871_;
                                    state = 83;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2481_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2481_,
                                        0,
                                        v___x_2478_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2481_,
                                        1,
                                        v_k_1866_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2481_,
                                        2,
                                        v_v_1867_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2481_,
                                        3,
                                        v_l_1868_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2481_,
                                        4,
                                        v___x_2383_,
                                    );
                                    v___x_2480_ = v_reuseFailAlloc_2481_;
                                    state = 83;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_l_1868_) == 0 {
                                v_l_2482_ = crate::leanh::lean_ctor_get(v_l_1868_, 3);
                                if crate::leanh::lean_obj_tag(v_l_2482_) == 0 {
                                    crate::leanh::lean_inc_ref(v_l_2482_);
                                    v_r_2483_ = crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                    crate::leanh::lean_inc(v_r_2483_);
                                    if crate::leanh::lean_obj_tag(v_r_2483_) == 0 {
                                        v_size_2484_ = crate::leanh::lean_ctor_get(v_l_1868_, 0);
                                        v_k_2485_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                                        v_v_2486_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                                        v_isSharedCheck_2500_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                        if v_isSharedCheck_2500_ == 0 {
                                            v_unused_2501_ =
                                                crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                            crate::leanh::lean_dec(v_unused_2501_);
                                            v_unused_2502_ =
                                                crate::leanh::lean_ctor_get(v_l_1868_, 3);
                                            crate::leanh::lean_dec(v_unused_2502_);
                                            v___x_2488_ = v_l_1868_;
                                            v_isShared_2489_ = v_isSharedCheck_2500_;
                                            state = 84;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2486_);
                                            crate::leanh::lean_inc(v_k_2485_);
                                            crate::leanh::lean_inc(v_size_2484_);
                                            crate::leanh::lean_dec(v_l_1868_);
                                            v___x_2488_ = crate::leanh::lean_box(0);
                                            v_isShared_2489_ = v_isSharedCheck_2500_;
                                            state = 84;
                                            continue;
                                        }
                                    } else {
                                        v_k_2503_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                                        v_v_2504_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                                        v_isSharedCheck_2516_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                        if v_isSharedCheck_2516_ == 0 {
                                            v_unused_2517_ =
                                                crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                            crate::leanh::lean_dec(v_unused_2517_);
                                            v_unused_2518_ =
                                                crate::leanh::lean_ctor_get(v_l_1868_, 3);
                                            crate::leanh::lean_dec(v_unused_2518_);
                                            v_unused_2519_ =
                                                crate::leanh::lean_ctor_get(v_l_1868_, 0);
                                            crate::leanh::lean_dec(v_unused_2519_);
                                            v___x_2506_ = v_l_1868_;
                                            v_isShared_2507_ = v_isSharedCheck_2516_;
                                            state = 87;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2504_);
                                            crate::leanh::lean_inc(v_k_2503_);
                                            crate::leanh::lean_dec(v_l_1868_);
                                            v___x_2506_ = crate::leanh::lean_box(0);
                                            v_isShared_2507_ = v_isSharedCheck_2516_;
                                            state = 87;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2520_ = crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                    crate::leanh::lean_inc(v_r_2520_);
                                    if crate::leanh::lean_obj_tag(v_r_2520_) == 0 {
                                        crate::leanh::lean_inc(v_l_2482_);
                                        v_k_2521_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                                        v_v_2522_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                                        v_isSharedCheck_2546_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                        if v_isSharedCheck_2546_ == 0 {
                                            v_unused_2547_ =
                                                crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                            crate::leanh::lean_dec(v_unused_2547_);
                                            v_unused_2548_ =
                                                crate::leanh::lean_ctor_get(v_l_1868_, 3);
                                            crate::leanh::lean_dec(v_unused_2548_);
                                            v_unused_2549_ =
                                                crate::leanh::lean_ctor_get(v_l_1868_, 0);
                                            crate::leanh::lean_dec(v_unused_2549_);
                                            v___x_2524_ = v_l_1868_;
                                            v_isShared_2525_ = v_isSharedCheck_2546_;
                                            state = 90;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_2522_);
                                            crate::leanh::lean_inc(v_k_2521_);
                                            crate::leanh::lean_dec(v_l_1868_);
                                            v___x_2524_ = crate::leanh::lean_box(0);
                                            v_isShared_2525_ = v_isSharedCheck_2546_;
                                            state = 90;
                                            continue;
                                        }
                                    } else {
                                        v___x_2550_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1872_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_1871_, 4, v_r_2520_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_1871_,
                                                0,
                                                v___x_2550_,
                                            );
                                            v___x_2552_ = v___x_1871_;
                                            state = 95;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2553_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2553_,
                                                0,
                                                v___x_2550_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2553_,
                                                1,
                                                v_k_1866_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2553_,
                                                2,
                                                v_v_1867_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2553_,
                                                3,
                                                v_l_1868_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2553_,
                                                4,
                                                v_r_2520_,
                                            );
                                            v___x_2552_ = v_reuseFailAlloc_2553_;
                                            state = 95;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___x_2554_ = crate::leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1872_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v_l_1868_);
                                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2554_);
                                    v___x_2556_ = v___x_1871_;
                                    state = 96;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2557_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2557_,
                                        0,
                                        v___x_2554_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2557_,
                                        1,
                                        v_k_1866_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2557_,
                                        2,
                                        v_v_1867_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2557_,
                                        3,
                                        v_l_1868_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2557_,
                                        4,
                                        v_l_1868_,
                                    );
                                    v___x_2556_ = v_reuseFailAlloc_2557_;
                                    state = 96;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1888_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_l_1879_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_1880_) == 0 {
                        v_size_1893_ = crate::leanh::lean_ctor_get(v_l_1879_, 0);
                        v_k_1894_ = crate::leanh::lean_ctor_get(v_l_1879_, 1);
                        v_v_1895_ = crate::leanh::lean_ctor_get(v_l_1879_, 2);
                        v_l_1896_ = crate::leanh::lean_ctor_get(v_l_1879_, 3);
                        v_r_1897_ = crate::leanh::lean_ctor_get(v_l_1879_, 4);
                        v_size_1898_ = crate::leanh::lean_ctor_get(v_r_1880_, 0);
                        v___x_1899_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_1900_ = lean_nat_mul(v___x_1899_, v_size_1898_);
                        v___x_1901_ = lean_nat_dec_lt(v_size_1893_, v___x_1900_);
                        crate::leanh::lean_dec(v___x_1900_);
                        if v___x_1901_ == 0 {
                            crate::leanh::lean_inc(v_r_1897_);
                            crate::leanh::lean_inc(v_l_1896_);
                            crate::leanh::lean_inc(v_v_1895_);
                            crate::leanh::lean_inc(v_k_1894_);
                            v_isSharedCheck_1930_ =
                                (!crate::leanh::lean_is_exclusive(v_l_1879_)) as u8;
                            if v_isSharedCheck_1930_ == 0 {
                                v_unused_1931_ = crate::leanh::lean_ctor_get(v_l_1879_, 4);
                                crate::leanh::lean_dec(v_unused_1931_);
                                v_unused_1932_ = crate::leanh::lean_ctor_get(v_l_1879_, 3);
                                crate::leanh::lean_dec(v_unused_1932_);
                                v_unused_1933_ = crate::leanh::lean_ctor_get(v_l_1879_, 2);
                                crate::leanh::lean_dec(v_unused_1933_);
                                v_unused_1934_ = crate::leanh::lean_ctor_get(v_l_1879_, 1);
                                crate::leanh::lean_dec(v_unused_1934_);
                                v_unused_1935_ = crate::leanh::lean_ctor_get(v_l_1879_, 0);
                                crate::leanh::lean_dec(v_unused_1935_);
                                v___x_1903_ = v_l_1879_;
                                v_isShared_1904_ = v_isSharedCheck_1930_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_1879_);
                                v___x_1903_ = crate::leanh::lean_box(0);
                                v_isShared_1904_ = v_isSharedCheck_1930_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1871_);
                            v___x_1936_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1937_ = lean_nat_add(v___x_1936_, v_size_1875_);
                            crate::leanh::lean_dec(v_size_1875_);
                            v___x_1938_ = lean_nat_add(v___x_1937_, v_size_1876_);
                            crate::leanh::lean_dec(v_size_1876_);
                            v___x_1939_ = lean_nat_add(v___x_1937_, v_size_1893_);
                            crate::leanh::lean_dec(v___x_1937_);
                            crate::leanh::lean_inc_ref(v___x_1874_);
                            if v_isShared_1892_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1891_, 4, v_l_1879_);
                                crate::leanh::lean_ctor_set(v___x_1891_, 3, v___x_1874_);
                                crate::leanh::lean_ctor_set(v___x_1891_, 2, v_v_1867_);
                                crate::leanh::lean_ctor_set(v___x_1891_, 1, v_k_1866_);
                                crate::leanh::lean_ctor_set(v___x_1891_, 0, v___x_1939_);
                                v___x_1941_ = v___x_1891_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1954_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1939_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_k_1866_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_v_1867_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 3, v___x_1874_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_l_1879_);
                                v___x_1941_ = v_reuseFailAlloc_1954_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_1879_, 5);
                        crate::leanh::lean_del_object(v___x_1891_);
                        crate::leanh::lean_dec(v_v_1878_);
                        crate::leanh::lean_dec(v_k_1877_);
                        crate::leanh::lean_dec(v_size_1876_);
                        crate::leanh::lean_dec(v_size_1875_);
                        crate::leanh::lean_dec_ref_known(v___x_1874_, 5);
                        crate::leanh::lean_del_object(v___x_1871_);
                        crate::leanh::lean_dec(v_v_1867_);
                        crate::leanh::lean_dec(v_k_1866_);
                        v___x_1955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7);
                        v___x_1956_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1955_);
                        return v___x_1956_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1891_);
                    crate::leanh::lean_dec(v_r_1880_);
                    crate::leanh::lean_dec(v_v_1878_);
                    crate::leanh::lean_dec(v_k_1877_);
                    crate::leanh::lean_dec(v_size_1876_);
                    crate::leanh::lean_dec(v_size_1875_);
                    crate::leanh::lean_dec_ref_known(v___x_1874_, 5);
                    crate::leanh::lean_del_object(v___x_1871_);
                    crate::leanh::lean_dec(v_v_1867_);
                    crate::leanh::lean_dec(v_k_1866_);
                    v___x_1957_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8);
                    v___x_1958_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1957_);
                    return v___x_1958_;
                }
            }
            4 => {
                v___x_1905_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1906_ = lean_nat_add(v___x_1905_, v_size_1875_);
                crate::leanh::lean_dec(v_size_1875_);
                v___x_1907_ = lean_nat_add(v___x_1906_, v_size_1876_);
                crate::leanh::lean_dec(v_size_1876_);
                if crate::leanh::lean_obj_tag(v_l_1896_) == 0 {
                    v_size_1928_ = crate::leanh::lean_ctor_get(v_l_1896_, 0);
                    crate::leanh::lean_inc(v_size_1928_);
                    v___y_1920_ = v_size_1928_;
                    state = 8;
                    continue;
                } else {
                    v___x_1929_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1920_ = v___x_1929_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1912_ = lean_nat_add(v___y_1910_, v___y_1911_);
                crate::leanh::lean_dec(v___y_1911_);
                crate::leanh::lean_dec(v___y_1910_);
                if v_isShared_1904_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1903_, 4, v_r_1880_);
                    crate::leanh::lean_ctor_set(v___x_1903_, 3, v_r_1897_);
                    crate::leanh::lean_ctor_set(v___x_1903_, 2, v_v_1878_);
                    crate::leanh::lean_ctor_set(v___x_1903_, 1, v_k_1877_);
                    crate::leanh::lean_ctor_set(v___x_1903_, 0, v___x_1912_);
                    v___x_1914_ = v___x_1903_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1912_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_k_1877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_v_1878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_r_1897_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_r_1880_);
                    v___x_1914_ = v_reuseFailAlloc_1918_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1892_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1891_, 4, v___x_1914_);
                    crate::leanh::lean_ctor_set(v___x_1891_, 3, v___y_1909_);
                    crate::leanh::lean_ctor_set(v___x_1891_, 2, v_v_1895_);
                    crate::leanh::lean_ctor_set(v___x_1891_, 1, v_k_1894_);
                    crate::leanh::lean_ctor_set(v___x_1891_, 0, v___x_1907_);
                    v___x_1916_ = v___x_1891_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_k_1894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_v_1895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 3, v___y_1909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 4, v___x_1914_);
                    v___x_1916_ = v_reuseFailAlloc_1917_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1916_;
            }
            8 => {
                v___x_1921_ = lean_nat_add(v___x_1906_, v___y_1920_);
                crate::leanh::lean_dec(v___y_1920_);
                crate::leanh::lean_dec(v___x_1906_);
                if v_isShared_1872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v_l_1896_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v___x_1874_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1921_);
                    v___x_1923_ = v___x_1871_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1927_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1921_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 3, v___x_1874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_l_1896_);
                    v___x_1923_ = v_reuseFailAlloc_1927_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1924_ = lean_nat_add(v___x_1905_, v_size_1898_);
                if crate::leanh::lean_obj_tag(v_r_1897_) == 0 {
                    v_size_1925_ = crate::leanh::lean_ctor_get(v_r_1897_, 0);
                    crate::leanh::lean_inc(v_size_1925_);
                    v___y_1909_ = v___x_1923_;
                    v___y_1910_ = v___x_1924_;
                    v___y_1911_ = v_size_1925_;
                    state = 5;
                    continue;
                } else {
                    v___x_1926_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1909_ = v___x_1923_;
                    v___y_1910_ = v___x_1924_;
                    v___y_1911_ = v___x_1926_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1948_ = (!crate::leanh::lean_is_exclusive(v___x_1874_)) as u8;
                if v_isSharedCheck_1948_ == 0 {
                    v_unused_1949_ = crate::leanh::lean_ctor_get(v___x_1874_, 4);
                    crate::leanh::lean_dec(v_unused_1949_);
                    v_unused_1950_ = crate::leanh::lean_ctor_get(v___x_1874_, 3);
                    crate::leanh::lean_dec(v_unused_1950_);
                    v_unused_1951_ = crate::leanh::lean_ctor_get(v___x_1874_, 2);
                    crate::leanh::lean_dec(v_unused_1951_);
                    v_unused_1952_ = crate::leanh::lean_ctor_get(v___x_1874_, 1);
                    crate::leanh::lean_dec(v_unused_1952_);
                    v_unused_1953_ = crate::leanh::lean_ctor_get(v___x_1874_, 0);
                    crate::leanh::lean_dec(v_unused_1953_);
                    v___x_1943_ = v___x_1874_;
                    v_isShared_1944_ = v_isSharedCheck_1948_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1874_);
                    v___x_1943_ = crate::leanh::lean_box(0);
                    v_isShared_1944_ = v_isSharedCheck_1948_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1944_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1943_, 4, v_r_1880_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 3, v___x_1941_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 2, v_v_1878_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 1, v_k_1877_);
                    crate::leanh::lean_ctor_set(v___x_1943_, 0, v___x_1938_);
                    v___x_1946_ = v___x_1943_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 3, v___x_1941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_r_1880_);
                    v___x_1946_ = v_reuseFailAlloc_1947_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1946_;
            }
            13 => {
                return v___x_1969_;
            }
            14 => {
                v_size_1979_ = crate::leanh::lean_ctor_get(v_l_1971_, 0);
                v___x_1980_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1981_ = lean_nat_add(v___x_1980_, v_size_1973_);
                crate::leanh::lean_dec(v_size_1973_);
                v___x_1982_ = lean_nat_add(v___x_1980_, v_size_1979_);
                if v_isShared_1978_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1977_, 4, v_l_1971_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 3, v___x_1874_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v___x_1977_, 0, v___x_1982_);
                    v___x_1984_ = v___x_1977_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1982_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 3, v___x_1874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_l_1971_);
                    v___x_1984_ = v_reuseFailAlloc_1988_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v_r_1972_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v___x_1984_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 2, v_v_1975_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 1, v_k_1974_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_1981_);
                    v___x_1986_ = v___x_1871_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1987_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1981_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_k_1974_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_v_1975_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 3, v___x_1984_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_r_1972_);
                    v___x_1986_ = v_reuseFailAlloc_1987_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1986_;
            }
            17 => {
                v_k_1997_ = crate::leanh::lean_ctor_get(v_l_1971_, 1);
                v_v_1998_ = crate::leanh::lean_ctor_get(v_l_1971_, 2);
                v_isSharedCheck_2013_ = (!crate::leanh::lean_is_exclusive(v_l_1971_)) as u8;
                if v_isSharedCheck_2013_ == 0 {
                    v_unused_2014_ = crate::leanh::lean_ctor_get(v_l_1971_, 4);
                    crate::leanh::lean_dec(v_unused_2014_);
                    v_unused_2015_ = crate::leanh::lean_ctor_get(v_l_1971_, 3);
                    crate::leanh::lean_dec(v_unused_2015_);
                    v_unused_2016_ = crate::leanh::lean_ctor_get(v_l_1971_, 0);
                    crate::leanh::lean_dec(v_unused_2016_);
                    v___x_2000_ = v_l_1971_;
                    v_isShared_2001_ = v_isSharedCheck_2013_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1998_);
                    crate::leanh::lean_inc(v_k_1997_);
                    crate::leanh::lean_dec(v_l_1971_);
                    v___x_2000_ = crate::leanh::lean_box(0);
                    v_isShared_2001_ = v_isSharedCheck_2013_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2002_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2003_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2001_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2000_, 4, v_r_1972_);
                    crate::leanh::lean_ctor_set(v___x_2000_, 3, v_r_1972_);
                    crate::leanh::lean_ctor_set(v___x_2000_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v___x_2000_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v___x_2000_, 0, v___x_2003_);
                    v___x_2005_ = v___x_2000_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2012_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_r_1972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_r_1972_);
                    v___x_2005_ = v_reuseFailAlloc_2012_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1996_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1995_, 3, v_r_1972_);
                    crate::leanh::lean_ctor_set(v___x_1995_, 0, v___x_2003_);
                    v___x_2007_ = v___x_1995_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2011_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_k_1992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_v_1993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 3, v_r_1972_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 4, v_r_1972_);
                    v___x_2007_ = v_reuseFailAlloc_2011_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v___x_2007_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v___x_2005_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 2, v_v_1998_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 1, v_k_1997_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2002_);
                    v___x_2009_ = v___x_1871_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_k_1997_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_v_1998_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 3, v___x_2005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 4, v___x_2007_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2009_;
            }
            22 => {
                v___x_2027_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2028_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2025_, 4, v_l_1971_);
                    crate::leanh::lean_ctor_set(v___x_2025_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v___x_2025_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v___x_2025_, 0, v___x_2028_);
                    v___x_2030_ = v___x_2025_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2028_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_l_1971_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_l_1971_);
                    v___x_2030_ = v_reuseFailAlloc_2034_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v_r_2021_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v___x_2030_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 2, v_v_2023_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 1, v_k_2022_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2027_);
                    v___x_2032_ = v___x_1871_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2027_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_k_2022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_v_2023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 3, v___x_2030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 4, v_r_2021_);
                    v___x_2032_ = v_reuseFailAlloc_2033_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_2032_;
            }
            25 => {
                return v___x_2041_;
            }
            26 => {
                return v___x_2045_;
            }
            27 => {
                v_d_2061_ = l_Std_DTreeMap_Internal_Impl_maxView_x21___redArg(
                    v_k_2048_, v_v_2049_, v_l_2050_, v_r_2051_,
                );
                v_tree_2062_ = crate::leanh::lean_ctor_get(v_d_2061_, 2);
                crate::leanh::lean_inc(v_tree_2062_);
                if crate::leanh::lean_obj_tag(v_tree_2062_) == 0 {
                    v_k_2063_ = crate::leanh::lean_ctor_get(v_d_2061_, 0);
                    crate::leanh::lean_inc(v_k_2063_);
                    v_v_2064_ = crate::leanh::lean_ctor_get(v_d_2061_, 1);
                    crate::leanh::lean_inc(v_v_2064_);
                    crate::leanh::lean_dec_ref(v_d_2061_);
                    v_size_2065_ = crate::leanh::lean_ctor_get(v_tree_2062_, 0);
                    v___x_2066_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2067_ = lean_nat_mul(v___x_2066_, v_size_2065_);
                    v___x_2068_ = lean_nat_dec_lt(v___x_2067_, v_size_2052_);
                    crate::leanh::lean_dec(v___x_2067_);
                    if v___x_2068_ == 0 {
                        crate::leanh::lean_dec(v_l_2055_);
                        v___x_2069_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2070_ = lean_nat_add(v___x_2069_, v_size_2065_);
                        v___x_2071_ = lean_nat_add(v___x_2070_, v_size_2052_);
                        crate::leanh::lean_dec(v___x_2070_);
                        if v_isShared_2060_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2059_, 4, v_r_1869_);
                            crate::leanh::lean_ctor_set(v___x_2059_, 3, v_tree_2062_);
                            crate::leanh::lean_ctor_set(v___x_2059_, 2, v_v_2064_);
                            crate::leanh::lean_ctor_set(v___x_2059_, 1, v_k_2063_);
                            crate::leanh::lean_ctor_set(v___x_2059_, 0, v___x_2071_);
                            v___x_2073_ = v___x_2059_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_2074_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_2063_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_2064_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_tree_2062_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_r_1869_);
                            v___x_2073_ = v_reuseFailAlloc_2074_;
                            state = 28;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_r_2056_);
                        crate::leanh::lean_inc(v_v_2054_);
                        crate::leanh::lean_inc(v_k_2053_);
                        crate::leanh::lean_inc(v_size_2052_);
                        v_isSharedCheck_2135_ = (!crate::leanh::lean_is_exclusive(v_r_1869_)) as u8;
                        if v_isSharedCheck_2135_ == 0 {
                            v_unused_2136_ = crate::leanh::lean_ctor_get(v_r_1869_, 4);
                            crate::leanh::lean_dec(v_unused_2136_);
                            v_unused_2137_ = crate::leanh::lean_ctor_get(v_r_1869_, 3);
                            crate::leanh::lean_dec(v_unused_2137_);
                            v_unused_2138_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                            crate::leanh::lean_dec(v_unused_2138_);
                            v_unused_2139_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                            crate::leanh::lean_dec(v_unused_2139_);
                            v_unused_2140_ = crate::leanh::lean_ctor_get(v_r_1869_, 0);
                            crate::leanh::lean_dec(v_unused_2140_);
                            v___x_2076_ = v_r_1869_;
                            v_isShared_2077_ = v_isSharedCheck_2135_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_1869_);
                            v___x_2076_ = crate::leanh::lean_box(0);
                            v_isShared_2077_ = v_isSharedCheck_2135_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_r_2056_);
                    if crate::leanh::lean_obj_tag(v_l_2055_) == 0 {
                        crate::leanh::lean_inc(v_v_2054_);
                        crate::leanh::lean_inc(v_k_2053_);
                        crate::leanh::lean_inc(v_size_2052_);
                        v_isSharedCheck_2178_ = (!crate::leanh::lean_is_exclusive(v_r_1869_)) as u8;
                        if v_isSharedCheck_2178_ == 0 {
                            v_unused_2179_ = crate::leanh::lean_ctor_get(v_r_1869_, 4);
                            crate::leanh::lean_dec(v_unused_2179_);
                            v_unused_2180_ = crate::leanh::lean_ctor_get(v_r_1869_, 3);
                            crate::leanh::lean_dec(v_unused_2180_);
                            v_unused_2181_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                            crate::leanh::lean_dec(v_unused_2181_);
                            v_unused_2182_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                            crate::leanh::lean_dec(v_unused_2182_);
                            v_unused_2183_ = crate::leanh::lean_ctor_get(v_r_1869_, 0);
                            crate::leanh::lean_dec(v_unused_2183_);
                            v___x_2142_ = v_r_1869_;
                            v_isShared_2143_ = v_isSharedCheck_2178_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_1869_);
                            v___x_2142_ = crate::leanh::lean_box(0);
                            v_isShared_2143_ = v_isSharedCheck_2178_;
                            state = 38;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_2056_) == 0 {
                            crate::leanh::lean_inc(v_v_2054_);
                            crate::leanh::lean_inc(v_k_2053_);
                            v_isSharedCheck_2197_ =
                                (!crate::leanh::lean_is_exclusive(v_r_1869_)) as u8;
                            if v_isSharedCheck_2197_ == 0 {
                                v_unused_2198_ = crate::leanh::lean_ctor_get(v_r_1869_, 4);
                                crate::leanh::lean_dec(v_unused_2198_);
                                v_unused_2199_ = crate::leanh::lean_ctor_get(v_r_1869_, 3);
                                crate::leanh::lean_dec(v_unused_2199_);
                                v_unused_2200_ = crate::leanh::lean_ctor_get(v_r_1869_, 2);
                                crate::leanh::lean_dec(v_unused_2200_);
                                v_unused_2201_ = crate::leanh::lean_ctor_get(v_r_1869_, 1);
                                crate::leanh::lean_dec(v_unused_2201_);
                                v_unused_2202_ = crate::leanh::lean_ctor_get(v_r_1869_, 0);
                                crate::leanh::lean_dec(v_unused_2202_);
                                v___x_2185_ = v_r_1869_;
                                v_isShared_2186_ = v_isSharedCheck_2197_;
                                state = 45;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_r_1869_);
                                v___x_2185_ = crate::leanh::lean_box(0);
                                v_isShared_2186_ = v_isSharedCheck_2197_;
                                state = 45;
                                continue;
                            }
                        } else {
                            v_k_2203_ = crate::leanh::lean_ctor_get(v_d_2061_, 0);
                            crate::leanh::lean_inc(v_k_2203_);
                            v_v_2204_ = crate::leanh::lean_ctor_get(v_d_2061_, 1);
                            crate::leanh::lean_inc(v_v_2204_);
                            crate::leanh::lean_dec_ref(v_d_2061_);
                            v___x_2205_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_2060_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2059_, 4, v_r_1869_);
                                crate::leanh::lean_ctor_set(v___x_2059_, 3, v_r_2056_);
                                crate::leanh::lean_ctor_set(v___x_2059_, 2, v_v_2204_);
                                crate::leanh::lean_ctor_set(v___x_2059_, 1, v_k_2203_);
                                crate::leanh::lean_ctor_set(v___x_2059_, 0, v___x_2205_);
                                v___x_2207_ = v___x_2059_;
                                state = 48;
                                continue;
                            } else {
                                v_reuseFailAlloc_2208_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2203_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2204_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_r_2056_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_r_1869_);
                                v___x_2207_ = v_reuseFailAlloc_2208_;
                                state = 48;
                                continue;
                            }
                        }
                    }
                }
            }
            28 => {
                return v___x_2073_;
            }
            29 => {
                if crate::leanh::lean_obj_tag(v_l_2055_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_2056_) == 0 {
                        v_size_2078_ = crate::leanh::lean_ctor_get(v_l_2055_, 0);
                        v_k_2079_ = crate::leanh::lean_ctor_get(v_l_2055_, 1);
                        v_v_2080_ = crate::leanh::lean_ctor_get(v_l_2055_, 2);
                        v_l_2081_ = crate::leanh::lean_ctor_get(v_l_2055_, 3);
                        v_r_2082_ = crate::leanh::lean_ctor_get(v_l_2055_, 4);
                        v_size_2083_ = crate::leanh::lean_ctor_get(v_r_2056_, 0);
                        v___x_2084_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2085_ = lean_nat_mul(v___x_2084_, v_size_2083_);
                        v___x_2086_ = lean_nat_dec_lt(v_size_2078_, v___x_2085_);
                        crate::leanh::lean_dec(v___x_2085_);
                        if v___x_2086_ == 0 {
                            crate::leanh::lean_inc(v_r_2082_);
                            crate::leanh::lean_inc(v_l_2081_);
                            crate::leanh::lean_inc(v_v_2080_);
                            crate::leanh::lean_inc(v_k_2079_);
                            v_isSharedCheck_2115_ =
                                (!crate::leanh::lean_is_exclusive(v_l_2055_)) as u8;
                            if v_isSharedCheck_2115_ == 0 {
                                v_unused_2116_ = crate::leanh::lean_ctor_get(v_l_2055_, 4);
                                crate::leanh::lean_dec(v_unused_2116_);
                                v_unused_2117_ = crate::leanh::lean_ctor_get(v_l_2055_, 3);
                                crate::leanh::lean_dec(v_unused_2117_);
                                v_unused_2118_ = crate::leanh::lean_ctor_get(v_l_2055_, 2);
                                crate::leanh::lean_dec(v_unused_2118_);
                                v_unused_2119_ = crate::leanh::lean_ctor_get(v_l_2055_, 1);
                                crate::leanh::lean_dec(v_unused_2119_);
                                v_unused_2120_ = crate::leanh::lean_ctor_get(v_l_2055_, 0);
                                crate::leanh::lean_dec(v_unused_2120_);
                                v___x_2088_ = v_l_2055_;
                                v_isShared_2089_ = v_isSharedCheck_2115_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_2055_);
                                v___x_2088_ = crate::leanh::lean_box(0);
                                v_isShared_2089_ = v_isSharedCheck_2115_;
                                state = 30;
                                continue;
                            }
                        } else {
                            v___x_2121_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2122_ = lean_nat_add(v___x_2121_, v_size_2065_);
                            v___x_2123_ = lean_nat_add(v___x_2122_, v_size_2052_);
                            crate::leanh::lean_dec(v_size_2052_);
                            v___x_2124_ = lean_nat_add(v___x_2122_, v_size_2078_);
                            crate::leanh::lean_dec(v___x_2122_);
                            if v_isShared_2077_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2076_, 4, v_l_2055_);
                                crate::leanh::lean_ctor_set(v___x_2076_, 3, v_tree_2062_);
                                crate::leanh::lean_ctor_set(v___x_2076_, 2, v_v_2064_);
                                crate::leanh::lean_ctor_set(v___x_2076_, 1, v_k_2063_);
                                crate::leanh::lean_ctor_set(v___x_2076_, 0, v___x_2124_);
                                v___x_2126_ = v___x_2076_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_2130_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2124_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_k_2063_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_v_2064_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2130_,
                                    3,
                                    v_tree_2062_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 4, v_l_2055_);
                                v___x_2126_ = v_reuseFailAlloc_2130_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_2055_, 5);
                        crate::leanh::lean_del_object(v___x_2076_);
                        crate::leanh::lean_dec(v_v_2064_);
                        crate::leanh::lean_dec_ref_known(v_tree_2062_, 5);
                        crate::leanh::lean_dec(v_k_2063_);
                        crate::leanh::lean_del_object(v___x_2059_);
                        crate::leanh::lean_dec(v_v_2054_);
                        crate::leanh::lean_dec(v_k_2053_);
                        crate::leanh::lean_dec(v_size_2052_);
                        v___x_2131_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7);
                        v___x_2132_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2131_);
                        return v___x_2132_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2076_);
                    crate::leanh::lean_dec(v_v_2064_);
                    crate::leanh::lean_dec_ref_known(v_tree_2062_, 5);
                    crate::leanh::lean_dec(v_k_2063_);
                    crate::leanh::lean_del_object(v___x_2059_);
                    crate::leanh::lean_dec(v_r_2056_);
                    crate::leanh::lean_dec(v_v_2054_);
                    crate::leanh::lean_dec(v_k_2053_);
                    crate::leanh::lean_dec(v_size_2052_);
                    v___x_2133_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8);
                    v___x_2134_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2133_);
                    return v___x_2134_;
                }
            }
            30 => {
                v___x_2090_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2091_ = lean_nat_add(v___x_2090_, v_size_2065_);
                v___x_2092_ = lean_nat_add(v___x_2091_, v_size_2052_);
                crate::leanh::lean_dec(v_size_2052_);
                if crate::leanh::lean_obj_tag(v_l_2081_) == 0 {
                    v_size_2113_ = crate::leanh::lean_ctor_get(v_l_2081_, 0);
                    crate::leanh::lean_inc(v_size_2113_);
                    v___y_2105_ = v_size_2113_;
                    state = 34;
                    continue;
                } else {
                    v___x_2114_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2105_ = v___x_2114_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_2097_ = lean_nat_add(v___y_2095_, v___y_2096_);
                crate::leanh::lean_dec(v___y_2096_);
                crate::leanh::lean_dec(v___y_2095_);
                if v_isShared_2089_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2088_, 4, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 3, v_r_2082_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 2, v_v_2054_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 1, v_k_2053_);
                    crate::leanh::lean_ctor_set(v___x_2088_, 0, v___x_2097_);
                    v___x_2099_ = v___x_2088_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2103_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_k_2053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_v_2054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_r_2082_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_r_2056_);
                    v___x_2099_ = v_reuseFailAlloc_2103_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2077_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2076_, 4, v___x_2099_);
                    crate::leanh::lean_ctor_set(v___x_2076_, 3, v___y_2094_);
                    crate::leanh::lean_ctor_set(v___x_2076_, 2, v_v_2080_);
                    crate::leanh::lean_ctor_set(v___x_2076_, 1, v_k_2079_);
                    crate::leanh::lean_ctor_set(v___x_2076_, 0, v___x_2092_);
                    v___x_2101_ = v___x_2076_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2102_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_k_2079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_v_2080_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 3, v___y_2094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 4, v___x_2099_);
                    v___x_2101_ = v_reuseFailAlloc_2102_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2101_;
            }
            34 => {
                v___x_2106_ = lean_nat_add(v___x_2091_, v___y_2105_);
                crate::leanh::lean_dec(v___y_2105_);
                crate::leanh::lean_dec(v___x_2091_);
                if v_isShared_2060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2059_, 4, v_l_2081_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 3, v_tree_2062_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 2, v_v_2064_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 1, v_k_2063_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 0, v___x_2106_);
                    v___x_2108_ = v___x_2059_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2112_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_k_2063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_2064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_tree_2062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_l_2081_);
                    v___x_2108_ = v_reuseFailAlloc_2112_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2109_ = lean_nat_add(v___x_2090_, v_size_2083_);
                if crate::leanh::lean_obj_tag(v_r_2082_) == 0 {
                    v_size_2110_ = crate::leanh::lean_ctor_get(v_r_2082_, 0);
                    crate::leanh::lean_inc(v_size_2110_);
                    v___y_2094_ = v___x_2108_;
                    v___y_2095_ = v___x_2109_;
                    v___y_2096_ = v_size_2110_;
                    state = 31;
                    continue;
                } else {
                    v___x_2111_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2094_ = v___x_2108_;
                    v___y_2095_ = v___x_2109_;
                    v___y_2096_ = v___x_2111_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                if v_isShared_2060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2059_, 4, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 3, v___x_2126_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 2, v_v_2054_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 1, v_k_2053_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 0, v___x_2123_);
                    v___x_2128_ = v___x_2059_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_k_2053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_v_2054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 3, v___x_2126_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_r_2056_);
                    v___x_2128_ = v_reuseFailAlloc_2129_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2128_;
            }
            38 => {
                if crate::leanh::lean_obj_tag(v_r_2056_) == 0 {
                    v_k_2144_ = crate::leanh::lean_ctor_get(v_d_2061_, 0);
                    crate::leanh::lean_inc(v_k_2144_);
                    v_v_2145_ = crate::leanh::lean_ctor_get(v_d_2061_, 1);
                    crate::leanh::lean_inc(v_v_2145_);
                    crate::leanh::lean_dec_ref(v_d_2061_);
                    v_size_2146_ = crate::leanh::lean_ctor_get(v_l_2055_, 0);
                    v___x_2147_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2148_ = lean_nat_add(v___x_2147_, v_size_2052_);
                    crate::leanh::lean_dec(v_size_2052_);
                    v___x_2149_ = lean_nat_add(v___x_2147_, v_size_2146_);
                    if v_isShared_2143_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2142_, 4, v_l_2055_);
                        crate::leanh::lean_ctor_set(v___x_2142_, 3, v_tree_2062_);
                        crate::leanh::lean_ctor_set(v___x_2142_, 2, v_v_2145_);
                        crate::leanh::lean_ctor_set(v___x_2142_, 1, v_k_2144_);
                        crate::leanh::lean_ctor_set(v___x_2142_, 0, v___x_2149_);
                        v___x_2151_ = v___x_2142_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_2155_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2149_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_2144_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_2145_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_tree_2062_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_l_2055_);
                        v___x_2151_ = v_reuseFailAlloc_2155_;
                        state = 39;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_2052_);
                    v_k_2156_ = crate::leanh::lean_ctor_get(v_d_2061_, 0);
                    crate::leanh::lean_inc(v_k_2156_);
                    v_v_2157_ = crate::leanh::lean_ctor_get(v_d_2061_, 1);
                    crate::leanh::lean_inc(v_v_2157_);
                    crate::leanh::lean_dec_ref(v_d_2061_);
                    v_k_2158_ = crate::leanh::lean_ctor_get(v_l_2055_, 1);
                    v_v_2159_ = crate::leanh::lean_ctor_get(v_l_2055_, 2);
                    v_isSharedCheck_2174_ = (!crate::leanh::lean_is_exclusive(v_l_2055_)) as u8;
                    if v_isSharedCheck_2174_ == 0 {
                        v_unused_2175_ = crate::leanh::lean_ctor_get(v_l_2055_, 4);
                        crate::leanh::lean_dec(v_unused_2175_);
                        v_unused_2176_ = crate::leanh::lean_ctor_get(v_l_2055_, 3);
                        crate::leanh::lean_dec(v_unused_2176_);
                        v_unused_2177_ = crate::leanh::lean_ctor_get(v_l_2055_, 0);
                        crate::leanh::lean_dec(v_unused_2177_);
                        v___x_2161_ = v_l_2055_;
                        v_isShared_2162_ = v_isSharedCheck_2174_;
                        state = 41;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_v_2159_);
                        crate::leanh::lean_inc(v_k_2158_);
                        crate::leanh::lean_dec(v_l_2055_);
                        v___x_2161_ = crate::leanh::lean_box(0);
                        v_isShared_2162_ = v_isSharedCheck_2174_;
                        state = 41;
                        continue;
                    }
                }
            }
            39 => {
                if v_isShared_2060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2059_, 4, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 3, v___x_2151_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 2, v_v_2054_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 1, v_k_2053_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 0, v___x_2148_);
                    v___x_2153_ = v___x_2059_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2148_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_k_2053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_v_2054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 3, v___x_2151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_r_2056_);
                    v___x_2153_ = v_reuseFailAlloc_2154_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2153_;
            }
            41 => {
                v___x_2163_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2164_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2161_, 4, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2161_, 3, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2161_, 2, v_v_2157_);
                    crate::leanh::lean_ctor_set(v___x_2161_, 1, v_k_2156_);
                    crate::leanh::lean_ctor_set(v___x_2161_, 0, v___x_2164_);
                    v___x_2166_ = v___x_2161_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2173_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_k_2156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_v_2157_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 3, v_r_2056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 4, v_r_2056_);
                    v___x_2166_ = v_reuseFailAlloc_2173_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_2143_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2142_, 3, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2142_, 0, v___x_2164_);
                    v___x_2168_ = v___x_2142_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_2053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_2054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_r_2056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_r_2056_);
                    v___x_2168_ = v_reuseFailAlloc_2172_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_2060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2059_, 4, v___x_2168_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 3, v___x_2166_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 2, v_v_2159_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 1, v_k_2158_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 0, v___x_2163_);
                    v___x_2170_ = v___x_2059_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_2158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_2159_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 3, v___x_2166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 4, v___x_2168_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_2170_;
            }
            45 => {
                v_k_2187_ = crate::leanh::lean_ctor_get(v_d_2061_, 0);
                crate::leanh::lean_inc(v_k_2187_);
                v_v_2188_ = crate::leanh::lean_ctor_get(v_d_2061_, 1);
                crate::leanh::lean_inc(v_v_2188_);
                crate::leanh::lean_dec_ref(v_d_2061_);
                v___x_2189_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2190_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2186_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2185_, 4, v_l_2055_);
                    crate::leanh::lean_ctor_set(v___x_2185_, 2, v_v_2188_);
                    crate::leanh::lean_ctor_set(v___x_2185_, 1, v_k_2187_);
                    crate::leanh::lean_ctor_set(v___x_2185_, 0, v___x_2190_);
                    v___x_2192_ = v___x_2185_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_k_2187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 2, v_v_2188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 3, v_l_2055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 4, v_l_2055_);
                    v___x_2192_ = v_reuseFailAlloc_2196_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_2060_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2059_, 4, v_r_2056_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 3, v___x_2192_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 2, v_v_2054_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 1, v_k_2053_);
                    crate::leanh::lean_ctor_set(v___x_2059_, 0, v___x_2189_);
                    v___x_2194_ = v___x_2059_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2189_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_k_2053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_v_2054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 3, v___x_2192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 4, v_r_2056_);
                    v___x_2194_ = v_reuseFailAlloc_2195_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_2194_;
            }
            48 => {
                return v___x_2207_;
            }
            49 => {
                v_d_2218_ = l_Std_DTreeMap_Internal_Impl_minView_x21___redArg(
                    v_k_2053_, v_v_2054_, v_l_2055_, v_r_2056_,
                );
                v_tree_2219_ = crate::leanh::lean_ctor_get(v_d_2218_, 2);
                crate::leanh::lean_inc(v_tree_2219_);
                if crate::leanh::lean_obj_tag(v_tree_2219_) == 0 {
                    v_k_2220_ = crate::leanh::lean_ctor_get(v_d_2218_, 0);
                    crate::leanh::lean_inc(v_k_2220_);
                    v_v_2221_ = crate::leanh::lean_ctor_get(v_d_2218_, 1);
                    crate::leanh::lean_inc(v_v_2221_);
                    crate::leanh::lean_dec_ref(v_d_2218_);
                    v_size_2222_ = crate::leanh::lean_ctor_get(v_tree_2219_, 0);
                    v___x_2223_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2224_ = lean_nat_mul(v___x_2223_, v_size_2222_);
                    v___x_2225_ = lean_nat_dec_lt(v___x_2224_, v_size_2047_);
                    crate::leanh::lean_dec(v___x_2224_);
                    if v___x_2225_ == 0 {
                        crate::leanh::lean_dec(v_r_2051_);
                        v___x_2226_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2227_ = lean_nat_add(v___x_2226_, v_size_2047_);
                        v___x_2228_ = lean_nat_add(v___x_2227_, v_size_2222_);
                        crate::leanh::lean_dec(v___x_2227_);
                        if v_isShared_2217_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2216_, 4, v_tree_2219_);
                            crate::leanh::lean_ctor_set(v___x_2216_, 3, v_l_1868_);
                            crate::leanh::lean_ctor_set(v___x_2216_, 2, v_v_2221_);
                            crate::leanh::lean_ctor_set(v___x_2216_, 1, v_k_2220_);
                            crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2228_);
                            v___x_2230_ = v___x_2216_;
                            state = 50;
                            continue;
                        } else {
                            v_reuseFailAlloc_2231_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_k_2220_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_v_2221_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_l_1868_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_tree_2219_);
                            v___x_2230_ = v_reuseFailAlloc_2231_;
                            state = 50;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_l_2050_);
                        crate::leanh::lean_inc(v_v_2049_);
                        crate::leanh::lean_inc(v_k_2048_);
                        crate::leanh::lean_inc(v_size_2047_);
                        v_isSharedCheck_2303_ = (!crate::leanh::lean_is_exclusive(v_l_1868_)) as u8;
                        if v_isSharedCheck_2303_ == 0 {
                            v_unused_2304_ = crate::leanh::lean_ctor_get(v_l_1868_, 4);
                            crate::leanh::lean_dec(v_unused_2304_);
                            v_unused_2305_ = crate::leanh::lean_ctor_get(v_l_1868_, 3);
                            crate::leanh::lean_dec(v_unused_2305_);
                            v_unused_2306_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                            crate::leanh::lean_dec(v_unused_2306_);
                            v_unused_2307_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                            crate::leanh::lean_dec(v_unused_2307_);
                            v_unused_2308_ = crate::leanh::lean_ctor_get(v_l_1868_, 0);
                            crate::leanh::lean_dec(v_unused_2308_);
                            v___x_2233_ = v_l_1868_;
                            v_isShared_2234_ = v_isSharedCheck_2303_;
                            state = 51;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_1868_);
                            v___x_2233_ = crate::leanh::lean_box(0);
                            v_isShared_2234_ = v_isSharedCheck_2303_;
                            state = 51;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_2050_) == 0 {
                        crate::leanh::lean_inc_ref(v_l_2050_);
                        crate::leanh::lean_inc(v_v_2049_);
                        crate::leanh::lean_inc(v_k_2048_);
                        crate::leanh::lean_inc(v_size_2047_);
                        v_isSharedCheck_2334_ = (!crate::leanh::lean_is_exclusive(v_l_1868_)) as u8;
                        if v_isSharedCheck_2334_ == 0 {
                            v_unused_2335_ = crate::leanh::lean_ctor_get(v_l_1868_, 4);
                            crate::leanh::lean_dec(v_unused_2335_);
                            v_unused_2336_ = crate::leanh::lean_ctor_get(v_l_1868_, 3);
                            crate::leanh::lean_dec(v_unused_2336_);
                            v_unused_2337_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                            crate::leanh::lean_dec(v_unused_2337_);
                            v_unused_2338_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                            crate::leanh::lean_dec(v_unused_2338_);
                            v_unused_2339_ = crate::leanh::lean_ctor_get(v_l_1868_, 0);
                            crate::leanh::lean_dec(v_unused_2339_);
                            v___x_2310_ = v_l_1868_;
                            v_isShared_2311_ = v_isSharedCheck_2334_;
                            state = 61;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_1868_);
                            v___x_2310_ = crate::leanh::lean_box(0);
                            v_isShared_2311_ = v_isSharedCheck_2334_;
                            state = 61;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_2051_) == 0 {
                            crate::leanh::lean_inc(v_l_2050_);
                            crate::leanh::lean_inc(v_v_2049_);
                            crate::leanh::lean_inc(v_k_2048_);
                            v_isSharedCheck_2365_ =
                                (!crate::leanh::lean_is_exclusive(v_l_1868_)) as u8;
                            if v_isSharedCheck_2365_ == 0 {
                                v_unused_2366_ = crate::leanh::lean_ctor_get(v_l_1868_, 4);
                                crate::leanh::lean_dec(v_unused_2366_);
                                v_unused_2367_ = crate::leanh::lean_ctor_get(v_l_1868_, 3);
                                crate::leanh::lean_dec(v_unused_2367_);
                                v_unused_2368_ = crate::leanh::lean_ctor_get(v_l_1868_, 2);
                                crate::leanh::lean_dec(v_unused_2368_);
                                v_unused_2369_ = crate::leanh::lean_ctor_get(v_l_1868_, 1);
                                crate::leanh::lean_dec(v_unused_2369_);
                                v_unused_2370_ = crate::leanh::lean_ctor_get(v_l_1868_, 0);
                                crate::leanh::lean_dec(v_unused_2370_);
                                v___x_2341_ = v_l_1868_;
                                v_isShared_2342_ = v_isSharedCheck_2365_;
                                state = 66;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_1868_);
                                v___x_2341_ = crate::leanh::lean_box(0);
                                v_isShared_2342_ = v_isSharedCheck_2365_;
                                state = 66;
                                continue;
                            }
                        } else {
                            v_k_2371_ = crate::leanh::lean_ctor_get(v_d_2218_, 0);
                            crate::leanh::lean_inc(v_k_2371_);
                            v_v_2372_ = crate::leanh::lean_ctor_get(v_d_2218_, 1);
                            crate::leanh::lean_inc(v_v_2372_);
                            crate::leanh::lean_dec_ref(v_d_2218_);
                            v___x_2373_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_2217_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2216_, 4, v_r_2051_);
                                crate::leanh::lean_ctor_set(v___x_2216_, 3, v_l_1868_);
                                crate::leanh::lean_ctor_set(v___x_2216_, 2, v_v_2372_);
                                crate::leanh::lean_ctor_set(v___x_2216_, 1, v_k_2371_);
                                crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2373_);
                                v___x_2375_ = v___x_2216_;
                                state = 71;
                                continue;
                            } else {
                                v_reuseFailAlloc_2376_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_k_2371_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 2, v_v_2372_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 3, v_l_1868_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 4, v_r_2051_);
                                v___x_2375_ = v_reuseFailAlloc_2376_;
                                state = 71;
                                continue;
                            }
                        }
                    }
                }
            }
            50 => {
                return v___x_2230_;
            }
            51 => {
                if crate::leanh::lean_obj_tag(v_l_2050_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_2051_) == 0 {
                        v_size_2235_ = crate::leanh::lean_ctor_get(v_l_2050_, 0);
                        v_size_2236_ = crate::leanh::lean_ctor_get(v_r_2051_, 0);
                        v_k_2237_ = crate::leanh::lean_ctor_get(v_r_2051_, 1);
                        v_v_2238_ = crate::leanh::lean_ctor_get(v_r_2051_, 2);
                        v_l_2239_ = crate::leanh::lean_ctor_get(v_r_2051_, 3);
                        v_r_2240_ = crate::leanh::lean_ctor_get(v_r_2051_, 4);
                        v___x_2241_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2242_ = lean_nat_mul(v___x_2241_, v_size_2235_);
                        v___x_2243_ = lean_nat_dec_lt(v_size_2236_, v___x_2242_);
                        crate::leanh::lean_dec(v___x_2242_);
                        if v___x_2243_ == 0 {
                            crate::leanh::lean_inc(v_r_2240_);
                            crate::leanh::lean_inc(v_l_2239_);
                            crate::leanh::lean_inc(v_v_2238_);
                            crate::leanh::lean_inc(v_k_2237_);
                            crate::leanh::lean_del_object(v___x_2233_);
                            v_isSharedCheck_2282_ =
                                (!crate::leanh::lean_is_exclusive(v_r_2051_)) as u8;
                            if v_isSharedCheck_2282_ == 0 {
                                v_unused_2283_ = crate::leanh::lean_ctor_get(v_r_2051_, 4);
                                crate::leanh::lean_dec(v_unused_2283_);
                                v_unused_2284_ = crate::leanh::lean_ctor_get(v_r_2051_, 3);
                                crate::leanh::lean_dec(v_unused_2284_);
                                v_unused_2285_ = crate::leanh::lean_ctor_get(v_r_2051_, 2);
                                crate::leanh::lean_dec(v_unused_2285_);
                                v_unused_2286_ = crate::leanh::lean_ctor_get(v_r_2051_, 1);
                                crate::leanh::lean_dec(v_unused_2286_);
                                v_unused_2287_ = crate::leanh::lean_ctor_get(v_r_2051_, 0);
                                crate::leanh::lean_dec(v_unused_2287_);
                                v___x_2245_ = v_r_2051_;
                                v_isShared_2246_ = v_isSharedCheck_2282_;
                                state = 52;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_r_2051_);
                                v___x_2245_ = crate::leanh::lean_box(0);
                                v_isShared_2246_ = v_isSharedCheck_2282_;
                                state = 52;
                                continue;
                            }
                        } else {
                            v___x_2288_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2289_ = lean_nat_add(v___x_2288_, v_size_2047_);
                            crate::leanh::lean_dec(v_size_2047_);
                            v___x_2290_ = lean_nat_add(v___x_2289_, v_size_2222_);
                            crate::leanh::lean_dec(v___x_2289_);
                            v___x_2291_ = lean_nat_add(v___x_2288_, v_size_2222_);
                            v___x_2292_ = lean_nat_add(v___x_2291_, v_size_2236_);
                            crate::leanh::lean_dec(v___x_2291_);
                            if v_isShared_2217_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2216_, 4, v_tree_2219_);
                                crate::leanh::lean_ctor_set(v___x_2216_, 3, v_r_2051_);
                                crate::leanh::lean_ctor_set(v___x_2216_, 2, v_v_2221_);
                                crate::leanh::lean_ctor_set(v___x_2216_, 1, v_k_2220_);
                                crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2292_);
                                v___x_2294_ = v___x_2216_;
                                state = 59;
                                continue;
                            } else {
                                v_reuseFailAlloc_2298_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2292_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_k_2220_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 2, v_v_2221_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 3, v_r_2051_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2298_,
                                    4,
                                    v_tree_2219_,
                                );
                                v___x_2294_ = v_reuseFailAlloc_2298_;
                                state = 59;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_2050_, 5);
                        crate::leanh::lean_del_object(v___x_2233_);
                        crate::leanh::lean_dec(v_v_2221_);
                        crate::leanh::lean_dec(v_k_2220_);
                        crate::leanh::lean_dec_ref_known(v_tree_2219_, 5);
                        crate::leanh::lean_del_object(v___x_2216_);
                        crate::leanh::lean_dec(v_v_2049_);
                        crate::leanh::lean_dec(v_k_2048_);
                        crate::leanh::lean_dec(v_size_2047_);
                        v___x_2299_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3);
                        v___x_2300_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2299_);
                        return v___x_2300_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2233_);
                    crate::leanh::lean_dec(v_v_2221_);
                    crate::leanh::lean_dec_ref_known(v_tree_2219_, 5);
                    crate::leanh::lean_dec(v_k_2220_);
                    crate::leanh::lean_del_object(v___x_2216_);
                    crate::leanh::lean_dec(v_r_2051_);
                    crate::leanh::lean_dec(v_v_2049_);
                    crate::leanh::lean_dec(v_k_2048_);
                    crate::leanh::lean_dec(v_size_2047_);
                    v___x_2301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4);
                    v___x_2302_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2301_);
                    return v___x_2302_;
                }
            }
            52 => {
                v___x_2247_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2248_ = lean_nat_add(v___x_2247_, v_size_2047_);
                crate::leanh::lean_dec(v_size_2047_);
                v___x_2249_ = lean_nat_add(v___x_2248_, v_size_2222_);
                crate::leanh::lean_dec(v___x_2248_);
                v___x_2270_ = lean_nat_add(v___x_2247_, v_size_2235_);
                if crate::leanh::lean_obj_tag(v_l_2239_) == 0 {
                    v_size_2280_ = crate::leanh::lean_ctor_get(v_l_2239_, 0);
                    crate::leanh::lean_inc(v_size_2280_);
                    v___y_2272_ = v_size_2280_;
                    state = 57;
                    continue;
                } else {
                    v___x_2281_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2272_ = v___x_2281_;
                    state = 57;
                    continue;
                }
            }
            53 => {
                v___x_2254_ = lean_nat_add(v___y_2252_, v___y_2253_);
                crate::leanh::lean_dec(v___y_2253_);
                crate::leanh::lean_dec(v___y_2252_);
                crate::leanh::lean_inc_ref(v_tree_2219_);
                if v_isShared_2246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2245_, 4, v_tree_2219_);
                    crate::leanh::lean_ctor_set(v___x_2245_, 3, v_r_2240_);
                    crate::leanh::lean_ctor_set(v___x_2245_, 2, v_v_2221_);
                    crate::leanh::lean_ctor_set(v___x_2245_, 1, v_k_2220_);
                    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2254_);
                    v___x_2256_ = v___x_2245_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2254_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_k_2220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_v_2221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 3, v_r_2240_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 4, v_tree_2219_);
                    v___x_2256_ = v_reuseFailAlloc_2269_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v_isSharedCheck_2263_ = (!crate::leanh::lean_is_exclusive(v_tree_2219_)) as u8;
                if v_isSharedCheck_2263_ == 0 {
                    v_unused_2264_ = crate::leanh::lean_ctor_get(v_tree_2219_, 4);
                    crate::leanh::lean_dec(v_unused_2264_);
                    v_unused_2265_ = crate::leanh::lean_ctor_get(v_tree_2219_, 3);
                    crate::leanh::lean_dec(v_unused_2265_);
                    v_unused_2266_ = crate::leanh::lean_ctor_get(v_tree_2219_, 2);
                    crate::leanh::lean_dec(v_unused_2266_);
                    v_unused_2267_ = crate::leanh::lean_ctor_get(v_tree_2219_, 1);
                    crate::leanh::lean_dec(v_unused_2267_);
                    v_unused_2268_ = crate::leanh::lean_ctor_get(v_tree_2219_, 0);
                    crate::leanh::lean_dec(v_unused_2268_);
                    v___x_2258_ = v_tree_2219_;
                    v_isShared_2259_ = v_isSharedCheck_2263_;
                    state = 55;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tree_2219_);
                    v___x_2258_ = crate::leanh::lean_box(0);
                    v_isShared_2259_ = v_isSharedCheck_2263_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                if v_isShared_2259_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2258_, 4, v___x_2256_);
                    crate::leanh::lean_ctor_set(v___x_2258_, 3, v___y_2251_);
                    crate::leanh::lean_ctor_set(v___x_2258_, 2, v_v_2238_);
                    crate::leanh::lean_ctor_set(v___x_2258_, 1, v_k_2237_);
                    crate::leanh::lean_ctor_set(v___x_2258_, 0, v___x_2249_);
                    v___x_2261_ = v___x_2258_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2262_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_k_2237_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_v_2238_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 3, v___y_2251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 4, v___x_2256_);
                    v___x_2261_ = v_reuseFailAlloc_2262_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_2261_;
            }
            57 => {
                v___x_2273_ = lean_nat_add(v___x_2270_, v___y_2272_);
                crate::leanh::lean_dec(v___y_2272_);
                crate::leanh::lean_dec(v___x_2270_);
                if v_isShared_2217_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2216_, 4, v_l_2239_);
                    crate::leanh::lean_ctor_set(v___x_2216_, 3, v_l_2050_);
                    crate::leanh::lean_ctor_set(v___x_2216_, 2, v_v_2049_);
                    crate::leanh::lean_ctor_set(v___x_2216_, 1, v_k_2048_);
                    crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2273_);
                    v___x_2275_ = v___x_2216_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2279_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_k_2048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_v_2049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_l_2050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 4, v_l_2239_);
                    v___x_2275_ = v_reuseFailAlloc_2279_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_2276_ = lean_nat_add(v___x_2247_, v_size_2222_);
                if crate::leanh::lean_obj_tag(v_r_2240_) == 0 {
                    v_size_2277_ = crate::leanh::lean_ctor_get(v_r_2240_, 0);
                    crate::leanh::lean_inc(v_size_2277_);
                    v___y_2251_ = v___x_2275_;
                    v___y_2252_ = v___x_2276_;
                    v___y_2253_ = v_size_2277_;
                    state = 53;
                    continue;
                } else {
                    v___x_2278_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2251_ = v___x_2275_;
                    v___y_2252_ = v___x_2276_;
                    v___y_2253_ = v___x_2278_;
                    state = 53;
                    continue;
                }
            }
            59 => {
                if v_isShared_2234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2233_, 4, v___x_2294_);
                    crate::leanh::lean_ctor_set(v___x_2233_, 0, v___x_2290_);
                    v___x_2296_ = v___x_2233_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_k_2048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 2, v_v_2049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 3, v_l_2050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 4, v___x_2294_);
                    v___x_2296_ = v_reuseFailAlloc_2297_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2296_;
            }
            61 => {
                if crate::leanh::lean_obj_tag(v_r_2051_) == 0 {
                    v_k_2312_ = crate::leanh::lean_ctor_get(v_d_2218_, 0);
                    crate::leanh::lean_inc(v_k_2312_);
                    v_v_2313_ = crate::leanh::lean_ctor_get(v_d_2218_, 1);
                    crate::leanh::lean_inc(v_v_2313_);
                    crate::leanh::lean_dec_ref(v_d_2218_);
                    v_size_2314_ = crate::leanh::lean_ctor_get(v_r_2051_, 0);
                    v___x_2315_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2316_ = lean_nat_add(v___x_2315_, v_size_2047_);
                    crate::leanh::lean_dec(v_size_2047_);
                    v___x_2317_ = lean_nat_add(v___x_2315_, v_size_2314_);
                    if v_isShared_2217_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2216_, 4, v_tree_2219_);
                        crate::leanh::lean_ctor_set(v___x_2216_, 3, v_r_2051_);
                        crate::leanh::lean_ctor_set(v___x_2216_, 2, v_v_2313_);
                        crate::leanh::lean_ctor_set(v___x_2216_, 1, v_k_2312_);
                        crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2317_);
                        v___x_2319_ = v___x_2216_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_2323_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2317_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_k_2312_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_v_2313_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_r_2051_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 4, v_tree_2219_);
                        v___x_2319_ = v_reuseFailAlloc_2323_;
                        state = 62;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_2047_);
                    v_k_2324_ = crate::leanh::lean_ctor_get(v_d_2218_, 0);
                    crate::leanh::lean_inc(v_k_2324_);
                    v_v_2325_ = crate::leanh::lean_ctor_get(v_d_2218_, 1);
                    crate::leanh::lean_inc(v_v_2325_);
                    crate::leanh::lean_dec_ref(v_d_2218_);
                    v___x_2326_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2327_ = crate::leanh::lean_unsigned_to_nat(1);
                    if v_isShared_2217_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2216_, 4, v_r_2051_);
                        crate::leanh::lean_ctor_set(v___x_2216_, 3, v_r_2051_);
                        crate::leanh::lean_ctor_set(v___x_2216_, 2, v_v_2325_);
                        crate::leanh::lean_ctor_set(v___x_2216_, 1, v_k_2324_);
                        crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2327_);
                        v___x_2329_ = v___x_2216_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2333_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2327_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_k_2324_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_v_2325_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_r_2051_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_r_2051_);
                        v___x_2329_ = v_reuseFailAlloc_2333_;
                        state = 64;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_2311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2310_, 4, v___x_2319_);
                    crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2316_);
                    v___x_2321_ = v___x_2310_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2316_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_k_2048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_v_2049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_l_2050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 4, v___x_2319_);
                    v___x_2321_ = v_reuseFailAlloc_2322_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_2321_;
            }
            64 => {
                if v_isShared_2311_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2310_, 4, v___x_2329_);
                    crate::leanh::lean_ctor_set(v___x_2310_, 0, v___x_2326_);
                    v___x_2331_ = v___x_2310_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2332_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_k_2048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_v_2049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_l_2050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 4, v___x_2329_);
                    v___x_2331_ = v_reuseFailAlloc_2332_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2331_;
            }
            66 => {
                v_k_2343_ = crate::leanh::lean_ctor_get(v_d_2218_, 0);
                crate::leanh::lean_inc(v_k_2343_);
                v_v_2344_ = crate::leanh::lean_ctor_get(v_d_2218_, 1);
                crate::leanh::lean_inc(v_v_2344_);
                crate::leanh::lean_dec_ref(v_d_2218_);
                v_k_2345_ = crate::leanh::lean_ctor_get(v_r_2051_, 1);
                v_v_2346_ = crate::leanh::lean_ctor_get(v_r_2051_, 2);
                v_isSharedCheck_2361_ = (!crate::leanh::lean_is_exclusive(v_r_2051_)) as u8;
                if v_isSharedCheck_2361_ == 0 {
                    v_unused_2362_ = crate::leanh::lean_ctor_get(v_r_2051_, 4);
                    crate::leanh::lean_dec(v_unused_2362_);
                    v_unused_2363_ = crate::leanh::lean_ctor_get(v_r_2051_, 3);
                    crate::leanh::lean_dec(v_unused_2363_);
                    v_unused_2364_ = crate::leanh::lean_ctor_get(v_r_2051_, 0);
                    crate::leanh::lean_dec(v_unused_2364_);
                    v___x_2348_ = v_r_2051_;
                    v_isShared_2349_ = v_isSharedCheck_2361_;
                    state = 67;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2346_);
                    crate::leanh::lean_inc(v_k_2345_);
                    crate::leanh::lean_dec(v_r_2051_);
                    v___x_2348_ = crate::leanh::lean_box(0);
                    v_isShared_2349_ = v_isSharedCheck_2361_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v___x_2350_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2351_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2349_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2348_, 4, v_l_2050_);
                    crate::leanh::lean_ctor_set(v___x_2348_, 3, v_l_2050_);
                    crate::leanh::lean_ctor_set(v___x_2348_, 2, v_v_2049_);
                    crate::leanh::lean_ctor_set(v___x_2348_, 1, v_k_2048_);
                    crate::leanh::lean_ctor_set(v___x_2348_, 0, v___x_2351_);
                    v___x_2353_ = v___x_2348_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_k_2048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_v_2049_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_l_2050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_l_2050_);
                    v___x_2353_ = v_reuseFailAlloc_2360_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_2217_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2216_, 4, v_l_2050_);
                    crate::leanh::lean_ctor_set(v___x_2216_, 3, v_l_2050_);
                    crate::leanh::lean_ctor_set(v___x_2216_, 2, v_v_2344_);
                    crate::leanh::lean_ctor_set(v___x_2216_, 1, v_k_2343_);
                    crate::leanh::lean_ctor_set(v___x_2216_, 0, v___x_2351_);
                    v___x_2355_ = v___x_2216_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_k_2343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_v_2344_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_l_2050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 4, v_l_2050_);
                    v___x_2355_ = v_reuseFailAlloc_2359_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_2342_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2341_, 4, v___x_2355_);
                    crate::leanh::lean_ctor_set(v___x_2341_, 3, v___x_2353_);
                    crate::leanh::lean_ctor_set(v___x_2341_, 2, v_v_2346_);
                    crate::leanh::lean_ctor_set(v___x_2341_, 1, v_k_2345_);
                    crate::leanh::lean_ctor_set(v___x_2341_, 0, v___x_2350_);
                    v___x_2357_ = v___x_2341_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_2345_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_2346_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 3, v___x_2353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 4, v___x_2355_);
                    v___x_2357_ = v_reuseFailAlloc_2358_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_2357_;
            }
            71 => {
                return v___x_2375_;
            }
            72 => {
                return v___x_2397_;
            }
            73 => {
                if crate::leanh::lean_obj_tag(v_l_2388_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_2389_) == 0 {
                        v_size_2402_ = crate::leanh::lean_ctor_get(v_l_2388_, 0);
                        v_size_2403_ = crate::leanh::lean_ctor_get(v_r_2389_, 0);
                        v_k_2404_ = crate::leanh::lean_ctor_get(v_r_2389_, 1);
                        v_v_2405_ = crate::leanh::lean_ctor_get(v_r_2389_, 2);
                        v_l_2406_ = crate::leanh::lean_ctor_get(v_r_2389_, 3);
                        v_r_2407_ = crate::leanh::lean_ctor_get(v_r_2389_, 4);
                        v___x_2408_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_2409_ = lean_nat_mul(v___x_2408_, v_size_2402_);
                        v___x_2410_ = lean_nat_dec_lt(v_size_2403_, v___x_2409_);
                        crate::leanh::lean_dec(v___x_2409_);
                        if v___x_2410_ == 0 {
                            crate::leanh::lean_inc(v_r_2407_);
                            crate::leanh::lean_inc(v_l_2406_);
                            crate::leanh::lean_inc(v_v_2405_);
                            crate::leanh::lean_inc(v_k_2404_);
                            v_isSharedCheck_2440_ =
                                (!crate::leanh::lean_is_exclusive(v_r_2389_)) as u8;
                            if v_isSharedCheck_2440_ == 0 {
                                v_unused_2441_ = crate::leanh::lean_ctor_get(v_r_2389_, 4);
                                crate::leanh::lean_dec(v_unused_2441_);
                                v_unused_2442_ = crate::leanh::lean_ctor_get(v_r_2389_, 3);
                                crate::leanh::lean_dec(v_unused_2442_);
                                v_unused_2443_ = crate::leanh::lean_ctor_get(v_r_2389_, 2);
                                crate::leanh::lean_dec(v_unused_2443_);
                                v_unused_2444_ = crate::leanh::lean_ctor_get(v_r_2389_, 1);
                                crate::leanh::lean_dec(v_unused_2444_);
                                v_unused_2445_ = crate::leanh::lean_ctor_get(v_r_2389_, 0);
                                crate::leanh::lean_dec(v_unused_2445_);
                                v___x_2412_ = v_r_2389_;
                                v_isShared_2413_ = v_isSharedCheck_2440_;
                                state = 74;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_r_2389_);
                                v___x_2412_ = crate::leanh::lean_box(0);
                                v_isShared_2413_ = v_isSharedCheck_2440_;
                                state = 74;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1871_);
                            v___x_2446_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_2447_ = lean_nat_add(v___x_2446_, v_size_2385_);
                            crate::leanh::lean_dec(v_size_2385_);
                            v___x_2448_ = lean_nat_add(v___x_2447_, v_size_2384_);
                            crate::leanh::lean_dec(v___x_2447_);
                            v___x_2449_ = lean_nat_add(v___x_2446_, v_size_2384_);
                            crate::leanh::lean_dec(v_size_2384_);
                            v___x_2450_ = lean_nat_add(v___x_2449_, v_size_2403_);
                            crate::leanh::lean_dec(v___x_2449_);
                            crate::leanh::lean_inc_ref(v___x_2383_);
                            if v_isShared_2401_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2400_, 4, v___x_2383_);
                                crate::leanh::lean_ctor_set(v___x_2400_, 3, v_r_2389_);
                                crate::leanh::lean_ctor_set(v___x_2400_, 2, v_v_1867_);
                                crate::leanh::lean_ctor_set(v___x_2400_, 1, v_k_1866_);
                                crate::leanh::lean_ctor_set(v___x_2400_, 0, v___x_2450_);
                                v___x_2452_ = v___x_2400_;
                                state = 80;
                                continue;
                            } else {
                                v_reuseFailAlloc_2465_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2450_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_k_1866_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_v_1867_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 3, v_r_2389_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 4, v___x_2383_);
                                v___x_2452_ = v_reuseFailAlloc_2465_;
                                state = 80;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_l_2388_, 5);
                        crate::leanh::lean_del_object(v___x_2400_);
                        crate::leanh::lean_dec(v_v_2387_);
                        crate::leanh::lean_dec(v_k_2386_);
                        crate::leanh::lean_dec(v_size_2385_);
                        crate::leanh::lean_dec(v_size_2384_);
                        crate::leanh::lean_dec_ref_known(v___x_2383_, 5);
                        crate::leanh::lean_del_object(v___x_1871_);
                        crate::leanh::lean_dec(v_v_1867_);
                        crate::leanh::lean_dec(v_k_1866_);
                        v___x_2466_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3);
                        v___x_2467_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2466_);
                        return v___x_2467_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2400_);
                    crate::leanh::lean_dec(v_r_2389_);
                    crate::leanh::lean_dec(v_v_2387_);
                    crate::leanh::lean_dec(v_k_2386_);
                    crate::leanh::lean_dec(v_size_2385_);
                    crate::leanh::lean_dec(v_size_2384_);
                    crate::leanh::lean_dec_ref_known(v___x_2383_, 5);
                    crate::leanh::lean_del_object(v___x_1871_);
                    crate::leanh::lean_dec(v_v_1867_);
                    crate::leanh::lean_dec(v_k_1866_);
                    v___x_2468_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4);
                    v___x_2469_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2468_);
                    return v___x_2469_;
                }
            }
            74 => {
                v___x_2414_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2415_ = lean_nat_add(v___x_2414_, v_size_2385_);
                crate::leanh::lean_dec(v_size_2385_);
                v___x_2416_ = lean_nat_add(v___x_2415_, v_size_2384_);
                crate::leanh::lean_dec(v___x_2415_);
                v___x_2428_ = lean_nat_add(v___x_2414_, v_size_2402_);
                if crate::leanh::lean_obj_tag(v_l_2406_) == 0 {
                    v_size_2438_ = crate::leanh::lean_ctor_get(v_l_2406_, 0);
                    crate::leanh::lean_inc(v_size_2438_);
                    v___y_2430_ = v_size_2438_;
                    state = 78;
                    continue;
                } else {
                    v___x_2439_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2430_ = v___x_2439_;
                    state = 78;
                    continue;
                }
            }
            75 => {
                v___x_2421_ = lean_nat_add(v___y_2418_, v___y_2420_);
                crate::leanh::lean_dec(v___y_2420_);
                crate::leanh::lean_dec(v___y_2418_);
                if v_isShared_2413_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2412_, 4, v___x_2383_);
                    crate::leanh::lean_ctor_set(v___x_2412_, 3, v_r_2407_);
                    crate::leanh::lean_ctor_set(v___x_2412_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v___x_2412_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v___x_2412_, 0, v___x_2421_);
                    v___x_2423_ = v___x_2412_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 3, v_r_2407_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 4, v___x_2383_);
                    v___x_2423_ = v_reuseFailAlloc_2427_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_2401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2400_, 4, v___x_2423_);
                    crate::leanh::lean_ctor_set(v___x_2400_, 3, v___y_2419_);
                    crate::leanh::lean_ctor_set(v___x_2400_, 2, v_v_2405_);
                    crate::leanh::lean_ctor_set(v___x_2400_, 1, v_k_2404_);
                    crate::leanh::lean_ctor_set(v___x_2400_, 0, v___x_2416_);
                    v___x_2425_ = v___x_2400_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_k_2404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_v_2405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 3, v___y_2419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 4, v___x_2423_);
                    v___x_2425_ = v_reuseFailAlloc_2426_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_2425_;
            }
            78 => {
                v___x_2431_ = lean_nat_add(v___x_2428_, v___y_2430_);
                crate::leanh::lean_dec(v___y_2430_);
                crate::leanh::lean_dec(v___x_2428_);
                if v_isShared_1872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v_l_2406_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v_l_2388_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 2, v_v_2387_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 1, v_k_2386_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2431_);
                    v___x_2433_ = v___x_1871_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_2437_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_k_2386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_v_2387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_l_2388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_l_2406_);
                    v___x_2433_ = v_reuseFailAlloc_2437_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_2434_ = lean_nat_add(v___x_2414_, v_size_2384_);
                crate::leanh::lean_dec(v_size_2384_);
                if crate::leanh::lean_obj_tag(v_r_2407_) == 0 {
                    v_size_2435_ = crate::leanh::lean_ctor_get(v_r_2407_, 0);
                    crate::leanh::lean_inc(v_size_2435_);
                    v___y_2418_ = v___x_2434_;
                    v___y_2419_ = v___x_2433_;
                    v___y_2420_ = v_size_2435_;
                    state = 75;
                    continue;
                } else {
                    v___x_2436_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_2418_ = v___x_2434_;
                    v___y_2419_ = v___x_2433_;
                    v___y_2420_ = v___x_2436_;
                    state = 75;
                    continue;
                }
            }
            80 => {
                v_isSharedCheck_2459_ = (!crate::leanh::lean_is_exclusive(v___x_2383_)) as u8;
                if v_isSharedCheck_2459_ == 0 {
                    v_unused_2460_ = crate::leanh::lean_ctor_get(v___x_2383_, 4);
                    crate::leanh::lean_dec(v_unused_2460_);
                    v_unused_2461_ = crate::leanh::lean_ctor_get(v___x_2383_, 3);
                    crate::leanh::lean_dec(v_unused_2461_);
                    v_unused_2462_ = crate::leanh::lean_ctor_get(v___x_2383_, 2);
                    crate::leanh::lean_dec(v_unused_2462_);
                    v_unused_2463_ = crate::leanh::lean_ctor_get(v___x_2383_, 1);
                    crate::leanh::lean_dec(v_unused_2463_);
                    v_unused_2464_ = crate::leanh::lean_ctor_get(v___x_2383_, 0);
                    crate::leanh::lean_dec(v_unused_2464_);
                    v___x_2454_ = v___x_2383_;
                    v_isShared_2455_ = v_isSharedCheck_2459_;
                    state = 81;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2383_);
                    v___x_2454_ = crate::leanh::lean_box(0);
                    v_isShared_2455_ = v_isSharedCheck_2459_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                if v_isShared_2455_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2454_, 4, v___x_2452_);
                    crate::leanh::lean_ctor_set(v___x_2454_, 3, v_l_2388_);
                    crate::leanh::lean_ctor_set(v___x_2454_, 2, v_v_2387_);
                    crate::leanh::lean_ctor_set(v___x_2454_, 1, v_k_2386_);
                    crate::leanh::lean_ctor_set(v___x_2454_, 0, v___x_2448_);
                    v___x_2457_ = v___x_2454_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_k_2386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 2, v_v_2387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 3, v_l_2388_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 4, v___x_2452_);
                    v___x_2457_ = v_reuseFailAlloc_2458_;
                    state = 82;
                    continue;
                }
            }
            82 => {
                return v___x_2457_;
            }
            83 => {
                return v___x_2480_;
            }
            84 => {
                v_size_2490_ = crate::leanh::lean_ctor_get(v_r_2483_, 0);
                v___x_2491_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2492_ = lean_nat_add(v___x_2491_, v_size_2484_);
                crate::leanh::lean_dec(v_size_2484_);
                v___x_2493_ = lean_nat_add(v___x_2491_, v_size_2490_);
                if v_isShared_2489_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2488_, 4, v___x_2383_);
                    crate::leanh::lean_ctor_set(v___x_2488_, 3, v_r_2483_);
                    crate::leanh::lean_ctor_set(v___x_2488_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v___x_2488_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v___x_2488_, 0, v___x_2493_);
                    v___x_2495_ = v___x_2488_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 3, v_r_2483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 4, v___x_2383_);
                    v___x_2495_ = v_reuseFailAlloc_2499_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_1872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v___x_2495_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v_l_2482_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 2, v_v_2486_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 1, v_k_2485_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2492_);
                    v___x_2497_ = v___x_1871_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_2498_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_k_2485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_v_2486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 3, v_l_2482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 4, v___x_2495_);
                    v___x_2497_ = v_reuseFailAlloc_2498_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_2497_;
            }
            87 => {
                v___x_2508_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2509_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2506_, 3, v_r_2483_);
                    crate::leanh::lean_ctor_set(v___x_2506_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v___x_2506_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v___x_2506_, 0, v___x_2509_);
                    v___x_2511_ = v___x_2506_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_2515_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_r_2483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_r_2483_);
                    v___x_2511_ = v_reuseFailAlloc_2515_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                if v_isShared_1872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v___x_2511_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v_l_2482_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 2, v_v_2504_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 1, v_k_2503_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2508_);
                    v___x_2513_ = v___x_1871_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_k_2503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_v_2504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_l_2482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 4, v___x_2511_);
                    v___x_2513_ = v_reuseFailAlloc_2514_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                return v___x_2513_;
            }
            90 => {
                v_k_2526_ = crate::leanh::lean_ctor_get(v_r_2520_, 1);
                v_v_2527_ = crate::leanh::lean_ctor_get(v_r_2520_, 2);
                v_isSharedCheck_2542_ = (!crate::leanh::lean_is_exclusive(v_r_2520_)) as u8;
                if v_isSharedCheck_2542_ == 0 {
                    v_unused_2543_ = crate::leanh::lean_ctor_get(v_r_2520_, 4);
                    crate::leanh::lean_dec(v_unused_2543_);
                    v_unused_2544_ = crate::leanh::lean_ctor_get(v_r_2520_, 3);
                    crate::leanh::lean_dec(v_unused_2544_);
                    v_unused_2545_ = crate::leanh::lean_ctor_get(v_r_2520_, 0);
                    crate::leanh::lean_dec(v_unused_2545_);
                    v___x_2529_ = v_r_2520_;
                    v_isShared_2530_ = v_isSharedCheck_2542_;
                    state = 91;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_2527_);
                    crate::leanh::lean_inc(v_k_2526_);
                    crate::leanh::lean_dec(v_r_2520_);
                    v___x_2529_ = crate::leanh::lean_box(0);
                    v_isShared_2530_ = v_isSharedCheck_2542_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                v___x_2531_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2532_ = crate::leanh::lean_unsigned_to_nat(1);
                if v_isShared_2530_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2529_, 4, v_l_2482_);
                    crate::leanh::lean_ctor_set(v___x_2529_, 3, v_l_2482_);
                    crate::leanh::lean_ctor_set(v___x_2529_, 2, v_v_2522_);
                    crate::leanh::lean_ctor_set(v___x_2529_, 1, v_k_2521_);
                    crate::leanh::lean_ctor_set(v___x_2529_, 0, v___x_2532_);
                    v___x_2534_ = v___x_2529_;
                    state = 92;
                    continue;
                } else {
                    v_reuseFailAlloc_2541_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_k_2521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_v_2522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_l_2482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 4, v_l_2482_);
                    v___x_2534_ = v_reuseFailAlloc_2541_;
                    state = 92;
                    continue;
                }
            }
            92 => {
                if v_isShared_2525_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2524_, 4, v_l_2482_);
                    crate::leanh::lean_ctor_set(v___x_2524_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v___x_2524_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v___x_2524_, 0, v___x_2532_);
                    v___x_2536_ = v___x_2524_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2532_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_k_1866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_v_1867_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 3, v_l_2482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 4, v_l_2482_);
                    v___x_2536_ = v_reuseFailAlloc_2540_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v_isShared_1872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1871_, 4, v___x_2536_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 3, v___x_2534_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 2, v_v_2527_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 1, v_k_2526_);
                    crate::leanh::lean_ctor_set(v___x_1871_, 0, v___x_2531_);
                    v___x_2538_ = v___x_1871_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_k_2526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_v_2527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 3, v___x_2534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 4, v___x_2536_);
                    v___x_2538_ = v_reuseFailAlloc_2539_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                return v___x_2538_;
            }
            95 => {
                return v___x_2552_;
            }
            96 => {
                return v___x_2556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg___boxed(
    mut v_k_2560_: *mut crate::leanh::LeanObject,
    mut v_t_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2562_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(
            v_k_2560_, v_t_2561_,
        );
    crate::leanh::lean_dec_ref(v_k_2560_);
    return v_res_2562_;
}
pub unsafe fn l_Lake_JsonObject_erase(
    mut v_obj_2563_: *mut crate::leanh::LeanObject,
    mut v_prop_2564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2565_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(
            v_prop_2564_,
            v_obj_2563_,
        );
    return v___x_2565_;
}
pub unsafe fn l_Lake_JsonObject_erase___boxed(
    mut v_obj_2566_: *mut crate::leanh::LeanObject,
    mut v_prop_2567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lake_JsonObject_erase(v_obj_2566_, v_prop_2567_);
    crate::leanh::lean_dec_ref(v_prop_2567_);
    return v_res_2568_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0(
    mut v_00_u03b2_2569_: *mut crate::leanh::LeanObject,
    mut v_k_2570_: *mut crate::leanh::LeanObject,
    mut v_t_2571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2572_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(
            v_k_2570_, v_t_2571_,
        );
    return v___x_2572_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___boxed(
    mut v_00_u03b2_2573_: *mut crate::leanh::LeanObject,
    mut v_k_2574_: *mut crate::leanh::LeanObject,
    mut v_t_2575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0(
        v_00_u03b2_2573_,
        v_k_2574_,
        v_t_2575_,
    );
    crate::leanh::lean_dec_ref(v_k_2574_);
    return v_res_2576_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(
    mut v_t_2577_: *mut crate::leanh::LeanObject,
    mut v_k_2578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2577_) == 0 {
                    v_k_2579_ = crate::leanh::lean_ctor_get(v_t_2577_, 1);
                    v_v_2580_ = crate::leanh::lean_ctor_get(v_t_2577_, 2);
                    v_l_2581_ = crate::leanh::lean_ctor_get(v_t_2577_, 3);
                    v_r_2582_ = crate::leanh::lean_ctor_get(v_t_2577_, 4);
                    v___x_2583_ = lean_string_compare(v_k_2578_, v_k_2579_);
                    match v___x_2583_ {
                        0 => {
                            v_t_2577_ = v_l_2581_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_2580_);
                            v___x_2585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2585_, 0, v_v_2580_);
                            return v___x_2585_;
                        }
                        _ => {
                            v_t_2577_ = v_r_2582_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2587_ = crate::leanh::lean_box(0);
                    return v___x_2587_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg___boxed(
    mut v_t_2588_: *mut crate::leanh::LeanObject,
    mut v_k_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_t_2588_, v_k_2589_);
    crate::leanh::lean_dec_ref(v_k_2589_);
    crate::leanh::lean_dec(v_t_2588_);
    return v_res_2590_;
}
pub unsafe fn l_Lake_JsonObject_getJson_x3f(
    mut v_obj_2591_: *mut crate::leanh::LeanObject,
    mut v_prop_2592_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2591_, v_prop_2592_);
    return v___x_2593_;
}
pub unsafe fn l_Lake_JsonObject_getJson_x3f___boxed(
    mut v_obj_2594_: *mut crate::leanh::LeanObject,
    mut v_prop_2595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2596_ = l_Lake_JsonObject_getJson_x3f(v_obj_2594_, v_prop_2595_);
    crate::leanh::lean_dec_ref(v_prop_2595_);
    crate::leanh::lean_dec(v_obj_2594_);
    return v_res_2596_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0(
    mut v_00_u03b4_2597_: *mut crate::leanh::LeanObject,
    mut v_t_2598_: *mut crate::leanh::LeanObject,
    mut v_k_2599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2600_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_t_2598_, v_k_2599_);
    return v___x_2600_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___boxed(
    mut v_00_u03b4_2601_: *mut crate::leanh::LeanObject,
    mut v_t_2602_: *mut crate::leanh::LeanObject,
    mut v_k_2603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2604_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0(
            v_00_u03b4_2601_,
            v_t_2602_,
            v_k_2603_,
        );
    crate::leanh::lean_dec_ref(v_k_2603_);
    crate::leanh::lean_dec(v_t_2602_);
    return v_res_2604_;
}
pub unsafe fn l_Lake_JsonObject_get___redArg(
    mut v_inst_2607_: *mut crate::leanh::LeanObject,
    mut v_obj_2608_: *mut crate::leanh::LeanObject,
    mut v_prop_2609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2610_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2608_, v_prop_2609_);
                if crate::leanh::lean_obj_tag(v___x_2610_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2607_);
                    v___x_2611_ = l_Lake_JsonObject_get___redArg___closed__0;
                    v___x_2612_ = lean_string_append(v___x_2611_, v_prop_2609_);
                    crate::leanh::lean_dec_ref(v_prop_2609_);
                    v___x_2613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2613_, 0, v___x_2612_);
                    return v___x_2613_;
                } else {
                    v_val_2614_ = crate::leanh::lean_ctor_get(v___x_2610_, 0);
                    crate::leanh::lean_inc(v_val_2614_);
                    crate::leanh::lean_dec_ref_known(v___x_2610_, 1);
                    v___x_2615_ = crate::leanh::lean_apply_1(v_inst_2607_, v_val_2614_);
                    if crate::leanh::lean_obj_tag(v___x_2615_) == 0 {
                        v_a_2616_ = crate::leanh::lean_ctor_get(v___x_2615_, 0);
                        v_isSharedCheck_2626_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2615_)) as u8;
                        if v_isSharedCheck_2626_ == 0 {
                            v___x_2618_ = v___x_2615_;
                            v_isShared_2619_ = v_isSharedCheck_2626_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2616_);
                            crate::leanh::lean_dec(v___x_2615_);
                            v___x_2618_ = crate::leanh::lean_box(0);
                            v_isShared_2619_ = v_isSharedCheck_2626_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_prop_2609_);
                        return v___x_2615_;
                    }
                }
            }
            1 => {
                v___x_2620_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2621_ = lean_string_append(v_prop_2609_, v___x_2620_);
                v___x_2622_ = lean_string_append(v___x_2621_, v_a_2616_);
                crate::leanh::lean_dec(v_a_2616_);
                if v_isShared_2619_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2618_, 0, v___x_2622_);
                    v___x_2624_ = v___x_2618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
                    v___x_2624_ = v_reuseFailAlloc_2625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JsonObject_get___redArg___boxed(
    mut v_inst_2627_: *mut crate::leanh::LeanObject,
    mut v_obj_2628_: *mut crate::leanh::LeanObject,
    mut v_prop_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2630_ = l_Lake_JsonObject_get___redArg(v_inst_2627_, v_obj_2628_, v_prop_2629_);
    crate::leanh::lean_dec(v_obj_2628_);
    return v_res_2630_;
}
pub unsafe fn l_Lake_JsonObject_get(
    mut v_00_u03b1_2631_: *mut crate::leanh::LeanObject,
    mut v_inst_2632_: *mut crate::leanh::LeanObject,
    mut v_obj_2633_: *mut crate::leanh::LeanObject,
    mut v_prop_2634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2644_: u8 = 0;
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2633_, v_prop_2634_);
                if crate::leanh::lean_obj_tag(v___x_2635_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2632_);
                    v___x_2636_ = l_Lake_JsonObject_get___redArg___closed__0;
                    v___x_2637_ = lean_string_append(v___x_2636_, v_prop_2634_);
                    crate::leanh::lean_dec_ref(v_prop_2634_);
                    v___x_2638_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2638_, 0, v___x_2637_);
                    return v___x_2638_;
                } else {
                    v_val_2639_ = crate::leanh::lean_ctor_get(v___x_2635_, 0);
                    crate::leanh::lean_inc(v_val_2639_);
                    crate::leanh::lean_dec_ref_known(v___x_2635_, 1);
                    v___x_2640_ = crate::leanh::lean_apply_1(v_inst_2632_, v_val_2639_);
                    if crate::leanh::lean_obj_tag(v___x_2640_) == 0 {
                        v_a_2641_ = crate::leanh::lean_ctor_get(v___x_2640_, 0);
                        v_isSharedCheck_2651_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2640_)) as u8;
                        if v_isSharedCheck_2651_ == 0 {
                            v___x_2643_ = v___x_2640_;
                            v_isShared_2644_ = v_isSharedCheck_2651_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2641_);
                            crate::leanh::lean_dec(v___x_2640_);
                            v___x_2643_ = crate::leanh::lean_box(0);
                            v_isShared_2644_ = v_isSharedCheck_2651_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_prop_2634_);
                        return v___x_2640_;
                    }
                }
            }
            1 => {
                v___x_2645_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2646_ = lean_string_append(v_prop_2634_, v___x_2645_);
                v___x_2647_ = lean_string_append(v___x_2646_, v_a_2641_);
                crate::leanh::lean_dec(v_a_2641_);
                if v_isShared_2644_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2643_, 0, v___x_2647_);
                    v___x_2649_ = v___x_2643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2650_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
                    v___x_2649_ = v_reuseFailAlloc_2650_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JsonObject_get___boxed(
    mut v_00_u03b1_2652_: *mut crate::leanh::LeanObject,
    mut v_inst_2653_: *mut crate::leanh::LeanObject,
    mut v_obj_2654_: *mut crate::leanh::LeanObject,
    mut v_prop_2655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_Lake_JsonObject_get(v_00_u03b1_2652_, v_inst_2653_, v_obj_2654_, v_prop_2655_);
    crate::leanh::lean_dec(v_obj_2654_);
    return v_res_2656_;
}
pub unsafe fn l_Lake_JsonObject_getAs___redArg(
    mut v_inst_2657_: *mut crate::leanh::LeanObject,
    mut v_obj_2658_: *mut crate::leanh::LeanObject,
    mut v_prop_2659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2660_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2658_, v_prop_2659_);
                if crate::leanh::lean_obj_tag(v___x_2660_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2657_);
                    v___x_2661_ = l_Lake_JsonObject_get___redArg___closed__0;
                    v___x_2662_ = lean_string_append(v___x_2661_, v_prop_2659_);
                    crate::leanh::lean_dec_ref(v_prop_2659_);
                    v___x_2663_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2663_, 0, v___x_2662_);
                    return v___x_2663_;
                } else {
                    v_val_2664_ = crate::leanh::lean_ctor_get(v___x_2660_, 0);
                    crate::leanh::lean_inc(v_val_2664_);
                    crate::leanh::lean_dec_ref_known(v___x_2660_, 1);
                    v___x_2665_ = crate::leanh::lean_apply_1(v_inst_2657_, v_val_2664_);
                    if crate::leanh::lean_obj_tag(v___x_2665_) == 0 {
                        v_a_2666_ = crate::leanh::lean_ctor_get(v___x_2665_, 0);
                        v_isSharedCheck_2676_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2665_)) as u8;
                        if v_isSharedCheck_2676_ == 0 {
                            v___x_2668_ = v___x_2665_;
                            v_isShared_2669_ = v_isSharedCheck_2676_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2666_);
                            crate::leanh::lean_dec(v___x_2665_);
                            v___x_2668_ = crate::leanh::lean_box(0);
                            v_isShared_2669_ = v_isSharedCheck_2676_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_prop_2659_);
                        return v___x_2665_;
                    }
                }
            }
            1 => {
                v___x_2670_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2671_ = lean_string_append(v_prop_2659_, v___x_2670_);
                v___x_2672_ = lean_string_append(v___x_2671_, v_a_2666_);
                crate::leanh::lean_dec(v_a_2666_);
                if v_isShared_2669_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2668_, 0, v___x_2672_);
                    v___x_2674_ = v___x_2668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2675_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
                    v___x_2674_ = v_reuseFailAlloc_2675_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2674_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JsonObject_getAs___redArg___boxed(
    mut v_inst_2677_: *mut crate::leanh::LeanObject,
    mut v_obj_2678_: *mut crate::leanh::LeanObject,
    mut v_prop_2679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2680_ = l_Lake_JsonObject_getAs___redArg(v_inst_2677_, v_obj_2678_, v_prop_2679_);
    crate::leanh::lean_dec(v_obj_2678_);
    return v_res_2680_;
}
pub unsafe fn l_Lake_JsonObject_getAs(
    mut v_00_u03b1_2681_: *mut crate::leanh::LeanObject,
    mut v_inst_2682_: *mut crate::leanh::LeanObject,
    mut v_obj_2683_: *mut crate::leanh::LeanObject,
    mut v_prop_2684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2694_: u8 = 0;
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2685_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2683_, v_prop_2684_);
                if crate::leanh::lean_obj_tag(v___x_2685_) == 0 {
                    crate::leanh::lean_dec_ref(v_inst_2682_);
                    v___x_2686_ = l_Lake_JsonObject_get___redArg___closed__0;
                    v___x_2687_ = lean_string_append(v___x_2686_, v_prop_2684_);
                    crate::leanh::lean_dec_ref(v_prop_2684_);
                    v___x_2688_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2688_, 0, v___x_2687_);
                    return v___x_2688_;
                } else {
                    v_val_2689_ = crate::leanh::lean_ctor_get(v___x_2685_, 0);
                    crate::leanh::lean_inc(v_val_2689_);
                    crate::leanh::lean_dec_ref_known(v___x_2685_, 1);
                    v___x_2690_ = crate::leanh::lean_apply_1(v_inst_2682_, v_val_2689_);
                    if crate::leanh::lean_obj_tag(v___x_2690_) == 0 {
                        v_a_2691_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
                        v_isSharedCheck_2701_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2690_)) as u8;
                        if v_isSharedCheck_2701_ == 0 {
                            v___x_2693_ = v___x_2690_;
                            v_isShared_2694_ = v_isSharedCheck_2701_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2691_);
                            crate::leanh::lean_dec(v___x_2690_);
                            v___x_2693_ = crate::leanh::lean_box(0);
                            v_isShared_2694_ = v_isSharedCheck_2701_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_prop_2684_);
                        return v___x_2690_;
                    }
                }
            }
            1 => {
                v___x_2695_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2696_ = lean_string_append(v_prop_2684_, v___x_2695_);
                v___x_2697_ = lean_string_append(v___x_2696_, v_a_2691_);
                crate::leanh::lean_dec(v_a_2691_);
                if v_isShared_2694_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2693_, 0, v___x_2697_);
                    v___x_2699_ = v___x_2693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
                    v___x_2699_ = v_reuseFailAlloc_2700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JsonObject_getAs___boxed(
    mut v_00_u03b1_2702_: *mut crate::leanh::LeanObject,
    mut v_inst_2703_: *mut crate::leanh::LeanObject,
    mut v_obj_2704_: *mut crate::leanh::LeanObject,
    mut v_prop_2705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2706_ =
        l_Lake_JsonObject_getAs(v_00_u03b1_2702_, v_inst_2703_, v_obj_2704_, v_prop_2705_);
    crate::leanh::lean_dec(v_obj_2704_);
    return v_res_2706_;
}
pub unsafe fn l_Lake_JsonObject_get_x3f___redArg(
    mut v_inst_2709_: *mut crate::leanh::LeanObject,
    mut v_obj_2710_: *mut crate::leanh::LeanObject,
    mut v_prop_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2712_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2710_, v_prop_2711_);
                if crate::leanh::lean_obj_tag(v___x_2712_) == 0 {
                    crate::leanh::lean_dec_ref(v_prop_2711_);
                    crate::leanh::lean_dec_ref(v_inst_2709_);
                    v___x_2713_ = l_Lake_JsonObject_get_x3f___redArg___closed__0;
                    return v___x_2713_;
                } else {
                    v_val_2714_ = crate::leanh::lean_ctor_get(v___x_2712_, 0);
                    crate::leanh::lean_inc(v_val_2714_);
                    crate::leanh::lean_dec_ref_known(v___x_2712_, 1);
                    v___x_2715_ = l_Option_fromJson_x3f___redArg(v_inst_2709_, v_val_2714_);
                    if crate::leanh::lean_obj_tag(v___x_2715_) == 0 {
                        v_a_2716_ = crate::leanh::lean_ctor_get(v___x_2715_, 0);
                        v_isSharedCheck_2726_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2715_)) as u8;
                        if v_isSharedCheck_2726_ == 0 {
                            v___x_2718_ = v___x_2715_;
                            v_isShared_2719_ = v_isSharedCheck_2726_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2716_);
                            crate::leanh::lean_dec(v___x_2715_);
                            v___x_2718_ = crate::leanh::lean_box(0);
                            v_isShared_2719_ = v_isSharedCheck_2726_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_prop_2711_);
                        return v___x_2715_;
                    }
                }
            }
            1 => {
                v___x_2720_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2721_ = lean_string_append(v_prop_2711_, v___x_2720_);
                v___x_2722_ = lean_string_append(v___x_2721_, v_a_2716_);
                crate::leanh::lean_dec(v_a_2716_);
                if v_isShared_2719_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2718_, 0, v___x_2722_);
                    v___x_2724_ = v___x_2718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
                    v___x_2724_ = v_reuseFailAlloc_2725_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JsonObject_get_x3f___redArg___boxed(
    mut v_inst_2727_: *mut crate::leanh::LeanObject,
    mut v_obj_2728_: *mut crate::leanh::LeanObject,
    mut v_prop_2729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2730_ = l_Lake_JsonObject_get_x3f___redArg(v_inst_2727_, v_obj_2728_, v_prop_2729_);
    crate::leanh::lean_dec(v_obj_2728_);
    return v_res_2730_;
}
pub unsafe fn l_Lake_JsonObject_get_x3f(
    mut v_00_u03b1_2731_: *mut crate::leanh::LeanObject,
    mut v_inst_2732_: *mut crate::leanh::LeanObject,
    mut v_obj_2733_: *mut crate::leanh::LeanObject,
    mut v_prop_2734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2735_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2733_, v_prop_2734_);
                if crate::leanh::lean_obj_tag(v___x_2735_) == 0 {
                    crate::leanh::lean_dec_ref(v_prop_2734_);
                    crate::leanh::lean_dec_ref(v_inst_2732_);
                    v___x_2736_ = l_Lake_JsonObject_get_x3f___redArg___closed__0;
                    return v___x_2736_;
                } else {
                    v_val_2737_ = crate::leanh::lean_ctor_get(v___x_2735_, 0);
                    crate::leanh::lean_inc(v_val_2737_);
                    crate::leanh::lean_dec_ref_known(v___x_2735_, 1);
                    v___x_2738_ = l_Option_fromJson_x3f___redArg(v_inst_2732_, v_val_2737_);
                    if crate::leanh::lean_obj_tag(v___x_2738_) == 0 {
                        v_a_2739_ = crate::leanh::lean_ctor_get(v___x_2738_, 0);
                        v_isSharedCheck_2749_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2738_)) as u8;
                        if v_isSharedCheck_2749_ == 0 {
                            v___x_2741_ = v___x_2738_;
                            v_isShared_2742_ = v_isSharedCheck_2749_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2739_);
                            crate::leanh::lean_dec(v___x_2738_);
                            v___x_2741_ = crate::leanh::lean_box(0);
                            v_isShared_2742_ = v_isSharedCheck_2749_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_prop_2734_);
                        return v___x_2738_;
                    }
                }
            }
            1 => {
                v___x_2743_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2744_ = lean_string_append(v_prop_2734_, v___x_2743_);
                v___x_2745_ = lean_string_append(v___x_2744_, v_a_2739_);
                crate::leanh::lean_dec(v_a_2739_);
                if v_isShared_2742_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2741_, 0, v___x_2745_);
                    v___x_2747_ = v___x_2741_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
                    v___x_2747_ = v_reuseFailAlloc_2748_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JsonObject_get_x3f___boxed(
    mut v_00_u03b1_2750_: *mut crate::leanh::LeanObject,
    mut v_inst_2751_: *mut crate::leanh::LeanObject,
    mut v_obj_2752_: *mut crate::leanh::LeanObject,
    mut v_prop_2753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2754_ =
        l_Lake_JsonObject_get_x3f(v_00_u03b1_2750_, v_inst_2751_, v_obj_2752_, v_prop_2753_);
    crate::leanh::lean_dec(v_obj_2752_);
    return v_res_2754_;
}
pub unsafe fn l_Lake_JsonObject_getAs_x3f___redArg(
    mut v_inst_2755_: *mut crate::leanh::LeanObject,
    mut v_obj_2756_: *mut crate::leanh::LeanObject,
    mut v_prop_2757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2765_: u8 = 0;
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2758_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2756_, v_prop_2757_);
                if crate::leanh::lean_obj_tag(v___x_2758_) == 0 {
                    crate::leanh::lean_dec_ref(v_prop_2757_);
                    crate::leanh::lean_dec_ref(v_inst_2755_);
                    v___x_2759_ = l_Lake_JsonObject_get_x3f___redArg___closed__0;
                    return v___x_2759_;
                } else {
                    v_val_2760_ = crate::leanh::lean_ctor_get(v___x_2758_, 0);
                    crate::leanh::lean_inc(v_val_2760_);
                    crate::leanh::lean_dec_ref_known(v___x_2758_, 1);
                    v___x_2761_ = l_Option_fromJson_x3f___redArg(v_inst_2755_, v_val_2760_);
                    if crate::leanh::lean_obj_tag(v___x_2761_) == 0 {
                        v_a_2762_ = crate::leanh::lean_ctor_get(v___x_2761_, 0);
                        v_isSharedCheck_2772_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2761_)) as u8;
                        if v_isSharedCheck_2772_ == 0 {
                            v___x_2764_ = v___x_2761_;
                            v_isShared_2765_ = v_isSharedCheck_2772_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2762_);
                            crate::leanh::lean_dec(v___x_2761_);
                            v___x_2764_ = crate::leanh::lean_box(0);
                            v_isShared_2765_ = v_isSharedCheck_2772_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_prop_2757_);
                        return v___x_2761_;
                    }
                }
            }
            1 => {
                v___x_2766_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2767_ = lean_string_append(v_prop_2757_, v___x_2766_);
                v___x_2768_ = lean_string_append(v___x_2767_, v_a_2762_);
                crate::leanh::lean_dec(v_a_2762_);
                if v_isShared_2765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2764_, 0, v___x_2768_);
                    v___x_2770_ = v___x_2764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
                    v___x_2770_ = v_reuseFailAlloc_2771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JsonObject_getAs_x3f___redArg___boxed(
    mut v_inst_2773_: *mut crate::leanh::LeanObject,
    mut v_obj_2774_: *mut crate::leanh::LeanObject,
    mut v_prop_2775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2776_ = l_Lake_JsonObject_getAs_x3f___redArg(v_inst_2773_, v_obj_2774_, v_prop_2775_);
    crate::leanh::lean_dec(v_obj_2774_);
    return v_res_2776_;
}
pub unsafe fn l_Lake_JsonObject_getAs_x3f(
    mut v_00_u03b1_2777_: *mut crate::leanh::LeanObject,
    mut v_inst_2778_: *mut crate::leanh::LeanObject,
    mut v_obj_2779_: *mut crate::leanh::LeanObject,
    mut v_prop_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2781_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2779_, v_prop_2780_);
                if crate::leanh::lean_obj_tag(v___x_2781_) == 0 {
                    crate::leanh::lean_dec_ref(v_prop_2780_);
                    crate::leanh::lean_dec_ref(v_inst_2778_);
                    v___x_2782_ = l_Lake_JsonObject_get_x3f___redArg___closed__0;
                    return v___x_2782_;
                } else {
                    v_val_2783_ = crate::leanh::lean_ctor_get(v___x_2781_, 0);
                    crate::leanh::lean_inc(v_val_2783_);
                    crate::leanh::lean_dec_ref_known(v___x_2781_, 1);
                    v___x_2784_ = l_Option_fromJson_x3f___redArg(v_inst_2778_, v_val_2783_);
                    if crate::leanh::lean_obj_tag(v___x_2784_) == 0 {
                        v_a_2785_ = crate::leanh::lean_ctor_get(v___x_2784_, 0);
                        v_isSharedCheck_2795_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2784_)) as u8;
                        if v_isSharedCheck_2795_ == 0 {
                            v___x_2787_ = v___x_2784_;
                            v_isShared_2788_ = v_isSharedCheck_2795_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2785_);
                            crate::leanh::lean_dec(v___x_2784_);
                            v___x_2787_ = crate::leanh::lean_box(0);
                            v_isShared_2788_ = v_isSharedCheck_2795_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_prop_2780_);
                        return v___x_2784_;
                    }
                }
            }
            1 => {
                v___x_2789_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2790_ = lean_string_append(v_prop_2780_, v___x_2789_);
                v___x_2791_ = lean_string_append(v___x_2790_, v_a_2785_);
                crate::leanh::lean_dec(v_a_2785_);
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2791_);
                    v___x_2793_ = v___x_2787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
                    v___x_2793_ = v_reuseFailAlloc_2794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_JsonObject_getAs_x3f___boxed(
    mut v_00_u03b1_2796_: *mut crate::leanh::LeanObject,
    mut v_inst_2797_: *mut crate::leanh::LeanObject,
    mut v_obj_2798_: *mut crate::leanh::LeanObject,
    mut v_prop_2799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2800_ =
        l_Lake_JsonObject_getAs_x3f(v_00_u03b1_2796_, v_inst_2797_, v_obj_2798_, v_prop_2799_);
    crate::leanh::lean_dec(v_obj_2798_);
    return v_res_2800_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_JsonObject(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lake_JsonObject_empty = _init_l_Lake_JsonObject_empty();
    crate::leanh::lean_mark_persistent(l_Lake_JsonObject_empty);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_JsonObject(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_JsonObject(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_JsonObject(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_JsonObject(builtin);
}
