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
pub static mut l_Lake_JsonObject_empty: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_JsonObject_instCoeJson___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_JsonObject_instCoeJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JsonObject_instCoeJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instCoeJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_JsonObject_instCoeJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instCoeJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_JsonObject_instToJson___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_JsonObject_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JsonObject_instToJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instToJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_JsonObject_instToJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instToJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_JsonObject_instFromJson___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lake_JsonObject_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JsonObject_instFromJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instFromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_JsonObject_instFromJson: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_instFromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_JsonObject_contains___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_String_compare___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_JsonObject_contains___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_contains___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 97, 116, 97, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 66, 97, 108, 97, 110, 99, 105, 110, 103, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__1_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 76, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 76, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__5_value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [83, 116, 100, 46, 68, 84, 114, 101, 101, 77, 97, 112, 46, 73, 110, 116, 101, 114, 110, 97, 108, 46, 73, 109, 112, 108, 46, 98, 97, 108, 97, 110, 99, 101, 82, 33, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [98, 97, 108, 97, 110, 99, 101, 82, 33, 32, 105, 110, 112, 117, 116, 32, 119, 97, 115, 32, 110, 111, 116, 32, 98, 97, 108, 97, 110, 99, 101, 100, 0]};
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_JsonObject_get___redArg___closed__0_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_JsonObject_get___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_get___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_JsonObject_get___redArg___closed__1_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lake_JsonObject_get___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_get___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_JsonObject_get_x3f___redArg___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lake_JsonObject_get_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_JsonObject_get_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_JsonObject_mk(
    mut v_val_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_val_1401_);
    return v_val_1401_;
}
pub unsafe fn l_Lake_JsonObject_mk___boxed(
    mut v_val_1402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Lake_JsonObject_mk(v_val_1402_);
    leanh::lean_dec(v_val_1402_);
    return v_res_1403_;
}
pub unsafe fn _init_l_Lake_JsonObject_empty() -> *mut leanh::LeanObject {
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1404_ = leanh::lean_box(1);
    return v___x_1404_;
}
pub unsafe fn l_Lake_JsonObject_toJson(
    mut v_obj_1405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1406_, 0, v_obj_1405_);
    return v___x_1406_;
}
pub unsafe fn l_Lake_JsonObject_instCoeJson___lam__0(
    mut v_kvPairs_1407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1408_ = leanh::lean_alloc_ctor(5, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1408_, 0, v_kvPairs_1407_);
    return v___x_1408_;
}
pub unsafe fn l_Lake_JsonObject_fromJson_x3f(
    mut v_json_1413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = l_Lean_Json_getObj_x3f(v_json_1413_);
    return v___x_1414_;
}
pub unsafe fn l_Lake_JsonObject_contains(
    mut v_obj_1418_: *mut leanh::LeanObject,
    mut v_prop_1419_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: u8 = 0;
    v___x_1420_ = l_Lake_JsonObject_contains___closed__0;
    v___x_1421_ =
        l_Std_DTreeMap_Internal_Impl_contains___redArg(v___x_1420_, v_prop_1419_, v_obj_1418_);
    return v___x_1421_;
}
pub unsafe fn l_Lake_JsonObject_contains___boxed(
    mut v_obj_1422_: *mut leanh::LeanObject,
    mut v_prop_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1424_: u8 = 0;
    let mut v_r_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1424_ = l_Lake_JsonObject_contains(v_obj_1422_, v_prop_1423_);
    v_r_1425_ = leanh::lean_box((v_res_1424_) as usize);
    return v_r_1425_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(
    mut v_msg_1426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1427_ = leanh::lean_box(1);
    v___x_1428_ = lean_panic_fn_borrowed(v___x_1427_, v_msg_1426_);
    return v___x_1428_;
}
pub unsafe fn _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2;
    v___x_1433_ = leanh::lean_unsigned_to_nat(35);
    v___x_1434_ = leanh::lean_unsigned_to_nat(182);
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
-> *mut leanh::LeanObject {
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1438_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__2;
    v___x_1439_ = leanh::lean_unsigned_to_nat(21);
    v___x_1440_ = leanh::lean_unsigned_to_nat(183);
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
-> *mut leanh::LeanObject {
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1446_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6;
    v___x_1447_ = leanh::lean_unsigned_to_nat(35);
    v___x_1448_ = leanh::lean_unsigned_to_nat(276);
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
-> *mut leanh::LeanObject {
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__6;
    v___x_1453_ = leanh::lean_unsigned_to_nat(21);
    v___x_1454_ = leanh::lean_unsigned_to_nat(277);
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
    mut v_k_1458_: *mut leanh::LeanObject,
    mut v_v_1459_: *mut leanh::LeanObject,
    mut v_t_1460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1468_: u8 = 0;
    let mut v___x_1469_: u8 = 0;
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: u8 = 0;
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1488_: u8 = 0;
    let mut v_size_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: u8 = 0;
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1500_: u8 = 0;
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1527_: u8 = 0;
    let mut v_unused_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1542_: u8 = 0;
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v_unused_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1557_: u8 = 0;
    let mut v_unused_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1576_: u8 = 0;
    let mut v_size_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1587_: u8 = 0;
    let mut v_unused_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1594_: u8 = 0;
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut v_unused_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1612_: u8 = 0;
    let mut v_k_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1617_: u8 = 0;
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1629_: u8 = 0;
    let mut v_unused_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1633_: u8 = 0;
    let mut v_unused_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1666_: u8 = 0;
    let mut v_size_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1704_: u8 = 0;
    let mut v_unused_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1722_: u8 = 0;
    let mut v_unused_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1733_: u8 = 0;
    let mut v_unused_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1752_: u8 = 0;
    let mut v_size_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1763_: u8 = 0;
    let mut v_unused_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1770_: u8 = 0;
    let mut v_k_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1775_: u8 = 0;
    let mut v___x_1776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1787_: u8 = 0;
    let mut v_unused_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut v_unused_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1800_: u8 = 0;
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1809_: u8 = 0;
    let mut v_unused_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1821_: u8 = 0;
    let mut v___x_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1460_) == 0 {
                    v_size_1461_ = leanh::lean_ctor_get(v_t_1460_, 0);
                    v_k_1462_ = leanh::lean_ctor_get(v_t_1460_, 1);
                    v_v_1463_ = leanh::lean_ctor_get(v_t_1460_, 2);
                    v_l_1464_ = leanh::lean_ctor_get(v_t_1460_, 3);
                    v_r_1465_ = leanh::lean_ctor_get(v_t_1460_, 4);
                    v_isSharedCheck_1821_ = (!leanh::lean_is_exclusive(v_t_1460_)) as u8;
                    if v_isSharedCheck_1821_ == 0 {
                        v___x_1467_ = v_t_1460_;
                        v_isShared_1468_ = v_isSharedCheck_1821_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1465_);
                        leanh::lean_inc(v_l_1464_);
                        leanh::lean_inc(v_v_1463_);
                        leanh::lean_inc(v_k_1462_);
                        leanh::lean_inc(v_size_1461_);
                        leanh::lean_dec(v_t_1460_);
                        v___x_1467_ = leanh::lean_box(0);
                        v_isShared_1468_ = v_isSharedCheck_1821_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1822_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1823_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v___x_1823_, 0, v___x_1822_);
                    leanh::lean_ctor_set(v___x_1823_, 1, v_k_1458_);
                    leanh::lean_ctor_set(v___x_1823_, 2, v_v_1459_);
                    leanh::lean_ctor_set(v___x_1823_, 3, v_t_1460_);
                    leanh::lean_ctor_set(v___x_1823_, 4, v_t_1460_);
                    return v___x_1823_;
                }
            }
            1 => {
                v___x_1469_ = lean_string_compare(v_k_1458_, v_k_1462_);
                match v___x_1469_ {
                    0 => {
                        leanh::lean_dec(v_size_1461_);
                        v___x_1470_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_k_1458_, v_v_1459_, v_l_1464_);
                        if leanh::lean_obj_tag(v_r_1465_) == 0 {
                            if leanh::lean_obj_tag(v___x_1470_) == 0 {
                                v_size_1471_ = leanh::lean_ctor_get(v_r_1465_, 0);
                                v_size_1472_ = leanh::lean_ctor_get(v___x_1470_, 0);
                                leanh::lean_inc(v_size_1472_);
                                v_k_1473_ = leanh::lean_ctor_get(v___x_1470_, 1);
                                leanh::lean_inc(v_k_1473_);
                                v_v_1474_ = leanh::lean_ctor_get(v___x_1470_, 2);
                                leanh::lean_inc(v_v_1474_);
                                v_l_1475_ = leanh::lean_ctor_get(v___x_1470_, 3);
                                leanh::lean_inc(v_l_1475_);
                                v_r_1476_ = leanh::lean_ctor_get(v___x_1470_, 4);
                                leanh::lean_inc(v_r_1476_);
                                v___x_1477_ = leanh::lean_unsigned_to_nat(3);
                                v___x_1478_ = lean_nat_mul(v___x_1477_, v_size_1471_);
                                v___x_1479_ = lean_nat_dec_lt(v___x_1478_, v_size_1472_);
                                leanh::lean_dec(v___x_1478_);
                                if v___x_1479_ == 0 {
                                    leanh::lean_dec(v_r_1476_);
                                    leanh::lean_dec(v_l_1475_);
                                    leanh::lean_dec(v_v_1474_);
                                    leanh::lean_dec(v_k_1473_);
                                    v___x_1480_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_1481_ = lean_nat_add(v___x_1480_, v_size_1472_);
                                    leanh::lean_dec(v_size_1472_);
                                    v___x_1482_ = lean_nat_add(v___x_1481_, v_size_1471_);
                                    leanh::lean_dec(v___x_1481_);
                                    if v_isShared_1468_ == 0 {
                                        leanh::lean_ctor_set(v___x_1467_, 3, v___x_1470_);
                                        leanh::lean_ctor_set(v___x_1467_, 0, v___x_1482_);
                                        v___x_1484_ = v___x_1467_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1485_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1485_,
                                            0,
                                            v___x_1482_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1485_,
                                            1,
                                            v_k_1462_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1485_,
                                            2,
                                            v_v_1463_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1485_,
                                            3,
                                            v___x_1470_,
                                        );
                                        leanh::lean_ctor_set(
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
                                        (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                                    if v_isSharedCheck_1557_ == 0 {
                                        v_unused_1558_ =
                                            leanh::lean_ctor_get(v___x_1470_, 4);
                                        leanh::lean_dec(v_unused_1558_);
                                        v_unused_1559_ =
                                            leanh::lean_ctor_get(v___x_1470_, 3);
                                        leanh::lean_dec(v_unused_1559_);
                                        v_unused_1560_ =
                                            leanh::lean_ctor_get(v___x_1470_, 2);
                                        leanh::lean_dec(v_unused_1560_);
                                        v_unused_1561_ =
                                            leanh::lean_ctor_get(v___x_1470_, 1);
                                        leanh::lean_dec(v_unused_1561_);
                                        v_unused_1562_ =
                                            leanh::lean_ctor_get(v___x_1470_, 0);
                                        leanh::lean_dec(v_unused_1562_);
                                        v___x_1487_ = v___x_1470_;
                                        v_isShared_1488_ = v_isSharedCheck_1557_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1470_);
                                        v___x_1487_ = leanh::lean_box(0);
                                        v_isShared_1488_ = v_isSharedCheck_1557_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1563_ = leanh::lean_ctor_get(v_r_1465_, 0);
                                v___x_1564_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1565_ = lean_nat_add(v___x_1564_, v_size_1563_);
                                if v_isShared_1468_ == 0 {
                                    leanh::lean_ctor_set(v___x_1467_, 3, v___x_1470_);
                                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1565_);
                                    v___x_1567_ = v___x_1467_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1568_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1568_,
                                        0,
                                        v___x_1565_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1568_,
                                        1,
                                        v_k_1462_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1568_,
                                        2,
                                        v_v_1463_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1568_,
                                        3,
                                        v___x_1470_,
                                    );
                                    leanh::lean_ctor_set(
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
                            if leanh::lean_obj_tag(v___x_1470_) == 0 {
                                v_l_1569_ = leanh::lean_ctor_get(v___x_1470_, 3);
                                leanh::lean_inc(v_l_1569_);
                                if leanh::lean_obj_tag(v_l_1569_) == 0 {
                                    v_r_1570_ = leanh::lean_ctor_get(v___x_1470_, 4);
                                    leanh::lean_inc(v_r_1570_);
                                    if leanh::lean_obj_tag(v_r_1570_) == 0 {
                                        v_size_1571_ = leanh::lean_ctor_get(v___x_1470_, 0);
                                        v_k_1572_ = leanh::lean_ctor_get(v___x_1470_, 1);
                                        v_v_1573_ = leanh::lean_ctor_get(v___x_1470_, 2);
                                        v_isSharedCheck_1587_ =
                                            (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                                        if v_isSharedCheck_1587_ == 0 {
                                            v_unused_1588_ =
                                                leanh::lean_ctor_get(v___x_1470_, 4);
                                            leanh::lean_dec(v_unused_1588_);
                                            v_unused_1589_ =
                                                leanh::lean_ctor_get(v___x_1470_, 3);
                                            leanh::lean_dec(v_unused_1589_);
                                            v___x_1575_ = v___x_1470_;
                                            v_isShared_1576_ = v_isSharedCheck_1587_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1573_);
                                            leanh::lean_inc(v_k_1572_);
                                            leanh::lean_inc(v_size_1571_);
                                            leanh::lean_dec(v___x_1470_);
                                            v___x_1575_ = leanh::lean_box(0);
                                            v_isShared_1576_ = v_isSharedCheck_1587_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1590_ = leanh::lean_ctor_get(v___x_1470_, 1);
                                        v_v_1591_ = leanh::lean_ctor_get(v___x_1470_, 2);
                                        v_isSharedCheck_1603_ =
                                            (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                                        if v_isSharedCheck_1603_ == 0 {
                                            v_unused_1604_ =
                                                leanh::lean_ctor_get(v___x_1470_, 4);
                                            leanh::lean_dec(v_unused_1604_);
                                            v_unused_1605_ =
                                                leanh::lean_ctor_get(v___x_1470_, 3);
                                            leanh::lean_dec(v_unused_1605_);
                                            v_unused_1606_ =
                                                leanh::lean_ctor_get(v___x_1470_, 0);
                                            leanh::lean_dec(v_unused_1606_);
                                            v___x_1593_ = v___x_1470_;
                                            v_isShared_1594_ = v_isSharedCheck_1603_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1591_);
                                            leanh::lean_inc(v_k_1590_);
                                            leanh::lean_dec(v___x_1470_);
                                            v___x_1593_ = leanh::lean_box(0);
                                            v_isShared_1594_ = v_isSharedCheck_1603_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1607_ = leanh::lean_ctor_get(v___x_1470_, 4);
                                    leanh::lean_inc(v_r_1607_);
                                    if leanh::lean_obj_tag(v_r_1607_) == 0 {
                                        v_k_1608_ = leanh::lean_ctor_get(v___x_1470_, 1);
                                        v_v_1609_ = leanh::lean_ctor_get(v___x_1470_, 2);
                                        v_isSharedCheck_1633_ =
                                            (!leanh::lean_is_exclusive(v___x_1470_)) as u8;
                                        if v_isSharedCheck_1633_ == 0 {
                                            v_unused_1634_ =
                                                leanh::lean_ctor_get(v___x_1470_, 4);
                                            leanh::lean_dec(v_unused_1634_);
                                            v_unused_1635_ =
                                                leanh::lean_ctor_get(v___x_1470_, 3);
                                            leanh::lean_dec(v_unused_1635_);
                                            v_unused_1636_ =
                                                leanh::lean_ctor_get(v___x_1470_, 0);
                                            leanh::lean_dec(v_unused_1636_);
                                            v___x_1611_ = v___x_1470_;
                                            v_isShared_1612_ = v_isSharedCheck_1633_;
                                            state = 20;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1609_);
                                            leanh::lean_inc(v_k_1608_);
                                            leanh::lean_dec(v___x_1470_);
                                            v___x_1611_ = leanh::lean_box(0);
                                            v_isShared_1612_ = v_isSharedCheck_1633_;
                                            state = 20;
                                            continue;
                                        }
                                    } else {
                                        v___x_1637_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1468_ == 0 {
                                            leanh::lean_ctor_set(v___x_1467_, 4, v_r_1607_);
                                            leanh::lean_ctor_set(
                                                v___x_1467_,
                                                3,
                                                v___x_1470_,
                                            );
                                            leanh::lean_ctor_set(
                                                v___x_1467_,
                                                0,
                                                v___x_1637_,
                                            );
                                            v___x_1639_ = v___x_1467_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1640_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1640_,
                                                0,
                                                v___x_1637_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1640_,
                                                1,
                                                v_k_1462_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1640_,
                                                2,
                                                v_v_1463_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1640_,
                                                3,
                                                v___x_1470_,
                                            );
                                            leanh::lean_ctor_set(
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
                                v___x_1641_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1468_ == 0 {
                                    leanh::lean_ctor_set(v___x_1467_, 4, v___x_1470_);
                                    leanh::lean_ctor_set(v___x_1467_, 3, v___x_1470_);
                                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1641_);
                                    v___x_1643_ = v___x_1467_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1644_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1644_,
                                        0,
                                        v___x_1641_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1644_,
                                        1,
                                        v_k_1462_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1644_,
                                        2,
                                        v_v_1463_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1644_,
                                        3,
                                        v___x_1470_,
                                    );
                                    leanh::lean_ctor_set(
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
                        leanh::lean_dec(v_v_1463_);
                        leanh::lean_dec(v_k_1462_);
                        if v_isShared_1468_ == 0 {
                            leanh::lean_ctor_set(v___x_1467_, 2, v_v_1459_);
                            leanh::lean_ctor_set(v___x_1467_, 1, v_k_1458_);
                            v___x_1646_ = v___x_1467_;
                            state = 27;
                            continue;
                        } else {
                            v_reuseFailAlloc_1647_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_size_1461_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_k_1458_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 2, v_v_1459_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 3, v_l_1464_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1647_, 4, v_r_1465_);
                            v___x_1646_ = v_reuseFailAlloc_1647_;
                            state = 27;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v_size_1461_);
                        v___x_1648_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_k_1458_, v_v_1459_, v_r_1465_);
                        if leanh::lean_obj_tag(v_l_1464_) == 0 {
                            if leanh::lean_obj_tag(v___x_1648_) == 0 {
                                v_size_1649_ = leanh::lean_ctor_get(v_l_1464_, 0);
                                v_size_1650_ = leanh::lean_ctor_get(v___x_1648_, 0);
                                leanh::lean_inc(v_size_1650_);
                                v_k_1651_ = leanh::lean_ctor_get(v___x_1648_, 1);
                                leanh::lean_inc(v_k_1651_);
                                v_v_1652_ = leanh::lean_ctor_get(v___x_1648_, 2);
                                leanh::lean_inc(v_v_1652_);
                                v_l_1653_ = leanh::lean_ctor_get(v___x_1648_, 3);
                                leanh::lean_inc(v_l_1653_);
                                v_r_1654_ = leanh::lean_ctor_get(v___x_1648_, 4);
                                leanh::lean_inc(v_r_1654_);
                                v___x_1655_ = leanh::lean_unsigned_to_nat(3);
                                v___x_1656_ = lean_nat_mul(v___x_1655_, v_size_1649_);
                                v___x_1657_ = lean_nat_dec_lt(v___x_1656_, v_size_1650_);
                                leanh::lean_dec(v___x_1656_);
                                if v___x_1657_ == 0 {
                                    leanh::lean_dec(v_r_1654_);
                                    leanh::lean_dec(v_l_1653_);
                                    leanh::lean_dec(v_v_1652_);
                                    leanh::lean_dec(v_k_1651_);
                                    v___x_1658_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_1659_ = lean_nat_add(v___x_1658_, v_size_1649_);
                                    v___x_1660_ = lean_nat_add(v___x_1659_, v_size_1650_);
                                    leanh::lean_dec(v_size_1650_);
                                    leanh::lean_dec(v___x_1659_);
                                    if v_isShared_1468_ == 0 {
                                        leanh::lean_ctor_set(v___x_1467_, 4, v___x_1648_);
                                        leanh::lean_ctor_set(v___x_1467_, 0, v___x_1660_);
                                        v___x_1662_ = v___x_1467_;
                                        state = 28;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1663_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1663_,
                                            0,
                                            v___x_1660_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1663_,
                                            1,
                                            v_k_1462_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1663_,
                                            2,
                                            v_v_1463_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1663_,
                                            3,
                                            v_l_1464_,
                                        );
                                        leanh::lean_ctor_set(
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
                                        (!leanh::lean_is_exclusive(v___x_1648_)) as u8;
                                    if v_isSharedCheck_1733_ == 0 {
                                        v_unused_1734_ =
                                            leanh::lean_ctor_get(v___x_1648_, 4);
                                        leanh::lean_dec(v_unused_1734_);
                                        v_unused_1735_ =
                                            leanh::lean_ctor_get(v___x_1648_, 3);
                                        leanh::lean_dec(v_unused_1735_);
                                        v_unused_1736_ =
                                            leanh::lean_ctor_get(v___x_1648_, 2);
                                        leanh::lean_dec(v_unused_1736_);
                                        v_unused_1737_ =
                                            leanh::lean_ctor_get(v___x_1648_, 1);
                                        leanh::lean_dec(v_unused_1737_);
                                        v_unused_1738_ =
                                            leanh::lean_ctor_get(v___x_1648_, 0);
                                        leanh::lean_dec(v_unused_1738_);
                                        v___x_1665_ = v___x_1648_;
                                        v_isShared_1666_ = v_isSharedCheck_1733_;
                                        state = 29;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v___x_1648_);
                                        v___x_1665_ = leanh::lean_box(0);
                                        v_isShared_1666_ = v_isSharedCheck_1733_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1739_ = leanh::lean_ctor_get(v_l_1464_, 0);
                                v___x_1740_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1741_ = lean_nat_add(v___x_1740_, v_size_1739_);
                                if v_isShared_1468_ == 0 {
                                    leanh::lean_ctor_set(v___x_1467_, 4, v___x_1648_);
                                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1741_);
                                    v___x_1743_ = v___x_1467_;
                                    state = 39;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1744_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1744_,
                                        0,
                                        v___x_1741_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1744_,
                                        1,
                                        v_k_1462_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1744_,
                                        2,
                                        v_v_1463_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1744_,
                                        3,
                                        v_l_1464_,
                                    );
                                    leanh::lean_ctor_set(
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
                            if leanh::lean_obj_tag(v___x_1648_) == 0 {
                                v_l_1745_ = leanh::lean_ctor_get(v___x_1648_, 3);
                                leanh::lean_inc(v_l_1745_);
                                if leanh::lean_obj_tag(v_l_1745_) == 0 {
                                    v_r_1746_ = leanh::lean_ctor_get(v___x_1648_, 4);
                                    leanh::lean_inc(v_r_1746_);
                                    if leanh::lean_obj_tag(v_r_1746_) == 0 {
                                        v_size_1747_ = leanh::lean_ctor_get(v___x_1648_, 0);
                                        v_k_1748_ = leanh::lean_ctor_get(v___x_1648_, 1);
                                        v_v_1749_ = leanh::lean_ctor_get(v___x_1648_, 2);
                                        v_isSharedCheck_1763_ =
                                            (!leanh::lean_is_exclusive(v___x_1648_)) as u8;
                                        if v_isSharedCheck_1763_ == 0 {
                                            v_unused_1764_ =
                                                leanh::lean_ctor_get(v___x_1648_, 4);
                                            leanh::lean_dec(v_unused_1764_);
                                            v_unused_1765_ =
                                                leanh::lean_ctor_get(v___x_1648_, 3);
                                            leanh::lean_dec(v_unused_1765_);
                                            v___x_1751_ = v___x_1648_;
                                            v_isShared_1752_ = v_isSharedCheck_1763_;
                                            state = 40;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1749_);
                                            leanh::lean_inc(v_k_1748_);
                                            leanh::lean_inc(v_size_1747_);
                                            leanh::lean_dec(v___x_1648_);
                                            v___x_1751_ = leanh::lean_box(0);
                                            v_isShared_1752_ = v_isSharedCheck_1763_;
                                            state = 40;
                                            continue;
                                        }
                                    } else {
                                        v_k_1766_ = leanh::lean_ctor_get(v___x_1648_, 1);
                                        v_v_1767_ = leanh::lean_ctor_get(v___x_1648_, 2);
                                        v_isSharedCheck_1791_ =
                                            (!leanh::lean_is_exclusive(v___x_1648_)) as u8;
                                        if v_isSharedCheck_1791_ == 0 {
                                            v_unused_1792_ =
                                                leanh::lean_ctor_get(v___x_1648_, 4);
                                            leanh::lean_dec(v_unused_1792_);
                                            v_unused_1793_ =
                                                leanh::lean_ctor_get(v___x_1648_, 3);
                                            leanh::lean_dec(v_unused_1793_);
                                            v_unused_1794_ =
                                                leanh::lean_ctor_get(v___x_1648_, 0);
                                            leanh::lean_dec(v_unused_1794_);
                                            v___x_1769_ = v___x_1648_;
                                            v_isShared_1770_ = v_isSharedCheck_1791_;
                                            state = 43;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1767_);
                                            leanh::lean_inc(v_k_1766_);
                                            leanh::lean_dec(v___x_1648_);
                                            v___x_1769_ = leanh::lean_box(0);
                                            v_isShared_1770_ = v_isSharedCheck_1791_;
                                            state = 43;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_1795_ = leanh::lean_ctor_get(v___x_1648_, 4);
                                    leanh::lean_inc(v_r_1795_);
                                    if leanh::lean_obj_tag(v_r_1795_) == 0 {
                                        v_k_1796_ = leanh::lean_ctor_get(v___x_1648_, 1);
                                        v_v_1797_ = leanh::lean_ctor_get(v___x_1648_, 2);
                                        v_isSharedCheck_1809_ =
                                            (!leanh::lean_is_exclusive(v___x_1648_)) as u8;
                                        if v_isSharedCheck_1809_ == 0 {
                                            v_unused_1810_ =
                                                leanh::lean_ctor_get(v___x_1648_, 4);
                                            leanh::lean_dec(v_unused_1810_);
                                            v_unused_1811_ =
                                                leanh::lean_ctor_get(v___x_1648_, 3);
                                            leanh::lean_dec(v_unused_1811_);
                                            v_unused_1812_ =
                                                leanh::lean_ctor_get(v___x_1648_, 0);
                                            leanh::lean_dec(v_unused_1812_);
                                            v___x_1799_ = v___x_1648_;
                                            v_isShared_1800_ = v_isSharedCheck_1809_;
                                            state = 48;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1797_);
                                            leanh::lean_inc(v_k_1796_);
                                            leanh::lean_dec(v___x_1648_);
                                            v___x_1799_ = leanh::lean_box(0);
                                            v_isShared_1800_ = v_isSharedCheck_1809_;
                                            state = 48;
                                            continue;
                                        }
                                    } else {
                                        v___x_1813_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1468_ == 0 {
                                            leanh::lean_ctor_set(
                                                v___x_1467_,
                                                4,
                                                v___x_1648_,
                                            );
                                            leanh::lean_ctor_set(v___x_1467_, 3, v_r_1795_);
                                            leanh::lean_ctor_set(
                                                v___x_1467_,
                                                0,
                                                v___x_1813_,
                                            );
                                            v___x_1815_ = v___x_1467_;
                                            state = 51;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_1816_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1816_,
                                                0,
                                                v___x_1813_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1816_,
                                                1,
                                                v_k_1462_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1816_,
                                                2,
                                                v_v_1463_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_1816_,
                                                3,
                                                v_r_1795_,
                                            );
                                            leanh::lean_ctor_set(
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
                                v___x_1817_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1468_ == 0 {
                                    leanh::lean_ctor_set(v___x_1467_, 4, v___x_1648_);
                                    leanh::lean_ctor_set(v___x_1467_, 3, v___x_1648_);
                                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1817_);
                                    v___x_1819_ = v___x_1467_;
                                    state = 52;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1820_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1820_,
                                        0,
                                        v___x_1817_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1820_,
                                        1,
                                        v_k_1462_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1820_,
                                        2,
                                        v_v_1463_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1820_,
                                        3,
                                        v___x_1648_,
                                    );
                                    leanh::lean_ctor_set(
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
                if leanh::lean_obj_tag(v_l_1475_) == 0 {
                    if leanh::lean_obj_tag(v_r_1476_) == 0 {
                        v_size_1489_ = leanh::lean_ctor_get(v_l_1475_, 0);
                        v_size_1490_ = leanh::lean_ctor_get(v_r_1476_, 0);
                        v_k_1491_ = leanh::lean_ctor_get(v_r_1476_, 1);
                        v_v_1492_ = leanh::lean_ctor_get(v_r_1476_, 2);
                        v_l_1493_ = leanh::lean_ctor_get(v_r_1476_, 3);
                        v_r_1494_ = leanh::lean_ctor_get(v_r_1476_, 4);
                        v___x_1495_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1496_ = lean_nat_mul(v___x_1495_, v_size_1489_);
                        v___x_1497_ = lean_nat_dec_lt(v_size_1490_, v___x_1496_);
                        leanh::lean_dec(v___x_1496_);
                        if v___x_1497_ == 0 {
                            leanh::lean_inc(v_r_1494_);
                            leanh::lean_inc(v_l_1493_);
                            leanh::lean_inc(v_v_1492_);
                            leanh::lean_inc(v_k_1491_);
                            v_isSharedCheck_1527_ =
                                (!leanh::lean_is_exclusive(v_r_1476_)) as u8;
                            if v_isSharedCheck_1527_ == 0 {
                                v_unused_1528_ = leanh::lean_ctor_get(v_r_1476_, 4);
                                leanh::lean_dec(v_unused_1528_);
                                v_unused_1529_ = leanh::lean_ctor_get(v_r_1476_, 3);
                                leanh::lean_dec(v_unused_1529_);
                                v_unused_1530_ = leanh::lean_ctor_get(v_r_1476_, 2);
                                leanh::lean_dec(v_unused_1530_);
                                v_unused_1531_ = leanh::lean_ctor_get(v_r_1476_, 1);
                                leanh::lean_dec(v_unused_1531_);
                                v_unused_1532_ = leanh::lean_ctor_get(v_r_1476_, 0);
                                leanh::lean_dec(v_unused_1532_);
                                v___x_1499_ = v_r_1476_;
                                v_isShared_1500_ = v_isSharedCheck_1527_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v_r_1476_);
                                v___x_1499_ = leanh::lean_box(0);
                                v_isShared_1500_ = v_isSharedCheck_1527_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1467_);
                            v___x_1533_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1534_ = lean_nat_add(v___x_1533_, v_size_1472_);
                            leanh::lean_dec(v_size_1472_);
                            v___x_1535_ = lean_nat_add(v___x_1534_, v_size_1471_);
                            leanh::lean_dec(v___x_1534_);
                            v___x_1536_ = lean_nat_add(v___x_1533_, v_size_1471_);
                            v___x_1537_ = lean_nat_add(v___x_1536_, v_size_1490_);
                            leanh::lean_dec(v___x_1536_);
                            leanh::lean_inc_ref(v_r_1465_);
                            if v_isShared_1488_ == 0 {
                                leanh::lean_ctor_set(v___x_1487_, 4, v_r_1465_);
                                leanh::lean_ctor_set(v___x_1487_, 3, v_r_1476_);
                                leanh::lean_ctor_set(v___x_1487_, 2, v_v_1463_);
                                leanh::lean_ctor_set(v___x_1487_, 1, v_k_1462_);
                                leanh::lean_ctor_set(v___x_1487_, 0, v___x_1537_);
                                v___x_1539_ = v___x_1487_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1552_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1537_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_k_1462_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 2, v_v_1463_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 3, v_r_1476_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1552_, 4, v_r_1465_);
                                v___x_1539_ = v_reuseFailAlloc_1552_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_1475_, 5);
                        leanh::lean_del_object(v___x_1487_);
                        leanh::lean_dec(v_v_1474_);
                        leanh::lean_dec(v_k_1473_);
                        leanh::lean_dec(v_size_1472_);
                        leanh::lean_dec_ref_known(v_r_1465_, 5);
                        leanh::lean_del_object(v___x_1467_);
                        leanh::lean_dec(v_v_1463_);
                        leanh::lean_dec(v_k_1462_);
                        v___x_1553_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3);
                        v___x_1554_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1553_);
                        return v___x_1554_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1487_);
                    leanh::lean_dec(v_r_1476_);
                    leanh::lean_dec(v_v_1474_);
                    leanh::lean_dec(v_k_1473_);
                    leanh::lean_dec(v_size_1472_);
                    leanh::lean_dec_ref_known(v_r_1465_, 5);
                    leanh::lean_del_object(v___x_1467_);
                    leanh::lean_dec(v_v_1463_);
                    leanh::lean_dec(v_k_1462_);
                    v___x_1555_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4);
                    v___x_1556_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1555_);
                    return v___x_1556_;
                }
            }
            4 => {
                v___x_1501_ = leanh::lean_unsigned_to_nat(1);
                v___x_1502_ = lean_nat_add(v___x_1501_, v_size_1472_);
                leanh::lean_dec(v_size_1472_);
                v___x_1503_ = lean_nat_add(v___x_1502_, v_size_1471_);
                leanh::lean_dec(v___x_1502_);
                v___x_1515_ = lean_nat_add(v___x_1501_, v_size_1489_);
                if leanh::lean_obj_tag(v_l_1493_) == 0 {
                    v_size_1525_ = leanh::lean_ctor_get(v_l_1493_, 0);
                    leanh::lean_inc(v_size_1525_);
                    v___y_1517_ = v_size_1525_;
                    state = 8;
                    continue;
                } else {
                    v___x_1526_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1517_ = v___x_1526_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1508_ = lean_nat_add(v___y_1505_, v___y_1507_);
                leanh::lean_dec(v___y_1507_);
                leanh::lean_dec(v___y_1505_);
                if v_isShared_1500_ == 0 {
                    leanh::lean_ctor_set(v___x_1499_, 4, v_r_1465_);
                    leanh::lean_ctor_set(v___x_1499_, 3, v_r_1494_);
                    leanh::lean_ctor_set(v___x_1499_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v___x_1499_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v___x_1499_, 0, v___x_1508_);
                    v___x_1510_ = v___x_1499_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1514_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 0, v___x_1508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 3, v_r_1494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1514_, 4, v_r_1465_);
                    v___x_1510_ = v_reuseFailAlloc_1514_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1488_ == 0 {
                    leanh::lean_ctor_set(v___x_1487_, 4, v___x_1510_);
                    leanh::lean_ctor_set(v___x_1487_, 3, v___y_1506_);
                    leanh::lean_ctor_set(v___x_1487_, 2, v_v_1492_);
                    leanh::lean_ctor_set(v___x_1487_, 1, v_k_1491_);
                    leanh::lean_ctor_set(v___x_1487_, 0, v___x_1503_);
                    v___x_1512_ = v___x_1487_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1513_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 0, v___x_1503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 1, v_k_1491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 2, v_v_1492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 3, v___y_1506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1513_, 4, v___x_1510_);
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
                leanh::lean_dec(v___y_1517_);
                leanh::lean_dec(v___x_1515_);
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set(v___x_1467_, 4, v_l_1493_);
                    leanh::lean_ctor_set(v___x_1467_, 3, v_l_1475_);
                    leanh::lean_ctor_set(v___x_1467_, 2, v_v_1474_);
                    leanh::lean_ctor_set(v___x_1467_, 1, v_k_1473_);
                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1518_);
                    v___x_1520_ = v___x_1467_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1518_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v_k_1473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 2, v_v_1474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 3, v_l_1475_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 4, v_l_1493_);
                    v___x_1520_ = v_reuseFailAlloc_1524_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1521_ = lean_nat_add(v___x_1501_, v_size_1471_);
                if leanh::lean_obj_tag(v_r_1494_) == 0 {
                    v_size_1522_ = leanh::lean_ctor_get(v_r_1494_, 0);
                    leanh::lean_inc(v_size_1522_);
                    v___y_1505_ = v___x_1521_;
                    v___y_1506_ = v___x_1520_;
                    v___y_1507_ = v_size_1522_;
                    state = 5;
                    continue;
                } else {
                    v___x_1523_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1505_ = v___x_1521_;
                    v___y_1506_ = v___x_1520_;
                    v___y_1507_ = v___x_1523_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1546_ = (!leanh::lean_is_exclusive(v_r_1465_)) as u8;
                if v_isSharedCheck_1546_ == 0 {
                    v_unused_1547_ = leanh::lean_ctor_get(v_r_1465_, 4);
                    leanh::lean_dec(v_unused_1547_);
                    v_unused_1548_ = leanh::lean_ctor_get(v_r_1465_, 3);
                    leanh::lean_dec(v_unused_1548_);
                    v_unused_1549_ = leanh::lean_ctor_get(v_r_1465_, 2);
                    leanh::lean_dec(v_unused_1549_);
                    v_unused_1550_ = leanh::lean_ctor_get(v_r_1465_, 1);
                    leanh::lean_dec(v_unused_1550_);
                    v_unused_1551_ = leanh::lean_ctor_get(v_r_1465_, 0);
                    leanh::lean_dec(v_unused_1551_);
                    v___x_1541_ = v_r_1465_;
                    v_isShared_1542_ = v_isSharedCheck_1546_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v_r_1465_);
                    v___x_1541_ = leanh::lean_box(0);
                    v_isShared_1542_ = v_isSharedCheck_1546_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1542_ == 0 {
                    leanh::lean_ctor_set(v___x_1541_, 4, v___x_1539_);
                    leanh::lean_ctor_set(v___x_1541_, 3, v_l_1475_);
                    leanh::lean_ctor_set(v___x_1541_, 2, v_v_1474_);
                    leanh::lean_ctor_set(v___x_1541_, 1, v_k_1473_);
                    leanh::lean_ctor_set(v___x_1541_, 0, v___x_1535_);
                    v___x_1544_ = v___x_1541_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1545_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1535_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_k_1473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_v_1474_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_l_1475_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1545_, 4, v___x_1539_);
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
                v_size_1577_ = leanh::lean_ctor_get(v_r_1570_, 0);
                v___x_1578_ = leanh::lean_unsigned_to_nat(1);
                v___x_1579_ = lean_nat_add(v___x_1578_, v_size_1571_);
                leanh::lean_dec(v_size_1571_);
                v___x_1580_ = lean_nat_add(v___x_1578_, v_size_1577_);
                if v_isShared_1576_ == 0 {
                    leanh::lean_ctor_set(v___x_1575_, 4, v_r_1465_);
                    leanh::lean_ctor_set(v___x_1575_, 3, v_r_1570_);
                    leanh::lean_ctor_set(v___x_1575_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v___x_1575_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v___x_1575_, 0, v___x_1580_);
                    v___x_1582_ = v___x_1575_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1586_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1580_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 3, v_r_1570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1586_, 4, v_r_1465_);
                    v___x_1582_ = v_reuseFailAlloc_1586_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set(v___x_1467_, 4, v___x_1582_);
                    leanh::lean_ctor_set(v___x_1467_, 3, v_l_1569_);
                    leanh::lean_ctor_set(v___x_1467_, 2, v_v_1573_);
                    leanh::lean_ctor_set(v___x_1467_, 1, v_k_1572_);
                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1579_);
                    v___x_1584_ = v___x_1467_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1585_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 1, v_k_1572_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_v_1573_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 3, v_l_1569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1585_, 4, v___x_1582_);
                    v___x_1584_ = v_reuseFailAlloc_1585_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1584_;
            }
            17 => {
                v___x_1595_ = leanh::lean_unsigned_to_nat(3);
                v___x_1596_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_1594_ == 0 {
                    leanh::lean_ctor_set(v___x_1593_, 3, v_r_1570_);
                    leanh::lean_ctor_set(v___x_1593_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v___x_1593_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v___x_1593_, 0, v___x_1596_);
                    v___x_1598_ = v___x_1593_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1596_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 3, v_r_1570_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 4, v_r_1570_);
                    v___x_1598_ = v_reuseFailAlloc_1602_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set(v___x_1467_, 4, v___x_1598_);
                    leanh::lean_ctor_set(v___x_1467_, 3, v_l_1569_);
                    leanh::lean_ctor_set(v___x_1467_, 2, v_v_1591_);
                    leanh::lean_ctor_set(v___x_1467_, 1, v_k_1590_);
                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1595_);
                    v___x_1600_ = v___x_1467_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1601_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1595_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 1, v_k_1590_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 2, v_v_1591_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 3, v_l_1569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1601_, 4, v___x_1598_);
                    v___x_1600_ = v_reuseFailAlloc_1601_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1600_;
            }
            20 => {
                v_k_1613_ = leanh::lean_ctor_get(v_r_1607_, 1);
                v_v_1614_ = leanh::lean_ctor_get(v_r_1607_, 2);
                v_isSharedCheck_1629_ = (!leanh::lean_is_exclusive(v_r_1607_)) as u8;
                if v_isSharedCheck_1629_ == 0 {
                    v_unused_1630_ = leanh::lean_ctor_get(v_r_1607_, 4);
                    leanh::lean_dec(v_unused_1630_);
                    v_unused_1631_ = leanh::lean_ctor_get(v_r_1607_, 3);
                    leanh::lean_dec(v_unused_1631_);
                    v_unused_1632_ = leanh::lean_ctor_get(v_r_1607_, 0);
                    leanh::lean_dec(v_unused_1632_);
                    v___x_1616_ = v_r_1607_;
                    v_isShared_1617_ = v_isSharedCheck_1629_;
                    state = 21;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1614_);
                    leanh::lean_inc(v_k_1613_);
                    leanh::lean_dec(v_r_1607_);
                    v___x_1616_ = leanh::lean_box(0);
                    v_isShared_1617_ = v_isSharedCheck_1629_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_1618_ = leanh::lean_unsigned_to_nat(3);
                v___x_1619_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_1617_ == 0 {
                    leanh::lean_ctor_set(v___x_1616_, 4, v_l_1569_);
                    leanh::lean_ctor_set(v___x_1616_, 3, v_l_1569_);
                    leanh::lean_ctor_set(v___x_1616_, 2, v_v_1609_);
                    leanh::lean_ctor_set(v___x_1616_, 1, v_k_1608_);
                    leanh::lean_ctor_set(v___x_1616_, 0, v___x_1619_);
                    v___x_1621_ = v___x_1616_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1628_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_k_1608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 2, v_v_1609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 3, v_l_1569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1628_, 4, v_l_1569_);
                    v___x_1621_ = v_reuseFailAlloc_1628_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_1612_ == 0 {
                    leanh::lean_ctor_set(v___x_1611_, 4, v_l_1569_);
                    leanh::lean_ctor_set(v___x_1611_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v___x_1611_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v___x_1611_, 0, v___x_1619_);
                    v___x_1623_ = v___x_1611_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_1627_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 0, v___x_1619_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 3, v_l_1569_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1627_, 4, v_l_1569_);
                    v___x_1623_ = v_reuseFailAlloc_1627_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set(v___x_1467_, 4, v___x_1623_);
                    leanh::lean_ctor_set(v___x_1467_, 3, v___x_1621_);
                    leanh::lean_ctor_set(v___x_1467_, 2, v_v_1614_);
                    leanh::lean_ctor_set(v___x_1467_, 1, v_k_1613_);
                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1618_);
                    v___x_1625_ = v___x_1467_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1618_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_k_1613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 2, v_v_1614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 3, v___x_1621_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 4, v___x_1623_);
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
                if leanh::lean_obj_tag(v_l_1653_) == 0 {
                    if leanh::lean_obj_tag(v_r_1654_) == 0 {
                        v_size_1667_ = leanh::lean_ctor_get(v_l_1653_, 0);
                        v_k_1668_ = leanh::lean_ctor_get(v_l_1653_, 1);
                        v_v_1669_ = leanh::lean_ctor_get(v_l_1653_, 2);
                        v_l_1670_ = leanh::lean_ctor_get(v_l_1653_, 3);
                        v_r_1671_ = leanh::lean_ctor_get(v_l_1653_, 4);
                        v_size_1672_ = leanh::lean_ctor_get(v_r_1654_, 0);
                        v___x_1673_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1674_ = lean_nat_mul(v___x_1673_, v_size_1672_);
                        v___x_1675_ = lean_nat_dec_lt(v_size_1667_, v___x_1674_);
                        leanh::lean_dec(v___x_1674_);
                        if v___x_1675_ == 0 {
                            leanh::lean_inc(v_r_1671_);
                            leanh::lean_inc(v_l_1670_);
                            leanh::lean_inc(v_v_1669_);
                            leanh::lean_inc(v_k_1668_);
                            v_isSharedCheck_1704_ =
                                (!leanh::lean_is_exclusive(v_l_1653_)) as u8;
                            if v_isSharedCheck_1704_ == 0 {
                                v_unused_1705_ = leanh::lean_ctor_get(v_l_1653_, 4);
                                leanh::lean_dec(v_unused_1705_);
                                v_unused_1706_ = leanh::lean_ctor_get(v_l_1653_, 3);
                                leanh::lean_dec(v_unused_1706_);
                                v_unused_1707_ = leanh::lean_ctor_get(v_l_1653_, 2);
                                leanh::lean_dec(v_unused_1707_);
                                v_unused_1708_ = leanh::lean_ctor_get(v_l_1653_, 1);
                                leanh::lean_dec(v_unused_1708_);
                                v_unused_1709_ = leanh::lean_ctor_get(v_l_1653_, 0);
                                leanh::lean_dec(v_unused_1709_);
                                v___x_1677_ = v_l_1653_;
                                v_isShared_1678_ = v_isSharedCheck_1704_;
                                state = 30;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_1653_);
                                v___x_1677_ = leanh::lean_box(0);
                                v_isShared_1678_ = v_isSharedCheck_1704_;
                                state = 30;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1467_);
                            v___x_1710_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1711_ = lean_nat_add(v___x_1710_, v_size_1649_);
                            v___x_1712_ = lean_nat_add(v___x_1711_, v_size_1650_);
                            leanh::lean_dec(v_size_1650_);
                            v___x_1713_ = lean_nat_add(v___x_1711_, v_size_1667_);
                            leanh::lean_dec(v___x_1711_);
                            leanh::lean_inc_ref(v_l_1464_);
                            if v_isShared_1666_ == 0 {
                                leanh::lean_ctor_set(v___x_1665_, 4, v_l_1653_);
                                leanh::lean_ctor_set(v___x_1665_, 3, v_l_1464_);
                                leanh::lean_ctor_set(v___x_1665_, 2, v_v_1463_);
                                leanh::lean_ctor_set(v___x_1665_, 1, v_k_1462_);
                                leanh::lean_ctor_set(v___x_1665_, 0, v___x_1713_);
                                v___x_1715_ = v___x_1665_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_1728_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1713_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_k_1462_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_v_1463_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 3, v_l_1464_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 4, v_l_1653_);
                                v___x_1715_ = v_reuseFailAlloc_1728_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_1653_, 5);
                        leanh::lean_del_object(v___x_1665_);
                        leanh::lean_dec(v_v_1652_);
                        leanh::lean_dec(v_k_1651_);
                        leanh::lean_dec(v_size_1650_);
                        leanh::lean_dec_ref_known(v_l_1464_, 5);
                        leanh::lean_del_object(v___x_1467_);
                        leanh::lean_dec(v_v_1463_);
                        leanh::lean_dec(v_k_1462_);
                        v___x_1729_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7);
                        v___x_1730_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1729_);
                        return v___x_1730_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1665_);
                    leanh::lean_dec(v_r_1654_);
                    leanh::lean_dec(v_v_1652_);
                    leanh::lean_dec(v_k_1651_);
                    leanh::lean_dec(v_size_1650_);
                    leanh::lean_dec_ref_known(v_l_1464_, 5);
                    leanh::lean_del_object(v___x_1467_);
                    leanh::lean_dec(v_v_1463_);
                    leanh::lean_dec(v_k_1462_);
                    v___x_1731_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8);
                    v___x_1732_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1731_);
                    return v___x_1732_;
                }
            }
            30 => {
                v___x_1679_ = leanh::lean_unsigned_to_nat(1);
                v___x_1680_ = lean_nat_add(v___x_1679_, v_size_1649_);
                v___x_1681_ = lean_nat_add(v___x_1680_, v_size_1650_);
                leanh::lean_dec(v_size_1650_);
                if leanh::lean_obj_tag(v_l_1670_) == 0 {
                    v_size_1702_ = leanh::lean_ctor_get(v_l_1670_, 0);
                    leanh::lean_inc(v_size_1702_);
                    v___y_1694_ = v_size_1702_;
                    state = 34;
                    continue;
                } else {
                    v___x_1703_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1694_ = v___x_1703_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_1686_ = lean_nat_add(v___y_1683_, v___y_1685_);
                leanh::lean_dec(v___y_1685_);
                leanh::lean_dec(v___y_1683_);
                if v_isShared_1678_ == 0 {
                    leanh::lean_ctor_set(v___x_1677_, 4, v_r_1654_);
                    leanh::lean_ctor_set(v___x_1677_, 3, v_r_1671_);
                    leanh::lean_ctor_set(v___x_1677_, 2, v_v_1652_);
                    leanh::lean_ctor_set(v___x_1677_, 1, v_k_1651_);
                    leanh::lean_ctor_set(v___x_1677_, 0, v___x_1686_);
                    v___x_1688_ = v___x_1677_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_1692_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 0, v___x_1686_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 1, v_k_1651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 2, v_v_1652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 3, v_r_1671_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1692_, 4, v_r_1654_);
                    v___x_1688_ = v_reuseFailAlloc_1692_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1666_ == 0 {
                    leanh::lean_ctor_set(v___x_1665_, 4, v___x_1688_);
                    leanh::lean_ctor_set(v___x_1665_, 3, v___y_1684_);
                    leanh::lean_ctor_set(v___x_1665_, 2, v_v_1669_);
                    leanh::lean_ctor_set(v___x_1665_, 1, v_k_1668_);
                    leanh::lean_ctor_set(v___x_1665_, 0, v___x_1681_);
                    v___x_1690_ = v___x_1665_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1691_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 0, v___x_1681_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 1, v_k_1668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 2, v_v_1669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 3, v___y_1684_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1691_, 4, v___x_1688_);
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
                leanh::lean_dec(v___y_1694_);
                leanh::lean_dec(v___x_1680_);
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set(v___x_1467_, 4, v_l_1670_);
                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1695_);
                    v___x_1697_ = v___x_1467_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1695_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_l_1464_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 4, v_l_1670_);
                    v___x_1697_ = v_reuseFailAlloc_1701_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_1698_ = lean_nat_add(v___x_1679_, v_size_1672_);
                if leanh::lean_obj_tag(v_r_1671_) == 0 {
                    v_size_1699_ = leanh::lean_ctor_get(v_r_1671_, 0);
                    leanh::lean_inc(v_size_1699_);
                    v___y_1683_ = v___x_1698_;
                    v___y_1684_ = v___x_1697_;
                    v___y_1685_ = v_size_1699_;
                    state = 31;
                    continue;
                } else {
                    v___x_1700_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1683_ = v___x_1698_;
                    v___y_1684_ = v___x_1697_;
                    v___y_1685_ = v___x_1700_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                v_isSharedCheck_1722_ = (!leanh::lean_is_exclusive(v_l_1464_)) as u8;
                if v_isSharedCheck_1722_ == 0 {
                    v_unused_1723_ = leanh::lean_ctor_get(v_l_1464_, 4);
                    leanh::lean_dec(v_unused_1723_);
                    v_unused_1724_ = leanh::lean_ctor_get(v_l_1464_, 3);
                    leanh::lean_dec(v_unused_1724_);
                    v_unused_1725_ = leanh::lean_ctor_get(v_l_1464_, 2);
                    leanh::lean_dec(v_unused_1725_);
                    v_unused_1726_ = leanh::lean_ctor_get(v_l_1464_, 1);
                    leanh::lean_dec(v_unused_1726_);
                    v_unused_1727_ = leanh::lean_ctor_get(v_l_1464_, 0);
                    leanh::lean_dec(v_unused_1727_);
                    v___x_1717_ = v_l_1464_;
                    v_isShared_1718_ = v_isSharedCheck_1722_;
                    state = 37;
                    continue;
                } else {
                    leanh::lean_dec(v_l_1464_);
                    v___x_1717_ = leanh::lean_box(0);
                    v_isShared_1718_ = v_isSharedCheck_1722_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_1718_ == 0 {
                    leanh::lean_ctor_set(v___x_1717_, 4, v_r_1654_);
                    leanh::lean_ctor_set(v___x_1717_, 3, v___x_1715_);
                    leanh::lean_ctor_set(v___x_1717_, 2, v_v_1652_);
                    leanh::lean_ctor_set(v___x_1717_, 1, v_k_1651_);
                    leanh::lean_ctor_set(v___x_1717_, 0, v___x_1712_);
                    v___x_1720_ = v___x_1717_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_1721_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1712_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_k_1651_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_v_1652_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 3, v___x_1715_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1721_, 4, v_r_1654_);
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
                v_size_1753_ = leanh::lean_ctor_get(v_l_1745_, 0);
                v___x_1754_ = leanh::lean_unsigned_to_nat(1);
                v___x_1755_ = lean_nat_add(v___x_1754_, v_size_1747_);
                leanh::lean_dec(v_size_1747_);
                v___x_1756_ = lean_nat_add(v___x_1754_, v_size_1753_);
                if v_isShared_1752_ == 0 {
                    leanh::lean_ctor_set(v___x_1751_, 4, v_l_1745_);
                    leanh::lean_ctor_set(v___x_1751_, 3, v_l_1464_);
                    leanh::lean_ctor_set(v___x_1751_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v___x_1751_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v___x_1751_, 0, v___x_1756_);
                    v___x_1758_ = v___x_1751_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1762_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 0, v___x_1756_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 3, v_l_1464_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1762_, 4, v_l_1745_);
                    v___x_1758_ = v_reuseFailAlloc_1762_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set(v___x_1467_, 4, v_r_1746_);
                    leanh::lean_ctor_set(v___x_1467_, 3, v___x_1758_);
                    leanh::lean_ctor_set(v___x_1467_, 2, v_v_1749_);
                    leanh::lean_ctor_set(v___x_1467_, 1, v_k_1748_);
                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1755_);
                    v___x_1760_ = v___x_1467_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_1761_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 0, v___x_1755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 1, v_k_1748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 2, v_v_1749_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 3, v___x_1758_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1761_, 4, v_r_1746_);
                    v___x_1760_ = v_reuseFailAlloc_1761_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_1760_;
            }
            43 => {
                v_k_1771_ = leanh::lean_ctor_get(v_l_1745_, 1);
                v_v_1772_ = leanh::lean_ctor_get(v_l_1745_, 2);
                v_isSharedCheck_1787_ = (!leanh::lean_is_exclusive(v_l_1745_)) as u8;
                if v_isSharedCheck_1787_ == 0 {
                    v_unused_1788_ = leanh::lean_ctor_get(v_l_1745_, 4);
                    leanh::lean_dec(v_unused_1788_);
                    v_unused_1789_ = leanh::lean_ctor_get(v_l_1745_, 3);
                    leanh::lean_dec(v_unused_1789_);
                    v_unused_1790_ = leanh::lean_ctor_get(v_l_1745_, 0);
                    leanh::lean_dec(v_unused_1790_);
                    v___x_1774_ = v_l_1745_;
                    v_isShared_1775_ = v_isSharedCheck_1787_;
                    state = 44;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1772_);
                    leanh::lean_inc(v_k_1771_);
                    leanh::lean_dec(v_l_1745_);
                    v___x_1774_ = leanh::lean_box(0);
                    v_isShared_1775_ = v_isSharedCheck_1787_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                v___x_1776_ = leanh::lean_unsigned_to_nat(3);
                v___x_1777_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_1775_ == 0 {
                    leanh::lean_ctor_set(v___x_1774_, 4, v_r_1746_);
                    leanh::lean_ctor_set(v___x_1774_, 3, v_r_1746_);
                    leanh::lean_ctor_set(v___x_1774_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v___x_1774_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v___x_1774_, 0, v___x_1777_);
                    v___x_1779_ = v___x_1774_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_1786_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 3, v_r_1746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 4, v_r_1746_);
                    v___x_1779_ = v_reuseFailAlloc_1786_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_1770_ == 0 {
                    leanh::lean_ctor_set(v___x_1769_, 3, v_r_1746_);
                    leanh::lean_ctor_set(v___x_1769_, 0, v___x_1777_);
                    v___x_1781_ = v___x_1769_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_k_1766_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_v_1767_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_r_1746_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 4, v_r_1746_);
                    v___x_1781_ = v_reuseFailAlloc_1785_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set(v___x_1467_, 4, v___x_1781_);
                    leanh::lean_ctor_set(v___x_1467_, 3, v___x_1779_);
                    leanh::lean_ctor_set(v___x_1467_, 2, v_v_1772_);
                    leanh::lean_ctor_set(v___x_1467_, 1, v_k_1771_);
                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1776_);
                    v___x_1783_ = v___x_1467_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_1784_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 0, v___x_1776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_k_1771_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_v_1772_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 3, v___x_1779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1784_, 4, v___x_1781_);
                    v___x_1783_ = v_reuseFailAlloc_1784_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_1783_;
            }
            48 => {
                v___x_1801_ = leanh::lean_unsigned_to_nat(3);
                v___x_1802_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_1800_ == 0 {
                    leanh::lean_ctor_set(v___x_1799_, 4, v_l_1745_);
                    leanh::lean_ctor_set(v___x_1799_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v___x_1799_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v___x_1799_, 0, v___x_1802_);
                    v___x_1804_ = v___x_1799_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_1808_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_k_1462_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_v_1463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_l_1745_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_l_1745_);
                    v___x_1804_ = v_reuseFailAlloc_1808_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                if v_isShared_1468_ == 0 {
                    leanh::lean_ctor_set(v___x_1467_, 4, v_r_1795_);
                    leanh::lean_ctor_set(v___x_1467_, 3, v___x_1804_);
                    leanh::lean_ctor_set(v___x_1467_, 2, v_v_1797_);
                    leanh::lean_ctor_set(v___x_1467_, 1, v_k_1796_);
                    leanh::lean_ctor_set(v___x_1467_, 0, v___x_1801_);
                    v___x_1806_ = v___x_1467_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_1807_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_k_1796_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_v_1797_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 3, v___x_1804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_r_1795_);
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
    mut v_obj_1824_: *mut leanh::LeanObject,
    mut v_prop_1825_: *mut leanh::LeanObject,
    mut v_val_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1825_, v_val_1826_, v_obj_1824_);
    return v___x_1827_;
}
pub unsafe fn l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0(
    mut v_00_u03b2_1828_: *mut leanh::LeanObject,
    mut v_msg_1829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1830_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v_msg_1829_);
    return v___x_1830_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0(
    mut v_00_u03b2_1831_: *mut leanh::LeanObject,
    mut v_k_1832_: *mut leanh::LeanObject,
    mut v_v_1833_: *mut leanh::LeanObject,
    mut v_t_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_k_1832_, v_v_1833_, v_t_1834_);
    return v___x_1835_;
}
pub unsafe fn l_Lake_JsonObject_insert___redArg(
    mut v_inst_1836_: *mut leanh::LeanObject,
    mut v_obj_1837_: *mut leanh::LeanObject,
    mut v_prop_1838_: *mut leanh::LeanObject,
    mut v_val_1839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1841_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ = leanh::lean_apply_1(v_inst_1836_, v_val_1839_);
    v___x_1841_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1838_, v___x_1840_, v_obj_1837_);
    return v___x_1841_;
}
pub unsafe fn l_Lake_JsonObject_insert(
    mut v_00_u03b1_1842_: *mut leanh::LeanObject,
    mut v_inst_1843_: *mut leanh::LeanObject,
    mut v_obj_1844_: *mut leanh::LeanObject,
    mut v_prop_1845_: *mut leanh::LeanObject,
    mut v_val_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = leanh::lean_apply_1(v_inst_1843_, v_val_1846_);
    v___x_1848_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1845_, v___x_1847_, v_obj_1844_);
    return v___x_1848_;
}
pub unsafe fn l_Lake_JsonObject_insertSome___redArg(
    mut v_inst_1849_: *mut leanh::LeanObject,
    mut v_obj_1850_: *mut leanh::LeanObject,
    mut v_prop_1851_: *mut leanh::LeanObject,
    mut v_val_x3f_1852_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_val_x3f_1852_) == 1 {
        let mut v_val_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1853_ = leanh::lean_ctor_get(v_val_x3f_1852_, 0);
        leanh::lean_inc(v_val_1853_);
        leanh::lean_dec_ref_known(v_val_x3f_1852_, 1);
        v___x_1854_ = leanh::lean_apply_1(v_inst_1849_, v_val_1853_);
        v___x_1855_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1851_, v___x_1854_, v_obj_1850_);
        return v___x_1855_;
    } else {
        leanh::lean_dec(v_val_x3f_1852_);
        leanh::lean_dec_ref(v_prop_1851_);
        leanh::lean_dec_ref(v_inst_1849_);
        return v_obj_1850_;
    }
}
pub unsafe fn l_Lake_JsonObject_insertSome(
    mut v_00_u03b1_1856_: *mut leanh::LeanObject,
    mut v_inst_1857_: *mut leanh::LeanObject,
    mut v_obj_1858_: *mut leanh::LeanObject,
    mut v_prop_1859_: *mut leanh::LeanObject,
    mut v_val_x3f_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_val_x3f_1860_) == 1 {
        let mut v_val_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1861_ = leanh::lean_ctor_get(v_val_x3f_1860_, 0);
        leanh::lean_inc(v_val_1861_);
        leanh::lean_dec_ref_known(v_val_x3f_1860_, 1);
        v___x_1862_ = leanh::lean_apply_1(v_inst_1857_, v_val_1861_);
        v___x_1863_ = l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg(v_prop_1859_, v___x_1862_, v_obj_1858_);
        return v___x_1863_;
    } else {
        leanh::lean_dec(v_val_x3f_1860_);
        leanh::lean_dec_ref(v_prop_1859_);
        leanh::lean_dec_ref(v_inst_1857_);
        return v_obj_1858_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(
    mut v_k_1864_: *mut leanh::LeanObject,
    mut v_t_1865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1872_: u8 = 0;
    let mut v___x_1873_: u8 = 0;
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1892_: u8 = 0;
    let mut v_size_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: u8 = 0;
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut v_unused_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1948_: u8 = 0;
    let mut v_unused_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1959_: u8 = 0;
    let mut v_unused_1960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1978_: u8 = 0;
    let mut v_size_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1989_: u8 = 0;
    let mut v_unused_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1996_: u8 = 0;
    let mut v_k_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2013_: u8 = 0;
    let mut v_unused_2014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2017_: u8 = 0;
    let mut v_unused_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2026_: u8 = 0;
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2035_: u8 = 0;
    let mut v_unused_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: u8 = 0;
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2060_: u8 = 0;
    let mut v_d_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: u8 = 0;
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2077_: u8 = 0;
    let mut v_size_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: u8 = 0;
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2089_: u8 = 0;
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2115_: u8 = 0;
    let mut v_unused_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_unused_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2143_: u8 = 0;
    let mut v_k_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2174_: u8 = 0;
    let mut v_unused_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2178_: u8 = 0;
    let mut v_unused_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v_k_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2197_: u8 = 0;
    let mut v_unused_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v_unused_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2217_: u8 = 0;
    let mut v_d_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v_size_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: u8 = 0;
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2246_: u8 = 0;
    let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2259_: u8 = 0;
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut v_unused_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2282_: u8 = 0;
    let mut v_unused_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_unused_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2311_: u8 = 0;
    let mut v_k_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut v_unused_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2342_: u8 = 0;
    let mut v_k_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2349_: u8 = 0;
    let mut v___x_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut v_unused_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2365_: u8 = 0;
    let mut v_unused_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2377_: u8 = 0;
    let mut v_unused_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: u8 = 0;
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2401_: u8 = 0;
    let mut v_size_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: u8 = 0;
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2413_: u8 = 0;
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut v_unused_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_unused_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut v_unused_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v_size_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut v_unused_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2507_: u8 = 0;
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2516_: u8 = 0;
    let mut v_unused_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2525_: u8 = 0;
    let mut v_k_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2542_: u8 = 0;
    let mut v_unused_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_unused_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v_unused_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_1865_) == 0 {
                    v_k_1866_ = leanh::lean_ctor_get(v_t_1865_, 1);
                    v_v_1867_ = leanh::lean_ctor_get(v_t_1865_, 2);
                    v_l_1868_ = leanh::lean_ctor_get(v_t_1865_, 3);
                    v_r_1869_ = leanh::lean_ctor_get(v_t_1865_, 4);
                    v_isSharedCheck_2558_ = (!leanh::lean_is_exclusive(v_t_1865_)) as u8;
                    if v_isSharedCheck_2558_ == 0 {
                        v_unused_2559_ = leanh::lean_ctor_get(v_t_1865_, 0);
                        leanh::lean_dec(v_unused_2559_);
                        v___x_1871_ = v_t_1865_;
                        v_isShared_1872_ = v_isSharedCheck_2558_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_r_1869_);
                        leanh::lean_inc(v_l_1868_);
                        leanh::lean_inc(v_v_1867_);
                        leanh::lean_inc(v_k_1866_);
                        leanh::lean_dec(v_t_1865_);
                        v___x_1871_ = leanh::lean_box(0);
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
                        if leanh::lean_obj_tag(v___x_1874_) == 0 {
                            if leanh::lean_obj_tag(v_r_1869_) == 0 {
                                v_size_1875_ = leanh::lean_ctor_get(v___x_1874_, 0);
                                leanh::lean_inc(v_size_1875_);
                                v_size_1876_ = leanh::lean_ctor_get(v_r_1869_, 0);
                                v_k_1877_ = leanh::lean_ctor_get(v_r_1869_, 1);
                                v_v_1878_ = leanh::lean_ctor_get(v_r_1869_, 2);
                                v_l_1879_ = leanh::lean_ctor_get(v_r_1869_, 3);
                                leanh::lean_inc(v_l_1879_);
                                v_r_1880_ = leanh::lean_ctor_get(v_r_1869_, 4);
                                v___x_1881_ = leanh::lean_unsigned_to_nat(3);
                                v___x_1882_ = lean_nat_mul(v___x_1881_, v_size_1875_);
                                v___x_1883_ = lean_nat_dec_lt(v___x_1882_, v_size_1876_);
                                leanh::lean_dec(v___x_1882_);
                                if v___x_1883_ == 0 {
                                    leanh::lean_dec(v_l_1879_);
                                    v___x_1884_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_1885_ = lean_nat_add(v___x_1884_, v_size_1875_);
                                    leanh::lean_dec(v_size_1875_);
                                    v___x_1886_ = lean_nat_add(v___x_1885_, v_size_1876_);
                                    leanh::lean_dec(v___x_1885_);
                                    if v_isShared_1872_ == 0 {
                                        leanh::lean_ctor_set(v___x_1871_, 3, v___x_1874_);
                                        leanh::lean_ctor_set(v___x_1871_, 0, v___x_1886_);
                                        v___x_1888_ = v___x_1871_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1889_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            0,
                                            v___x_1886_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            1,
                                            v_k_1866_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            2,
                                            v_v_1867_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            3,
                                            v___x_1874_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1889_,
                                            4,
                                            v_r_1869_,
                                        );
                                        v___x_1888_ = v_reuseFailAlloc_1889_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_1880_);
                                    leanh::lean_inc(v_v_1878_);
                                    leanh::lean_inc(v_k_1877_);
                                    leanh::lean_inc(v_size_1876_);
                                    v_isSharedCheck_1959_ =
                                        (!leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                    if v_isSharedCheck_1959_ == 0 {
                                        v_unused_1960_ = leanh::lean_ctor_get(v_r_1869_, 4);
                                        leanh::lean_dec(v_unused_1960_);
                                        v_unused_1961_ = leanh::lean_ctor_get(v_r_1869_, 3);
                                        leanh::lean_dec(v_unused_1961_);
                                        v_unused_1962_ = leanh::lean_ctor_get(v_r_1869_, 2);
                                        leanh::lean_dec(v_unused_1962_);
                                        v_unused_1963_ = leanh::lean_ctor_get(v_r_1869_, 1);
                                        leanh::lean_dec(v_unused_1963_);
                                        v_unused_1964_ = leanh::lean_ctor_get(v_r_1869_, 0);
                                        leanh::lean_dec(v_unused_1964_);
                                        v___x_1891_ = v_r_1869_;
                                        v_isShared_1892_ = v_isSharedCheck_1959_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_1869_);
                                        v___x_1891_ = leanh::lean_box(0);
                                        v_isShared_1892_ = v_isSharedCheck_1959_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_1965_ = leanh::lean_ctor_get(v___x_1874_, 0);
                                leanh::lean_inc(v_size_1965_);
                                v___x_1966_ = leanh::lean_unsigned_to_nat(1);
                                v___x_1967_ = lean_nat_add(v___x_1966_, v_size_1965_);
                                leanh::lean_dec(v_size_1965_);
                                if v_isShared_1872_ == 0 {
                                    leanh::lean_ctor_set(v___x_1871_, 3, v___x_1874_);
                                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_1967_);
                                    v___x_1969_ = v___x_1871_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1970_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1970_,
                                        0,
                                        v___x_1967_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1970_,
                                        1,
                                        v_k_1866_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1970_,
                                        2,
                                        v_v_1867_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1970_,
                                        3,
                                        v___x_1874_,
                                    );
                                    leanh::lean_ctor_set(
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
                            if leanh::lean_obj_tag(v_r_1869_) == 0 {
                                v_l_1971_ = leanh::lean_ctor_get(v_r_1869_, 3);
                                leanh::lean_inc(v_l_1971_);
                                if leanh::lean_obj_tag(v_l_1971_) == 0 {
                                    v_r_1972_ = leanh::lean_ctor_get(v_r_1869_, 4);
                                    leanh::lean_inc(v_r_1972_);
                                    if leanh::lean_obj_tag(v_r_1972_) == 0 {
                                        v_size_1973_ = leanh::lean_ctor_get(v_r_1869_, 0);
                                        v_k_1974_ = leanh::lean_ctor_get(v_r_1869_, 1);
                                        v_v_1975_ = leanh::lean_ctor_get(v_r_1869_, 2);
                                        v_isSharedCheck_1989_ =
                                            (!leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                        if v_isSharedCheck_1989_ == 0 {
                                            v_unused_1990_ =
                                                leanh::lean_ctor_get(v_r_1869_, 4);
                                            leanh::lean_dec(v_unused_1990_);
                                            v_unused_1991_ =
                                                leanh::lean_ctor_get(v_r_1869_, 3);
                                            leanh::lean_dec(v_unused_1991_);
                                            v___x_1977_ = v_r_1869_;
                                            v_isShared_1978_ = v_isSharedCheck_1989_;
                                            state = 14;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1975_);
                                            leanh::lean_inc(v_k_1974_);
                                            leanh::lean_inc(v_size_1973_);
                                            leanh::lean_dec(v_r_1869_);
                                            v___x_1977_ = leanh::lean_box(0);
                                            v_isShared_1978_ = v_isSharedCheck_1989_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_1992_ = leanh::lean_ctor_get(v_r_1869_, 1);
                                        v_v_1993_ = leanh::lean_ctor_get(v_r_1869_, 2);
                                        v_isSharedCheck_2017_ =
                                            (!leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                        if v_isSharedCheck_2017_ == 0 {
                                            v_unused_2018_ =
                                                leanh::lean_ctor_get(v_r_1869_, 4);
                                            leanh::lean_dec(v_unused_2018_);
                                            v_unused_2019_ =
                                                leanh::lean_ctor_get(v_r_1869_, 3);
                                            leanh::lean_dec(v_unused_2019_);
                                            v_unused_2020_ =
                                                leanh::lean_ctor_get(v_r_1869_, 0);
                                            leanh::lean_dec(v_unused_2020_);
                                            v___x_1995_ = v_r_1869_;
                                            v_isShared_1996_ = v_isSharedCheck_2017_;
                                            state = 17;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_1993_);
                                            leanh::lean_inc(v_k_1992_);
                                            leanh::lean_dec(v_r_1869_);
                                            v___x_1995_ = leanh::lean_box(0);
                                            v_isShared_1996_ = v_isSharedCheck_2017_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2021_ = leanh::lean_ctor_get(v_r_1869_, 4);
                                    leanh::lean_inc(v_r_2021_);
                                    if leanh::lean_obj_tag(v_r_2021_) == 0 {
                                        v_k_2022_ = leanh::lean_ctor_get(v_r_1869_, 1);
                                        v_v_2023_ = leanh::lean_ctor_get(v_r_1869_, 2);
                                        v_isSharedCheck_2035_ =
                                            (!leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                        if v_isSharedCheck_2035_ == 0 {
                                            v_unused_2036_ =
                                                leanh::lean_ctor_get(v_r_1869_, 4);
                                            leanh::lean_dec(v_unused_2036_);
                                            v_unused_2037_ =
                                                leanh::lean_ctor_get(v_r_1869_, 3);
                                            leanh::lean_dec(v_unused_2037_);
                                            v_unused_2038_ =
                                                leanh::lean_ctor_get(v_r_1869_, 0);
                                            leanh::lean_dec(v_unused_2038_);
                                            v___x_2025_ = v_r_1869_;
                                            v_isShared_2026_ = v_isSharedCheck_2035_;
                                            state = 22;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2023_);
                                            leanh::lean_inc(v_k_2022_);
                                            leanh::lean_dec(v_r_1869_);
                                            v___x_2025_ = leanh::lean_box(0);
                                            v_isShared_2026_ = v_isSharedCheck_2035_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v___x_2039_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1872_ == 0 {
                                            leanh::lean_ctor_set(v___x_1871_, 3, v_r_2021_);
                                            leanh::lean_ctor_set(
                                                v___x_1871_,
                                                0,
                                                v___x_2039_,
                                            );
                                            v___x_2041_ = v___x_1871_;
                                            state = 25;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2042_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2042_,
                                                0,
                                                v___x_2039_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2042_,
                                                1,
                                                v_k_1866_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2042_,
                                                2,
                                                v_v_1867_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2042_,
                                                3,
                                                v_r_2021_,
                                            );
                                            leanh::lean_ctor_set(
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
                                v___x_2043_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1872_ == 0 {
                                    leanh::lean_ctor_set(v___x_1871_, 3, v_r_1869_);
                                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_2043_);
                                    v___x_2045_ = v___x_1871_;
                                    state = 26;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2046_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2046_,
                                        0,
                                        v___x_2043_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2046_,
                                        1,
                                        v_k_1866_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2046_,
                                        2,
                                        v_v_1867_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2046_,
                                        3,
                                        v_r_1869_,
                                    );
                                    leanh::lean_ctor_set(
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
                        leanh::lean_del_object(v___x_1871_);
                        leanh::lean_dec(v_v_1867_);
                        leanh::lean_dec(v_k_1866_);
                        if leanh::lean_obj_tag(v_l_1868_) == 0 {
                            if leanh::lean_obj_tag(v_r_1869_) == 0 {
                                v_size_2047_ = leanh::lean_ctor_get(v_l_1868_, 0);
                                v_k_2048_ = leanh::lean_ctor_get(v_l_1868_, 1);
                                v_v_2049_ = leanh::lean_ctor_get(v_l_1868_, 2);
                                v_l_2050_ = leanh::lean_ctor_get(v_l_1868_, 3);
                                v_r_2051_ = leanh::lean_ctor_get(v_l_1868_, 4);
                                leanh::lean_inc(v_r_2051_);
                                v_size_2052_ = leanh::lean_ctor_get(v_r_1869_, 0);
                                v_k_2053_ = leanh::lean_ctor_get(v_r_1869_, 1);
                                v_v_2054_ = leanh::lean_ctor_get(v_r_1869_, 2);
                                v_l_2055_ = leanh::lean_ctor_get(v_r_1869_, 3);
                                leanh::lean_inc(v_l_2055_);
                                v_r_2056_ = leanh::lean_ctor_get(v_r_1869_, 4);
                                v___x_2057_ = lean_nat_dec_lt(v_size_2047_, v_size_2052_);
                                if v___x_2057_ == 0 {
                                    leanh::lean_inc(v_l_2050_);
                                    leanh::lean_inc(v_v_2049_);
                                    leanh::lean_inc(v_k_2048_);
                                    v_isSharedCheck_2209_ =
                                        (!leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                    if v_isSharedCheck_2209_ == 0 {
                                        v_unused_2210_ = leanh::lean_ctor_get(v_l_1868_, 4);
                                        leanh::lean_dec(v_unused_2210_);
                                        v_unused_2211_ = leanh::lean_ctor_get(v_l_1868_, 3);
                                        leanh::lean_dec(v_unused_2211_);
                                        v_unused_2212_ = leanh::lean_ctor_get(v_l_1868_, 2);
                                        leanh::lean_dec(v_unused_2212_);
                                        v_unused_2213_ = leanh::lean_ctor_get(v_l_1868_, 1);
                                        leanh::lean_dec(v_unused_2213_);
                                        v_unused_2214_ = leanh::lean_ctor_get(v_l_1868_, 0);
                                        leanh::lean_dec(v_unused_2214_);
                                        v___x_2059_ = v_l_1868_;
                                        v_isShared_2060_ = v_isSharedCheck_2209_;
                                        state = 27;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_1868_);
                                        v___x_2059_ = leanh::lean_box(0);
                                        v_isShared_2060_ = v_isSharedCheck_2209_;
                                        state = 27;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_r_2056_);
                                    leanh::lean_inc(v_v_2054_);
                                    leanh::lean_inc(v_k_2053_);
                                    v_isSharedCheck_2377_ =
                                        (!leanh::lean_is_exclusive(v_r_1869_)) as u8;
                                    if v_isSharedCheck_2377_ == 0 {
                                        v_unused_2378_ = leanh::lean_ctor_get(v_r_1869_, 4);
                                        leanh::lean_dec(v_unused_2378_);
                                        v_unused_2379_ = leanh::lean_ctor_get(v_r_1869_, 3);
                                        leanh::lean_dec(v_unused_2379_);
                                        v_unused_2380_ = leanh::lean_ctor_get(v_r_1869_, 2);
                                        leanh::lean_dec(v_unused_2380_);
                                        v_unused_2381_ = leanh::lean_ctor_get(v_r_1869_, 1);
                                        leanh::lean_dec(v_unused_2381_);
                                        v_unused_2382_ = leanh::lean_ctor_get(v_r_1869_, 0);
                                        leanh::lean_dec(v_unused_2382_);
                                        v___x_2216_ = v_r_1869_;
                                        v_isShared_2217_ = v_isSharedCheck_2377_;
                                        state = 49;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_r_1869_);
                                        v___x_2216_ = leanh::lean_box(0);
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
                        if leanh::lean_obj_tag(v___x_2383_) == 0 {
                            if leanh::lean_obj_tag(v_l_1868_) == 0 {
                                v_size_2384_ = leanh::lean_ctor_get(v___x_2383_, 0);
                                leanh::lean_inc(v_size_2384_);
                                v_size_2385_ = leanh::lean_ctor_get(v_l_1868_, 0);
                                v_k_2386_ = leanh::lean_ctor_get(v_l_1868_, 1);
                                v_v_2387_ = leanh::lean_ctor_get(v_l_1868_, 2);
                                v_l_2388_ = leanh::lean_ctor_get(v_l_1868_, 3);
                                v_r_2389_ = leanh::lean_ctor_get(v_l_1868_, 4);
                                leanh::lean_inc(v_r_2389_);
                                v___x_2390_ = leanh::lean_unsigned_to_nat(3);
                                v___x_2391_ = lean_nat_mul(v___x_2390_, v_size_2384_);
                                v___x_2392_ = lean_nat_dec_lt(v___x_2391_, v_size_2385_);
                                leanh::lean_dec(v___x_2391_);
                                if v___x_2392_ == 0 {
                                    leanh::lean_dec(v_r_2389_);
                                    v___x_2393_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_2394_ = lean_nat_add(v___x_2393_, v_size_2385_);
                                    v___x_2395_ = lean_nat_add(v___x_2394_, v_size_2384_);
                                    leanh::lean_dec(v_size_2384_);
                                    leanh::lean_dec(v___x_2394_);
                                    if v_isShared_1872_ == 0 {
                                        leanh::lean_ctor_set(v___x_1871_, 4, v___x_2383_);
                                        leanh::lean_ctor_set(v___x_1871_, 0, v___x_2395_);
                                        v___x_2397_ = v___x_1871_;
                                        state = 72;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_2398_ =
                                            leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            0,
                                            v___x_2395_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            1,
                                            v_k_1866_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            2,
                                            v_v_1867_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            3,
                                            v_l_1868_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_2398_,
                                            4,
                                            v___x_2383_,
                                        );
                                        v___x_2397_ = v_reuseFailAlloc_2398_;
                                        state = 72;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_inc(v_l_2388_);
                                    leanh::lean_inc(v_v_2387_);
                                    leanh::lean_inc(v_k_2386_);
                                    leanh::lean_inc(v_size_2385_);
                                    v_isSharedCheck_2470_ =
                                        (!leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                    if v_isSharedCheck_2470_ == 0 {
                                        v_unused_2471_ = leanh::lean_ctor_get(v_l_1868_, 4);
                                        leanh::lean_dec(v_unused_2471_);
                                        v_unused_2472_ = leanh::lean_ctor_get(v_l_1868_, 3);
                                        leanh::lean_dec(v_unused_2472_);
                                        v_unused_2473_ = leanh::lean_ctor_get(v_l_1868_, 2);
                                        leanh::lean_dec(v_unused_2473_);
                                        v_unused_2474_ = leanh::lean_ctor_get(v_l_1868_, 1);
                                        leanh::lean_dec(v_unused_2474_);
                                        v_unused_2475_ = leanh::lean_ctor_get(v_l_1868_, 0);
                                        leanh::lean_dec(v_unused_2475_);
                                        v___x_2400_ = v_l_1868_;
                                        v_isShared_2401_ = v_isSharedCheck_2470_;
                                        state = 73;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_1868_);
                                        v___x_2400_ = leanh::lean_box(0);
                                        v_isShared_2401_ = v_isSharedCheck_2470_;
                                        state = 73;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_2476_ = leanh::lean_ctor_get(v___x_2383_, 0);
                                leanh::lean_inc(v_size_2476_);
                                v___x_2477_ = leanh::lean_unsigned_to_nat(1);
                                v___x_2478_ = lean_nat_add(v___x_2477_, v_size_2476_);
                                leanh::lean_dec(v_size_2476_);
                                if v_isShared_1872_ == 0 {
                                    leanh::lean_ctor_set(v___x_1871_, 4, v___x_2383_);
                                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_2478_);
                                    v___x_2480_ = v___x_1871_;
                                    state = 83;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2481_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2481_,
                                        0,
                                        v___x_2478_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2481_,
                                        1,
                                        v_k_1866_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2481_,
                                        2,
                                        v_v_1867_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2481_,
                                        3,
                                        v_l_1868_,
                                    );
                                    leanh::lean_ctor_set(
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
                            if leanh::lean_obj_tag(v_l_1868_) == 0 {
                                v_l_2482_ = leanh::lean_ctor_get(v_l_1868_, 3);
                                if leanh::lean_obj_tag(v_l_2482_) == 0 {
                                    leanh::lean_inc_ref(v_l_2482_);
                                    v_r_2483_ = leanh::lean_ctor_get(v_l_1868_, 4);
                                    leanh::lean_inc(v_r_2483_);
                                    if leanh::lean_obj_tag(v_r_2483_) == 0 {
                                        v_size_2484_ = leanh::lean_ctor_get(v_l_1868_, 0);
                                        v_k_2485_ = leanh::lean_ctor_get(v_l_1868_, 1);
                                        v_v_2486_ = leanh::lean_ctor_get(v_l_1868_, 2);
                                        v_isSharedCheck_2500_ =
                                            (!leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                        if v_isSharedCheck_2500_ == 0 {
                                            v_unused_2501_ =
                                                leanh::lean_ctor_get(v_l_1868_, 4);
                                            leanh::lean_dec(v_unused_2501_);
                                            v_unused_2502_ =
                                                leanh::lean_ctor_get(v_l_1868_, 3);
                                            leanh::lean_dec(v_unused_2502_);
                                            v___x_2488_ = v_l_1868_;
                                            v_isShared_2489_ = v_isSharedCheck_2500_;
                                            state = 84;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2486_);
                                            leanh::lean_inc(v_k_2485_);
                                            leanh::lean_inc(v_size_2484_);
                                            leanh::lean_dec(v_l_1868_);
                                            v___x_2488_ = leanh::lean_box(0);
                                            v_isShared_2489_ = v_isSharedCheck_2500_;
                                            state = 84;
                                            continue;
                                        }
                                    } else {
                                        v_k_2503_ = leanh::lean_ctor_get(v_l_1868_, 1);
                                        v_v_2504_ = leanh::lean_ctor_get(v_l_1868_, 2);
                                        v_isSharedCheck_2516_ =
                                            (!leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                        if v_isSharedCheck_2516_ == 0 {
                                            v_unused_2517_ =
                                                leanh::lean_ctor_get(v_l_1868_, 4);
                                            leanh::lean_dec(v_unused_2517_);
                                            v_unused_2518_ =
                                                leanh::lean_ctor_get(v_l_1868_, 3);
                                            leanh::lean_dec(v_unused_2518_);
                                            v_unused_2519_ =
                                                leanh::lean_ctor_get(v_l_1868_, 0);
                                            leanh::lean_dec(v_unused_2519_);
                                            v___x_2506_ = v_l_1868_;
                                            v_isShared_2507_ = v_isSharedCheck_2516_;
                                            state = 87;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2504_);
                                            leanh::lean_inc(v_k_2503_);
                                            leanh::lean_dec(v_l_1868_);
                                            v___x_2506_ = leanh::lean_box(0);
                                            v_isShared_2507_ = v_isSharedCheck_2516_;
                                            state = 87;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_2520_ = leanh::lean_ctor_get(v_l_1868_, 4);
                                    leanh::lean_inc(v_r_2520_);
                                    if leanh::lean_obj_tag(v_r_2520_) == 0 {
                                        leanh::lean_inc(v_l_2482_);
                                        v_k_2521_ = leanh::lean_ctor_get(v_l_1868_, 1);
                                        v_v_2522_ = leanh::lean_ctor_get(v_l_1868_, 2);
                                        v_isSharedCheck_2546_ =
                                            (!leanh::lean_is_exclusive(v_l_1868_)) as u8;
                                        if v_isSharedCheck_2546_ == 0 {
                                            v_unused_2547_ =
                                                leanh::lean_ctor_get(v_l_1868_, 4);
                                            leanh::lean_dec(v_unused_2547_);
                                            v_unused_2548_ =
                                                leanh::lean_ctor_get(v_l_1868_, 3);
                                            leanh::lean_dec(v_unused_2548_);
                                            v_unused_2549_ =
                                                leanh::lean_ctor_get(v_l_1868_, 0);
                                            leanh::lean_dec(v_unused_2549_);
                                            v___x_2524_ = v_l_1868_;
                                            v_isShared_2525_ = v_isSharedCheck_2546_;
                                            state = 90;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_v_2522_);
                                            leanh::lean_inc(v_k_2521_);
                                            leanh::lean_dec(v_l_1868_);
                                            v___x_2524_ = leanh::lean_box(0);
                                            v_isShared_2525_ = v_isSharedCheck_2546_;
                                            state = 90;
                                            continue;
                                        }
                                    } else {
                                        v___x_2550_ = leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_1872_ == 0 {
                                            leanh::lean_ctor_set(v___x_1871_, 4, v_r_2520_);
                                            leanh::lean_ctor_set(
                                                v___x_1871_,
                                                0,
                                                v___x_2550_,
                                            );
                                            v___x_2552_ = v___x_1871_;
                                            state = 95;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_2553_ =
                                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2553_,
                                                0,
                                                v___x_2550_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2553_,
                                                1,
                                                v_k_1866_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2553_,
                                                2,
                                                v_v_1867_,
                                            );
                                            leanh::lean_ctor_set(
                                                v_reuseFailAlloc_2553_,
                                                3,
                                                v_l_1868_,
                                            );
                                            leanh::lean_ctor_set(
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
                                v___x_2554_ = leanh::lean_unsigned_to_nat(1);
                                if v_isShared_1872_ == 0 {
                                    leanh::lean_ctor_set(v___x_1871_, 4, v_l_1868_);
                                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_2554_);
                                    v___x_2556_ = v___x_1871_;
                                    state = 96;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2557_ =
                                        leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2557_,
                                        0,
                                        v___x_2554_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2557_,
                                        1,
                                        v_k_1866_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2557_,
                                        2,
                                        v_v_1867_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_2557_,
                                        3,
                                        v_l_1868_,
                                    );
                                    leanh::lean_ctor_set(
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
                if leanh::lean_obj_tag(v_l_1879_) == 0 {
                    if leanh::lean_obj_tag(v_r_1880_) == 0 {
                        v_size_1893_ = leanh::lean_ctor_get(v_l_1879_, 0);
                        v_k_1894_ = leanh::lean_ctor_get(v_l_1879_, 1);
                        v_v_1895_ = leanh::lean_ctor_get(v_l_1879_, 2);
                        v_l_1896_ = leanh::lean_ctor_get(v_l_1879_, 3);
                        v_r_1897_ = leanh::lean_ctor_get(v_l_1879_, 4);
                        v_size_1898_ = leanh::lean_ctor_get(v_r_1880_, 0);
                        v___x_1899_ = leanh::lean_unsigned_to_nat(2);
                        v___x_1900_ = lean_nat_mul(v___x_1899_, v_size_1898_);
                        v___x_1901_ = lean_nat_dec_lt(v_size_1893_, v___x_1900_);
                        leanh::lean_dec(v___x_1900_);
                        if v___x_1901_ == 0 {
                            leanh::lean_inc(v_r_1897_);
                            leanh::lean_inc(v_l_1896_);
                            leanh::lean_inc(v_v_1895_);
                            leanh::lean_inc(v_k_1894_);
                            v_isSharedCheck_1930_ =
                                (!leanh::lean_is_exclusive(v_l_1879_)) as u8;
                            if v_isSharedCheck_1930_ == 0 {
                                v_unused_1931_ = leanh::lean_ctor_get(v_l_1879_, 4);
                                leanh::lean_dec(v_unused_1931_);
                                v_unused_1932_ = leanh::lean_ctor_get(v_l_1879_, 3);
                                leanh::lean_dec(v_unused_1932_);
                                v_unused_1933_ = leanh::lean_ctor_get(v_l_1879_, 2);
                                leanh::lean_dec(v_unused_1933_);
                                v_unused_1934_ = leanh::lean_ctor_get(v_l_1879_, 1);
                                leanh::lean_dec(v_unused_1934_);
                                v_unused_1935_ = leanh::lean_ctor_get(v_l_1879_, 0);
                                leanh::lean_dec(v_unused_1935_);
                                v___x_1903_ = v_l_1879_;
                                v_isShared_1904_ = v_isSharedCheck_1930_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_1879_);
                                v___x_1903_ = leanh::lean_box(0);
                                v_isShared_1904_ = v_isSharedCheck_1930_;
                                state = 4;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1871_);
                            v___x_1936_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1937_ = lean_nat_add(v___x_1936_, v_size_1875_);
                            leanh::lean_dec(v_size_1875_);
                            v___x_1938_ = lean_nat_add(v___x_1937_, v_size_1876_);
                            leanh::lean_dec(v_size_1876_);
                            v___x_1939_ = lean_nat_add(v___x_1937_, v_size_1893_);
                            leanh::lean_dec(v___x_1937_);
                            leanh::lean_inc_ref(v___x_1874_);
                            if v_isShared_1892_ == 0 {
                                leanh::lean_ctor_set(v___x_1891_, 4, v_l_1879_);
                                leanh::lean_ctor_set(v___x_1891_, 3, v___x_1874_);
                                leanh::lean_ctor_set(v___x_1891_, 2, v_v_1867_);
                                leanh::lean_ctor_set(v___x_1891_, 1, v_k_1866_);
                                leanh::lean_ctor_set(v___x_1891_, 0, v___x_1939_);
                                v___x_1941_ = v___x_1891_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1954_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1939_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_k_1866_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_v_1867_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 3, v___x_1874_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1954_, 4, v_l_1879_);
                                v___x_1941_ = v_reuseFailAlloc_1954_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_1879_, 5);
                        leanh::lean_del_object(v___x_1891_);
                        leanh::lean_dec(v_v_1878_);
                        leanh::lean_dec(v_k_1877_);
                        leanh::lean_dec(v_size_1876_);
                        leanh::lean_dec(v_size_1875_);
                        leanh::lean_dec_ref_known(v___x_1874_, 5);
                        leanh::lean_del_object(v___x_1871_);
                        leanh::lean_dec(v_v_1867_);
                        leanh::lean_dec(v_k_1866_);
                        v___x_1955_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7);
                        v___x_1956_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1955_);
                        return v___x_1956_;
                    }
                } else {
                    leanh::lean_del_object(v___x_1891_);
                    leanh::lean_dec(v_r_1880_);
                    leanh::lean_dec(v_v_1878_);
                    leanh::lean_dec(v_k_1877_);
                    leanh::lean_dec(v_size_1876_);
                    leanh::lean_dec(v_size_1875_);
                    leanh::lean_dec_ref_known(v___x_1874_, 5);
                    leanh::lean_del_object(v___x_1871_);
                    leanh::lean_dec(v_v_1867_);
                    leanh::lean_dec(v_k_1866_);
                    v___x_1957_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8);
                    v___x_1958_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_1957_);
                    return v___x_1958_;
                }
            }
            4 => {
                v___x_1905_ = leanh::lean_unsigned_to_nat(1);
                v___x_1906_ = lean_nat_add(v___x_1905_, v_size_1875_);
                leanh::lean_dec(v_size_1875_);
                v___x_1907_ = lean_nat_add(v___x_1906_, v_size_1876_);
                leanh::lean_dec(v_size_1876_);
                if leanh::lean_obj_tag(v_l_1896_) == 0 {
                    v_size_1928_ = leanh::lean_ctor_get(v_l_1896_, 0);
                    leanh::lean_inc(v_size_1928_);
                    v___y_1920_ = v_size_1928_;
                    state = 8;
                    continue;
                } else {
                    v___x_1929_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1920_ = v___x_1929_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1912_ = lean_nat_add(v___y_1910_, v___y_1911_);
                leanh::lean_dec(v___y_1911_);
                leanh::lean_dec(v___y_1910_);
                if v_isShared_1904_ == 0 {
                    leanh::lean_ctor_set(v___x_1903_, 4, v_r_1880_);
                    leanh::lean_ctor_set(v___x_1903_, 3, v_r_1897_);
                    leanh::lean_ctor_set(v___x_1903_, 2, v_v_1878_);
                    leanh::lean_ctor_set(v___x_1903_, 1, v_k_1877_);
                    leanh::lean_ctor_set(v___x_1903_, 0, v___x_1912_);
                    v___x_1914_ = v___x_1903_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1912_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_k_1877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_v_1878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 3, v_r_1897_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 4, v_r_1880_);
                    v___x_1914_ = v_reuseFailAlloc_1918_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1892_ == 0 {
                    leanh::lean_ctor_set(v___x_1891_, 4, v___x_1914_);
                    leanh::lean_ctor_set(v___x_1891_, 3, v___y_1909_);
                    leanh::lean_ctor_set(v___x_1891_, 2, v_v_1895_);
                    leanh::lean_ctor_set(v___x_1891_, 1, v_k_1894_);
                    leanh::lean_ctor_set(v___x_1891_, 0, v___x_1907_);
                    v___x_1916_ = v___x_1891_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 1, v_k_1894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 2, v_v_1895_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 3, v___y_1909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 4, v___x_1914_);
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
                leanh::lean_dec(v___y_1920_);
                leanh::lean_dec(v___x_1906_);
                if v_isShared_1872_ == 0 {
                    leanh::lean_ctor_set(v___x_1871_, 4, v_l_1896_);
                    leanh::lean_ctor_set(v___x_1871_, 3, v___x_1874_);
                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_1921_);
                    v___x_1923_ = v___x_1871_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1927_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 0, v___x_1921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 3, v___x_1874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1927_, 4, v_l_1896_);
                    v___x_1923_ = v_reuseFailAlloc_1927_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1924_ = lean_nat_add(v___x_1905_, v_size_1898_);
                if leanh::lean_obj_tag(v_r_1897_) == 0 {
                    v_size_1925_ = leanh::lean_ctor_get(v_r_1897_, 0);
                    leanh::lean_inc(v_size_1925_);
                    v___y_1909_ = v___x_1923_;
                    v___y_1910_ = v___x_1924_;
                    v___y_1911_ = v_size_1925_;
                    state = 5;
                    continue;
                } else {
                    v___x_1926_ = leanh::lean_unsigned_to_nat(0);
                    v___y_1909_ = v___x_1923_;
                    v___y_1910_ = v___x_1924_;
                    v___y_1911_ = v___x_1926_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1948_ = (!leanh::lean_is_exclusive(v___x_1874_)) as u8;
                if v_isSharedCheck_1948_ == 0 {
                    v_unused_1949_ = leanh::lean_ctor_get(v___x_1874_, 4);
                    leanh::lean_dec(v_unused_1949_);
                    v_unused_1950_ = leanh::lean_ctor_get(v___x_1874_, 3);
                    leanh::lean_dec(v_unused_1950_);
                    v_unused_1951_ = leanh::lean_ctor_get(v___x_1874_, 2);
                    leanh::lean_dec(v_unused_1951_);
                    v_unused_1952_ = leanh::lean_ctor_get(v___x_1874_, 1);
                    leanh::lean_dec(v_unused_1952_);
                    v_unused_1953_ = leanh::lean_ctor_get(v___x_1874_, 0);
                    leanh::lean_dec(v_unused_1953_);
                    v___x_1943_ = v___x_1874_;
                    v_isShared_1944_ = v_isSharedCheck_1948_;
                    state = 11;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1874_);
                    v___x_1943_ = leanh::lean_box(0);
                    v_isShared_1944_ = v_isSharedCheck_1948_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1944_ == 0 {
                    leanh::lean_ctor_set(v___x_1943_, 4, v_r_1880_);
                    leanh::lean_ctor_set(v___x_1943_, 3, v___x_1941_);
                    leanh::lean_ctor_set(v___x_1943_, 2, v_v_1878_);
                    leanh::lean_ctor_set(v___x_1943_, 1, v_k_1877_);
                    leanh::lean_ctor_set(v___x_1943_, 0, v___x_1938_);
                    v___x_1946_ = v___x_1943_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1947_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1938_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_k_1877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_v_1878_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 3, v___x_1941_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1947_, 4, v_r_1880_);
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
                v_size_1979_ = leanh::lean_ctor_get(v_l_1971_, 0);
                v___x_1980_ = leanh::lean_unsigned_to_nat(1);
                v___x_1981_ = lean_nat_add(v___x_1980_, v_size_1973_);
                leanh::lean_dec(v_size_1973_);
                v___x_1982_ = lean_nat_add(v___x_1980_, v_size_1979_);
                if v_isShared_1978_ == 0 {
                    leanh::lean_ctor_set(v___x_1977_, 4, v_l_1971_);
                    leanh::lean_ctor_set(v___x_1977_, 3, v___x_1874_);
                    leanh::lean_ctor_set(v___x_1977_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v___x_1977_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v___x_1977_, 0, v___x_1982_);
                    v___x_1984_ = v___x_1977_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1988_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1982_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 3, v___x_1874_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1988_, 4, v_l_1971_);
                    v___x_1984_ = v_reuseFailAlloc_1988_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_1872_ == 0 {
                    leanh::lean_ctor_set(v___x_1871_, 4, v_r_1972_);
                    leanh::lean_ctor_set(v___x_1871_, 3, v___x_1984_);
                    leanh::lean_ctor_set(v___x_1871_, 2, v_v_1975_);
                    leanh::lean_ctor_set(v___x_1871_, 1, v_k_1974_);
                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_1981_);
                    v___x_1986_ = v___x_1871_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1987_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 0, v___x_1981_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_k_1974_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_v_1975_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 3, v___x_1984_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_r_1972_);
                    v___x_1986_ = v_reuseFailAlloc_1987_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1986_;
            }
            17 => {
                v_k_1997_ = leanh::lean_ctor_get(v_l_1971_, 1);
                v_v_1998_ = leanh::lean_ctor_get(v_l_1971_, 2);
                v_isSharedCheck_2013_ = (!leanh::lean_is_exclusive(v_l_1971_)) as u8;
                if v_isSharedCheck_2013_ == 0 {
                    v_unused_2014_ = leanh::lean_ctor_get(v_l_1971_, 4);
                    leanh::lean_dec(v_unused_2014_);
                    v_unused_2015_ = leanh::lean_ctor_get(v_l_1971_, 3);
                    leanh::lean_dec(v_unused_2015_);
                    v_unused_2016_ = leanh::lean_ctor_get(v_l_1971_, 0);
                    leanh::lean_dec(v_unused_2016_);
                    v___x_2000_ = v_l_1971_;
                    v_isShared_2001_ = v_isSharedCheck_2013_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_inc(v_v_1998_);
                    leanh::lean_inc(v_k_1997_);
                    leanh::lean_dec(v_l_1971_);
                    v___x_2000_ = leanh::lean_box(0);
                    v_isShared_2001_ = v_isSharedCheck_2013_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2002_ = leanh::lean_unsigned_to_nat(3);
                v___x_2003_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_2001_ == 0 {
                    leanh::lean_ctor_set(v___x_2000_, 4, v_r_1972_);
                    leanh::lean_ctor_set(v___x_2000_, 3, v_r_1972_);
                    leanh::lean_ctor_set(v___x_2000_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v___x_2000_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v___x_2000_, 0, v___x_2003_);
                    v___x_2005_ = v___x_2000_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2012_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 0, v___x_2003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 3, v_r_1972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2012_, 4, v_r_1972_);
                    v___x_2005_ = v_reuseFailAlloc_2012_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1996_ == 0 {
                    leanh::lean_ctor_set(v___x_1995_, 3, v_r_1972_);
                    leanh::lean_ctor_set(v___x_1995_, 0, v___x_2003_);
                    v___x_2007_ = v___x_1995_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2011_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2003_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_k_1992_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_v_1993_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 3, v_r_1972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2011_, 4, v_r_1972_);
                    v___x_2007_ = v_reuseFailAlloc_2011_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_1872_ == 0 {
                    leanh::lean_ctor_set(v___x_1871_, 4, v___x_2007_);
                    leanh::lean_ctor_set(v___x_1871_, 3, v___x_2005_);
                    leanh::lean_ctor_set(v___x_1871_, 2, v_v_1998_);
                    leanh::lean_ctor_set(v___x_1871_, 1, v_k_1997_);
                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_2002_);
                    v___x_2009_ = v___x_1871_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_2002_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 1, v_k_1997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 2, v_v_1998_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 3, v___x_2005_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 4, v___x_2007_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2009_;
            }
            22 => {
                v___x_2027_ = leanh::lean_unsigned_to_nat(3);
                v___x_2028_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_2026_ == 0 {
                    leanh::lean_ctor_set(v___x_2025_, 4, v_l_1971_);
                    leanh::lean_ctor_set(v___x_2025_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v___x_2025_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v___x_2025_, 0, v___x_2028_);
                    v___x_2030_ = v___x_2025_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2034_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 3, v_l_1971_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2034_, 4, v_l_1971_);
                    v___x_2030_ = v_reuseFailAlloc_2034_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_1872_ == 0 {
                    leanh::lean_ctor_set(v___x_1871_, 4, v_r_2021_);
                    leanh::lean_ctor_set(v___x_1871_, 3, v___x_2030_);
                    leanh::lean_ctor_set(v___x_1871_, 2, v_v_2023_);
                    leanh::lean_ctor_set(v___x_1871_, 1, v_k_2022_);
                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_2027_);
                    v___x_2032_ = v___x_1871_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2027_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_k_2022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 2, v_v_2023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 3, v___x_2030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 4, v_r_2021_);
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
                v_tree_2062_ = leanh::lean_ctor_get(v_d_2061_, 2);
                leanh::lean_inc(v_tree_2062_);
                if leanh::lean_obj_tag(v_tree_2062_) == 0 {
                    v_k_2063_ = leanh::lean_ctor_get(v_d_2061_, 0);
                    leanh::lean_inc(v_k_2063_);
                    v_v_2064_ = leanh::lean_ctor_get(v_d_2061_, 1);
                    leanh::lean_inc(v_v_2064_);
                    leanh::lean_dec_ref(v_d_2061_);
                    v_size_2065_ = leanh::lean_ctor_get(v_tree_2062_, 0);
                    v___x_2066_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2067_ = lean_nat_mul(v___x_2066_, v_size_2065_);
                    v___x_2068_ = lean_nat_dec_lt(v___x_2067_, v_size_2052_);
                    leanh::lean_dec(v___x_2067_);
                    if v___x_2068_ == 0 {
                        leanh::lean_dec(v_l_2055_);
                        v___x_2069_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2070_ = lean_nat_add(v___x_2069_, v_size_2065_);
                        v___x_2071_ = lean_nat_add(v___x_2070_, v_size_2052_);
                        leanh::lean_dec(v___x_2070_);
                        if v_isShared_2060_ == 0 {
                            leanh::lean_ctor_set(v___x_2059_, 4, v_r_1869_);
                            leanh::lean_ctor_set(v___x_2059_, 3, v_tree_2062_);
                            leanh::lean_ctor_set(v___x_2059_, 2, v_v_2064_);
                            leanh::lean_ctor_set(v___x_2059_, 1, v_k_2063_);
                            leanh::lean_ctor_set(v___x_2059_, 0, v___x_2071_);
                            v___x_2073_ = v___x_2059_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_2074_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_k_2063_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_v_2064_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_tree_2062_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_r_1869_);
                            v___x_2073_ = v_reuseFailAlloc_2074_;
                            state = 28;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_r_2056_);
                        leanh::lean_inc(v_v_2054_);
                        leanh::lean_inc(v_k_2053_);
                        leanh::lean_inc(v_size_2052_);
                        v_isSharedCheck_2135_ = (!leanh::lean_is_exclusive(v_r_1869_)) as u8;
                        if v_isSharedCheck_2135_ == 0 {
                            v_unused_2136_ = leanh::lean_ctor_get(v_r_1869_, 4);
                            leanh::lean_dec(v_unused_2136_);
                            v_unused_2137_ = leanh::lean_ctor_get(v_r_1869_, 3);
                            leanh::lean_dec(v_unused_2137_);
                            v_unused_2138_ = leanh::lean_ctor_get(v_r_1869_, 2);
                            leanh::lean_dec(v_unused_2138_);
                            v_unused_2139_ = leanh::lean_ctor_get(v_r_1869_, 1);
                            leanh::lean_dec(v_unused_2139_);
                            v_unused_2140_ = leanh::lean_ctor_get(v_r_1869_, 0);
                            leanh::lean_dec(v_unused_2140_);
                            v___x_2076_ = v_r_1869_;
                            v_isShared_2077_ = v_isSharedCheck_2135_;
                            state = 29;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_1869_);
                            v___x_2076_ = leanh::lean_box(0);
                            v_isShared_2077_ = v_isSharedCheck_2135_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_r_2056_);
                    if leanh::lean_obj_tag(v_l_2055_) == 0 {
                        leanh::lean_inc(v_v_2054_);
                        leanh::lean_inc(v_k_2053_);
                        leanh::lean_inc(v_size_2052_);
                        v_isSharedCheck_2178_ = (!leanh::lean_is_exclusive(v_r_1869_)) as u8;
                        if v_isSharedCheck_2178_ == 0 {
                            v_unused_2179_ = leanh::lean_ctor_get(v_r_1869_, 4);
                            leanh::lean_dec(v_unused_2179_);
                            v_unused_2180_ = leanh::lean_ctor_get(v_r_1869_, 3);
                            leanh::lean_dec(v_unused_2180_);
                            v_unused_2181_ = leanh::lean_ctor_get(v_r_1869_, 2);
                            leanh::lean_dec(v_unused_2181_);
                            v_unused_2182_ = leanh::lean_ctor_get(v_r_1869_, 1);
                            leanh::lean_dec(v_unused_2182_);
                            v_unused_2183_ = leanh::lean_ctor_get(v_r_1869_, 0);
                            leanh::lean_dec(v_unused_2183_);
                            v___x_2142_ = v_r_1869_;
                            v_isShared_2143_ = v_isSharedCheck_2178_;
                            state = 38;
                            continue;
                        } else {
                            leanh::lean_dec(v_r_1869_);
                            v___x_2142_ = leanh::lean_box(0);
                            v_isShared_2143_ = v_isSharedCheck_2178_;
                            state = 38;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_r_2056_) == 0 {
                            leanh::lean_inc(v_v_2054_);
                            leanh::lean_inc(v_k_2053_);
                            v_isSharedCheck_2197_ =
                                (!leanh::lean_is_exclusive(v_r_1869_)) as u8;
                            if v_isSharedCheck_2197_ == 0 {
                                v_unused_2198_ = leanh::lean_ctor_get(v_r_1869_, 4);
                                leanh::lean_dec(v_unused_2198_);
                                v_unused_2199_ = leanh::lean_ctor_get(v_r_1869_, 3);
                                leanh::lean_dec(v_unused_2199_);
                                v_unused_2200_ = leanh::lean_ctor_get(v_r_1869_, 2);
                                leanh::lean_dec(v_unused_2200_);
                                v_unused_2201_ = leanh::lean_ctor_get(v_r_1869_, 1);
                                leanh::lean_dec(v_unused_2201_);
                                v_unused_2202_ = leanh::lean_ctor_get(v_r_1869_, 0);
                                leanh::lean_dec(v_unused_2202_);
                                v___x_2185_ = v_r_1869_;
                                v_isShared_2186_ = v_isSharedCheck_2197_;
                                state = 45;
                                continue;
                            } else {
                                leanh::lean_dec(v_r_1869_);
                                v___x_2185_ = leanh::lean_box(0);
                                v_isShared_2186_ = v_isSharedCheck_2197_;
                                state = 45;
                                continue;
                            }
                        } else {
                            v_k_2203_ = leanh::lean_ctor_get(v_d_2061_, 0);
                            leanh::lean_inc(v_k_2203_);
                            v_v_2204_ = leanh::lean_ctor_get(v_d_2061_, 1);
                            leanh::lean_inc(v_v_2204_);
                            leanh::lean_dec_ref(v_d_2061_);
                            v___x_2205_ = leanh::lean_unsigned_to_nat(2);
                            if v_isShared_2060_ == 0 {
                                leanh::lean_ctor_set(v___x_2059_, 4, v_r_1869_);
                                leanh::lean_ctor_set(v___x_2059_, 3, v_r_2056_);
                                leanh::lean_ctor_set(v___x_2059_, 2, v_v_2204_);
                                leanh::lean_ctor_set(v___x_2059_, 1, v_k_2203_);
                                leanh::lean_ctor_set(v___x_2059_, 0, v___x_2205_);
                                v___x_2207_ = v___x_2059_;
                                state = 48;
                                continue;
                            } else {
                                v_reuseFailAlloc_2208_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_k_2203_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 2, v_v_2204_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 3, v_r_2056_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 4, v_r_1869_);
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
                if leanh::lean_obj_tag(v_l_2055_) == 0 {
                    if leanh::lean_obj_tag(v_r_2056_) == 0 {
                        v_size_2078_ = leanh::lean_ctor_get(v_l_2055_, 0);
                        v_k_2079_ = leanh::lean_ctor_get(v_l_2055_, 1);
                        v_v_2080_ = leanh::lean_ctor_get(v_l_2055_, 2);
                        v_l_2081_ = leanh::lean_ctor_get(v_l_2055_, 3);
                        v_r_2082_ = leanh::lean_ctor_get(v_l_2055_, 4);
                        v_size_2083_ = leanh::lean_ctor_get(v_r_2056_, 0);
                        v___x_2084_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2085_ = lean_nat_mul(v___x_2084_, v_size_2083_);
                        v___x_2086_ = lean_nat_dec_lt(v_size_2078_, v___x_2085_);
                        leanh::lean_dec(v___x_2085_);
                        if v___x_2086_ == 0 {
                            leanh::lean_inc(v_r_2082_);
                            leanh::lean_inc(v_l_2081_);
                            leanh::lean_inc(v_v_2080_);
                            leanh::lean_inc(v_k_2079_);
                            v_isSharedCheck_2115_ =
                                (!leanh::lean_is_exclusive(v_l_2055_)) as u8;
                            if v_isSharedCheck_2115_ == 0 {
                                v_unused_2116_ = leanh::lean_ctor_get(v_l_2055_, 4);
                                leanh::lean_dec(v_unused_2116_);
                                v_unused_2117_ = leanh::lean_ctor_get(v_l_2055_, 3);
                                leanh::lean_dec(v_unused_2117_);
                                v_unused_2118_ = leanh::lean_ctor_get(v_l_2055_, 2);
                                leanh::lean_dec(v_unused_2118_);
                                v_unused_2119_ = leanh::lean_ctor_get(v_l_2055_, 1);
                                leanh::lean_dec(v_unused_2119_);
                                v_unused_2120_ = leanh::lean_ctor_get(v_l_2055_, 0);
                                leanh::lean_dec(v_unused_2120_);
                                v___x_2088_ = v_l_2055_;
                                v_isShared_2089_ = v_isSharedCheck_2115_;
                                state = 30;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_2055_);
                                v___x_2088_ = leanh::lean_box(0);
                                v_isShared_2089_ = v_isSharedCheck_2115_;
                                state = 30;
                                continue;
                            }
                        } else {
                            v___x_2121_ = leanh::lean_unsigned_to_nat(1);
                            v___x_2122_ = lean_nat_add(v___x_2121_, v_size_2065_);
                            v___x_2123_ = lean_nat_add(v___x_2122_, v_size_2052_);
                            leanh::lean_dec(v_size_2052_);
                            v___x_2124_ = lean_nat_add(v___x_2122_, v_size_2078_);
                            leanh::lean_dec(v___x_2122_);
                            if v_isShared_2077_ == 0 {
                                leanh::lean_ctor_set(v___x_2076_, 4, v_l_2055_);
                                leanh::lean_ctor_set(v___x_2076_, 3, v_tree_2062_);
                                leanh::lean_ctor_set(v___x_2076_, 2, v_v_2064_);
                                leanh::lean_ctor_set(v___x_2076_, 1, v_k_2063_);
                                leanh::lean_ctor_set(v___x_2076_, 0, v___x_2124_);
                                v___x_2126_ = v___x_2076_;
                                state = 36;
                                continue;
                            } else {
                                v_reuseFailAlloc_2130_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2124_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_k_2063_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 2, v_v_2064_);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_2130_,
                                    3,
                                    v_tree_2062_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 4, v_l_2055_);
                                v___x_2126_ = v_reuseFailAlloc_2130_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_2055_, 5);
                        leanh::lean_del_object(v___x_2076_);
                        leanh::lean_dec(v_v_2064_);
                        leanh::lean_dec_ref_known(v_tree_2062_, 5);
                        leanh::lean_dec(v_k_2063_);
                        leanh::lean_del_object(v___x_2059_);
                        leanh::lean_dec(v_v_2054_);
                        leanh::lean_dec(v_k_2053_);
                        leanh::lean_dec(v_size_2052_);
                        v___x_2131_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__7);
                        v___x_2132_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2131_);
                        return v___x_2132_;
                    }
                } else {
                    leanh::lean_del_object(v___x_2076_);
                    leanh::lean_dec(v_v_2064_);
                    leanh::lean_dec_ref_known(v_tree_2062_, 5);
                    leanh::lean_dec(v_k_2063_);
                    leanh::lean_del_object(v___x_2059_);
                    leanh::lean_dec(v_r_2056_);
                    leanh::lean_dec(v_v_2054_);
                    leanh::lean_dec(v_k_2053_);
                    leanh::lean_dec(v_size_2052_);
                    v___x_2133_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__8);
                    v___x_2134_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2133_);
                    return v___x_2134_;
                }
            }
            30 => {
                v___x_2090_ = leanh::lean_unsigned_to_nat(1);
                v___x_2091_ = lean_nat_add(v___x_2090_, v_size_2065_);
                v___x_2092_ = lean_nat_add(v___x_2091_, v_size_2052_);
                leanh::lean_dec(v_size_2052_);
                if leanh::lean_obj_tag(v_l_2081_) == 0 {
                    v_size_2113_ = leanh::lean_ctor_get(v_l_2081_, 0);
                    leanh::lean_inc(v_size_2113_);
                    v___y_2105_ = v_size_2113_;
                    state = 34;
                    continue;
                } else {
                    v___x_2114_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2105_ = v___x_2114_;
                    state = 34;
                    continue;
                }
            }
            31 => {
                v___x_2097_ = lean_nat_add(v___y_2095_, v___y_2096_);
                leanh::lean_dec(v___y_2096_);
                leanh::lean_dec(v___y_2095_);
                if v_isShared_2089_ == 0 {
                    leanh::lean_ctor_set(v___x_2088_, 4, v_r_2056_);
                    leanh::lean_ctor_set(v___x_2088_, 3, v_r_2082_);
                    leanh::lean_ctor_set(v___x_2088_, 2, v_v_2054_);
                    leanh::lean_ctor_set(v___x_2088_, 1, v_k_2053_);
                    leanh::lean_ctor_set(v___x_2088_, 0, v___x_2097_);
                    v___x_2099_ = v___x_2088_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2103_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_k_2053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_v_2054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 3, v_r_2082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_r_2056_);
                    v___x_2099_ = v_reuseFailAlloc_2103_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2077_ == 0 {
                    leanh::lean_ctor_set(v___x_2076_, 4, v___x_2099_);
                    leanh::lean_ctor_set(v___x_2076_, 3, v___y_2094_);
                    leanh::lean_ctor_set(v___x_2076_, 2, v_v_2080_);
                    leanh::lean_ctor_set(v___x_2076_, 1, v_k_2079_);
                    leanh::lean_ctor_set(v___x_2076_, 0, v___x_2092_);
                    v___x_2101_ = v___x_2076_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2102_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 0, v___x_2092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 1, v_k_2079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_v_2080_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 3, v___y_2094_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2102_, 4, v___x_2099_);
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
                leanh::lean_dec(v___y_2105_);
                leanh::lean_dec(v___x_2091_);
                if v_isShared_2060_ == 0 {
                    leanh::lean_ctor_set(v___x_2059_, 4, v_l_2081_);
                    leanh::lean_ctor_set(v___x_2059_, 3, v_tree_2062_);
                    leanh::lean_ctor_set(v___x_2059_, 2, v_v_2064_);
                    leanh::lean_ctor_set(v___x_2059_, 1, v_k_2063_);
                    leanh::lean_ctor_set(v___x_2059_, 0, v___x_2106_);
                    v___x_2108_ = v___x_2059_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2112_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2106_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_k_2063_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_v_2064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_tree_2062_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_l_2081_);
                    v___x_2108_ = v_reuseFailAlloc_2112_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___x_2109_ = lean_nat_add(v___x_2090_, v_size_2083_);
                if leanh::lean_obj_tag(v_r_2082_) == 0 {
                    v_size_2110_ = leanh::lean_ctor_get(v_r_2082_, 0);
                    leanh::lean_inc(v_size_2110_);
                    v___y_2094_ = v___x_2108_;
                    v___y_2095_ = v___x_2109_;
                    v___y_2096_ = v_size_2110_;
                    state = 31;
                    continue;
                } else {
                    v___x_2111_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2094_ = v___x_2108_;
                    v___y_2095_ = v___x_2109_;
                    v___y_2096_ = v___x_2111_;
                    state = 31;
                    continue;
                }
            }
            36 => {
                if v_isShared_2060_ == 0 {
                    leanh::lean_ctor_set(v___x_2059_, 4, v_r_2056_);
                    leanh::lean_ctor_set(v___x_2059_, 3, v___x_2126_);
                    leanh::lean_ctor_set(v___x_2059_, 2, v_v_2054_);
                    leanh::lean_ctor_set(v___x_2059_, 1, v_k_2053_);
                    leanh::lean_ctor_set(v___x_2059_, 0, v___x_2123_);
                    v___x_2128_ = v___x_2059_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2129_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2123_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 1, v_k_2053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 2, v_v_2054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 3, v___x_2126_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2129_, 4, v_r_2056_);
                    v___x_2128_ = v_reuseFailAlloc_2129_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2128_;
            }
            38 => {
                if leanh::lean_obj_tag(v_r_2056_) == 0 {
                    v_k_2144_ = leanh::lean_ctor_get(v_d_2061_, 0);
                    leanh::lean_inc(v_k_2144_);
                    v_v_2145_ = leanh::lean_ctor_get(v_d_2061_, 1);
                    leanh::lean_inc(v_v_2145_);
                    leanh::lean_dec_ref(v_d_2061_);
                    v_size_2146_ = leanh::lean_ctor_get(v_l_2055_, 0);
                    v___x_2147_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2148_ = lean_nat_add(v___x_2147_, v_size_2052_);
                    leanh::lean_dec(v_size_2052_);
                    v___x_2149_ = lean_nat_add(v___x_2147_, v_size_2146_);
                    if v_isShared_2143_ == 0 {
                        leanh::lean_ctor_set(v___x_2142_, 4, v_l_2055_);
                        leanh::lean_ctor_set(v___x_2142_, 3, v_tree_2062_);
                        leanh::lean_ctor_set(v___x_2142_, 2, v_v_2145_);
                        leanh::lean_ctor_set(v___x_2142_, 1, v_k_2144_);
                        leanh::lean_ctor_set(v___x_2142_, 0, v___x_2149_);
                        v___x_2151_ = v___x_2142_;
                        state = 39;
                        continue;
                    } else {
                        v_reuseFailAlloc_2155_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2149_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_k_2144_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_v_2145_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_tree_2062_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2155_, 4, v_l_2055_);
                        v___x_2151_ = v_reuseFailAlloc_2155_;
                        state = 39;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_size_2052_);
                    v_k_2156_ = leanh::lean_ctor_get(v_d_2061_, 0);
                    leanh::lean_inc(v_k_2156_);
                    v_v_2157_ = leanh::lean_ctor_get(v_d_2061_, 1);
                    leanh::lean_inc(v_v_2157_);
                    leanh::lean_dec_ref(v_d_2061_);
                    v_k_2158_ = leanh::lean_ctor_get(v_l_2055_, 1);
                    v_v_2159_ = leanh::lean_ctor_get(v_l_2055_, 2);
                    v_isSharedCheck_2174_ = (!leanh::lean_is_exclusive(v_l_2055_)) as u8;
                    if v_isSharedCheck_2174_ == 0 {
                        v_unused_2175_ = leanh::lean_ctor_get(v_l_2055_, 4);
                        leanh::lean_dec(v_unused_2175_);
                        v_unused_2176_ = leanh::lean_ctor_get(v_l_2055_, 3);
                        leanh::lean_dec(v_unused_2176_);
                        v_unused_2177_ = leanh::lean_ctor_get(v_l_2055_, 0);
                        leanh::lean_dec(v_unused_2177_);
                        v___x_2161_ = v_l_2055_;
                        v_isShared_2162_ = v_isSharedCheck_2174_;
                        state = 41;
                        continue;
                    } else {
                        leanh::lean_inc(v_v_2159_);
                        leanh::lean_inc(v_k_2158_);
                        leanh::lean_dec(v_l_2055_);
                        v___x_2161_ = leanh::lean_box(0);
                        v_isShared_2162_ = v_isSharedCheck_2174_;
                        state = 41;
                        continue;
                    }
                }
            }
            39 => {
                if v_isShared_2060_ == 0 {
                    leanh::lean_ctor_set(v___x_2059_, 4, v_r_2056_);
                    leanh::lean_ctor_set(v___x_2059_, 3, v___x_2151_);
                    leanh::lean_ctor_set(v___x_2059_, 2, v_v_2054_);
                    leanh::lean_ctor_set(v___x_2059_, 1, v_k_2053_);
                    leanh::lean_ctor_set(v___x_2059_, 0, v___x_2148_);
                    v___x_2153_ = v___x_2059_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2154_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 0, v___x_2148_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 1, v_k_2053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 2, v_v_2054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 3, v___x_2151_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2154_, 4, v_r_2056_);
                    v___x_2153_ = v_reuseFailAlloc_2154_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2153_;
            }
            41 => {
                v___x_2163_ = leanh::lean_unsigned_to_nat(3);
                v___x_2164_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_2162_ == 0 {
                    leanh::lean_ctor_set(v___x_2161_, 4, v_r_2056_);
                    leanh::lean_ctor_set(v___x_2161_, 3, v_r_2056_);
                    leanh::lean_ctor_set(v___x_2161_, 2, v_v_2157_);
                    leanh::lean_ctor_set(v___x_2161_, 1, v_k_2156_);
                    leanh::lean_ctor_set(v___x_2161_, 0, v___x_2164_);
                    v___x_2166_ = v___x_2161_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2173_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_k_2156_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 2, v_v_2157_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 3, v_r_2056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2173_, 4, v_r_2056_);
                    v___x_2166_ = v_reuseFailAlloc_2173_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                if v_isShared_2143_ == 0 {
                    leanh::lean_ctor_set(v___x_2142_, 3, v_r_2056_);
                    leanh::lean_ctor_set(v___x_2142_, 0, v___x_2164_);
                    v___x_2168_ = v___x_2142_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2164_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_k_2053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_v_2054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_r_2056_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_r_2056_);
                    v___x_2168_ = v_reuseFailAlloc_2172_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                if v_isShared_2060_ == 0 {
                    leanh::lean_ctor_set(v___x_2059_, 4, v___x_2168_);
                    leanh::lean_ctor_set(v___x_2059_, 3, v___x_2166_);
                    leanh::lean_ctor_set(v___x_2059_, 2, v_v_2159_);
                    leanh::lean_ctor_set(v___x_2059_, 1, v_k_2158_);
                    leanh::lean_ctor_set(v___x_2059_, 0, v___x_2163_);
                    v___x_2170_ = v___x_2059_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2163_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_k_2158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 2, v_v_2159_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 3, v___x_2166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 4, v___x_2168_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_2170_;
            }
            45 => {
                v_k_2187_ = leanh::lean_ctor_get(v_d_2061_, 0);
                leanh::lean_inc(v_k_2187_);
                v_v_2188_ = leanh::lean_ctor_get(v_d_2061_, 1);
                leanh::lean_inc(v_v_2188_);
                leanh::lean_dec_ref(v_d_2061_);
                v___x_2189_ = leanh::lean_unsigned_to_nat(3);
                v___x_2190_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_2186_ == 0 {
                    leanh::lean_ctor_set(v___x_2185_, 4, v_l_2055_);
                    leanh::lean_ctor_set(v___x_2185_, 2, v_v_2188_);
                    leanh::lean_ctor_set(v___x_2185_, 1, v_k_2187_);
                    leanh::lean_ctor_set(v___x_2185_, 0, v___x_2190_);
                    v___x_2192_ = v___x_2185_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_2196_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2190_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_k_2187_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 2, v_v_2188_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 3, v_l_2055_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2196_, 4, v_l_2055_);
                    v___x_2192_ = v_reuseFailAlloc_2196_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                if v_isShared_2060_ == 0 {
                    leanh::lean_ctor_set(v___x_2059_, 4, v_r_2056_);
                    leanh::lean_ctor_set(v___x_2059_, 3, v___x_2192_);
                    leanh::lean_ctor_set(v___x_2059_, 2, v_v_2054_);
                    leanh::lean_ctor_set(v___x_2059_, 1, v_k_2053_);
                    leanh::lean_ctor_set(v___x_2059_, 0, v___x_2189_);
                    v___x_2194_ = v___x_2059_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_2195_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 0, v___x_2189_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_k_2053_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 2, v_v_2054_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 3, v___x_2192_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2195_, 4, v_r_2056_);
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
                v_tree_2219_ = leanh::lean_ctor_get(v_d_2218_, 2);
                leanh::lean_inc(v_tree_2219_);
                if leanh::lean_obj_tag(v_tree_2219_) == 0 {
                    v_k_2220_ = leanh::lean_ctor_get(v_d_2218_, 0);
                    leanh::lean_inc(v_k_2220_);
                    v_v_2221_ = leanh::lean_ctor_get(v_d_2218_, 1);
                    leanh::lean_inc(v_v_2221_);
                    leanh::lean_dec_ref(v_d_2218_);
                    v_size_2222_ = leanh::lean_ctor_get(v_tree_2219_, 0);
                    v___x_2223_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2224_ = lean_nat_mul(v___x_2223_, v_size_2222_);
                    v___x_2225_ = lean_nat_dec_lt(v___x_2224_, v_size_2047_);
                    leanh::lean_dec(v___x_2224_);
                    if v___x_2225_ == 0 {
                        leanh::lean_dec(v_r_2051_);
                        v___x_2226_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2227_ = lean_nat_add(v___x_2226_, v_size_2047_);
                        v___x_2228_ = lean_nat_add(v___x_2227_, v_size_2222_);
                        leanh::lean_dec(v___x_2227_);
                        if v_isShared_2217_ == 0 {
                            leanh::lean_ctor_set(v___x_2216_, 4, v_tree_2219_);
                            leanh::lean_ctor_set(v___x_2216_, 3, v_l_1868_);
                            leanh::lean_ctor_set(v___x_2216_, 2, v_v_2221_);
                            leanh::lean_ctor_set(v___x_2216_, 1, v_k_2220_);
                            leanh::lean_ctor_set(v___x_2216_, 0, v___x_2228_);
                            v___x_2230_ = v___x_2216_;
                            state = 50;
                            continue;
                        } else {
                            v_reuseFailAlloc_2231_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 0, v___x_2228_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_k_2220_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 2, v_v_2221_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 3, v_l_1868_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 4, v_tree_2219_);
                            v___x_2230_ = v_reuseFailAlloc_2231_;
                            state = 50;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_l_2050_);
                        leanh::lean_inc(v_v_2049_);
                        leanh::lean_inc(v_k_2048_);
                        leanh::lean_inc(v_size_2047_);
                        v_isSharedCheck_2303_ = (!leanh::lean_is_exclusive(v_l_1868_)) as u8;
                        if v_isSharedCheck_2303_ == 0 {
                            v_unused_2304_ = leanh::lean_ctor_get(v_l_1868_, 4);
                            leanh::lean_dec(v_unused_2304_);
                            v_unused_2305_ = leanh::lean_ctor_get(v_l_1868_, 3);
                            leanh::lean_dec(v_unused_2305_);
                            v_unused_2306_ = leanh::lean_ctor_get(v_l_1868_, 2);
                            leanh::lean_dec(v_unused_2306_);
                            v_unused_2307_ = leanh::lean_ctor_get(v_l_1868_, 1);
                            leanh::lean_dec(v_unused_2307_);
                            v_unused_2308_ = leanh::lean_ctor_get(v_l_1868_, 0);
                            leanh::lean_dec(v_unused_2308_);
                            v___x_2233_ = v_l_1868_;
                            v_isShared_2234_ = v_isSharedCheck_2303_;
                            state = 51;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_1868_);
                            v___x_2233_ = leanh::lean_box(0);
                            v_isShared_2234_ = v_isSharedCheck_2303_;
                            state = 51;
                            continue;
                        }
                    }
                } else {
                    if leanh::lean_obj_tag(v_l_2050_) == 0 {
                        leanh::lean_inc_ref(v_l_2050_);
                        leanh::lean_inc(v_v_2049_);
                        leanh::lean_inc(v_k_2048_);
                        leanh::lean_inc(v_size_2047_);
                        v_isSharedCheck_2334_ = (!leanh::lean_is_exclusive(v_l_1868_)) as u8;
                        if v_isSharedCheck_2334_ == 0 {
                            v_unused_2335_ = leanh::lean_ctor_get(v_l_1868_, 4);
                            leanh::lean_dec(v_unused_2335_);
                            v_unused_2336_ = leanh::lean_ctor_get(v_l_1868_, 3);
                            leanh::lean_dec(v_unused_2336_);
                            v_unused_2337_ = leanh::lean_ctor_get(v_l_1868_, 2);
                            leanh::lean_dec(v_unused_2337_);
                            v_unused_2338_ = leanh::lean_ctor_get(v_l_1868_, 1);
                            leanh::lean_dec(v_unused_2338_);
                            v_unused_2339_ = leanh::lean_ctor_get(v_l_1868_, 0);
                            leanh::lean_dec(v_unused_2339_);
                            v___x_2310_ = v_l_1868_;
                            v_isShared_2311_ = v_isSharedCheck_2334_;
                            state = 61;
                            continue;
                        } else {
                            leanh::lean_dec(v_l_1868_);
                            v___x_2310_ = leanh::lean_box(0);
                            v_isShared_2311_ = v_isSharedCheck_2334_;
                            state = 61;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v_r_2051_) == 0 {
                            leanh::lean_inc(v_l_2050_);
                            leanh::lean_inc(v_v_2049_);
                            leanh::lean_inc(v_k_2048_);
                            v_isSharedCheck_2365_ =
                                (!leanh::lean_is_exclusive(v_l_1868_)) as u8;
                            if v_isSharedCheck_2365_ == 0 {
                                v_unused_2366_ = leanh::lean_ctor_get(v_l_1868_, 4);
                                leanh::lean_dec(v_unused_2366_);
                                v_unused_2367_ = leanh::lean_ctor_get(v_l_1868_, 3);
                                leanh::lean_dec(v_unused_2367_);
                                v_unused_2368_ = leanh::lean_ctor_get(v_l_1868_, 2);
                                leanh::lean_dec(v_unused_2368_);
                                v_unused_2369_ = leanh::lean_ctor_get(v_l_1868_, 1);
                                leanh::lean_dec(v_unused_2369_);
                                v_unused_2370_ = leanh::lean_ctor_get(v_l_1868_, 0);
                                leanh::lean_dec(v_unused_2370_);
                                v___x_2341_ = v_l_1868_;
                                v_isShared_2342_ = v_isSharedCheck_2365_;
                                state = 66;
                                continue;
                            } else {
                                leanh::lean_dec(v_l_1868_);
                                v___x_2341_ = leanh::lean_box(0);
                                v_isShared_2342_ = v_isSharedCheck_2365_;
                                state = 66;
                                continue;
                            }
                        } else {
                            v_k_2371_ = leanh::lean_ctor_get(v_d_2218_, 0);
                            leanh::lean_inc(v_k_2371_);
                            v_v_2372_ = leanh::lean_ctor_get(v_d_2218_, 1);
                            leanh::lean_inc(v_v_2372_);
                            leanh::lean_dec_ref(v_d_2218_);
                            v___x_2373_ = leanh::lean_unsigned_to_nat(2);
                            if v_isShared_2217_ == 0 {
                                leanh::lean_ctor_set(v___x_2216_, 4, v_r_2051_);
                                leanh::lean_ctor_set(v___x_2216_, 3, v_l_1868_);
                                leanh::lean_ctor_set(v___x_2216_, 2, v_v_2372_);
                                leanh::lean_ctor_set(v___x_2216_, 1, v_k_2371_);
                                leanh::lean_ctor_set(v___x_2216_, 0, v___x_2373_);
                                v___x_2375_ = v___x_2216_;
                                state = 71;
                                continue;
                            } else {
                                v_reuseFailAlloc_2376_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_k_2371_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 2, v_v_2372_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 3, v_l_1868_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 4, v_r_2051_);
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
                if leanh::lean_obj_tag(v_l_2050_) == 0 {
                    if leanh::lean_obj_tag(v_r_2051_) == 0 {
                        v_size_2235_ = leanh::lean_ctor_get(v_l_2050_, 0);
                        v_size_2236_ = leanh::lean_ctor_get(v_r_2051_, 0);
                        v_k_2237_ = leanh::lean_ctor_get(v_r_2051_, 1);
                        v_v_2238_ = leanh::lean_ctor_get(v_r_2051_, 2);
                        v_l_2239_ = leanh::lean_ctor_get(v_r_2051_, 3);
                        v_r_2240_ = leanh::lean_ctor_get(v_r_2051_, 4);
                        v___x_2241_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2242_ = lean_nat_mul(v___x_2241_, v_size_2235_);
                        v___x_2243_ = lean_nat_dec_lt(v_size_2236_, v___x_2242_);
                        leanh::lean_dec(v___x_2242_);
                        if v___x_2243_ == 0 {
                            leanh::lean_inc(v_r_2240_);
                            leanh::lean_inc(v_l_2239_);
                            leanh::lean_inc(v_v_2238_);
                            leanh::lean_inc(v_k_2237_);
                            leanh::lean_del_object(v___x_2233_);
                            v_isSharedCheck_2282_ =
                                (!leanh::lean_is_exclusive(v_r_2051_)) as u8;
                            if v_isSharedCheck_2282_ == 0 {
                                v_unused_2283_ = leanh::lean_ctor_get(v_r_2051_, 4);
                                leanh::lean_dec(v_unused_2283_);
                                v_unused_2284_ = leanh::lean_ctor_get(v_r_2051_, 3);
                                leanh::lean_dec(v_unused_2284_);
                                v_unused_2285_ = leanh::lean_ctor_get(v_r_2051_, 2);
                                leanh::lean_dec(v_unused_2285_);
                                v_unused_2286_ = leanh::lean_ctor_get(v_r_2051_, 1);
                                leanh::lean_dec(v_unused_2286_);
                                v_unused_2287_ = leanh::lean_ctor_get(v_r_2051_, 0);
                                leanh::lean_dec(v_unused_2287_);
                                v___x_2245_ = v_r_2051_;
                                v_isShared_2246_ = v_isSharedCheck_2282_;
                                state = 52;
                                continue;
                            } else {
                                leanh::lean_dec(v_r_2051_);
                                v___x_2245_ = leanh::lean_box(0);
                                v_isShared_2246_ = v_isSharedCheck_2282_;
                                state = 52;
                                continue;
                            }
                        } else {
                            v___x_2288_ = leanh::lean_unsigned_to_nat(1);
                            v___x_2289_ = lean_nat_add(v___x_2288_, v_size_2047_);
                            leanh::lean_dec(v_size_2047_);
                            v___x_2290_ = lean_nat_add(v___x_2289_, v_size_2222_);
                            leanh::lean_dec(v___x_2289_);
                            v___x_2291_ = lean_nat_add(v___x_2288_, v_size_2222_);
                            v___x_2292_ = lean_nat_add(v___x_2291_, v_size_2236_);
                            leanh::lean_dec(v___x_2291_);
                            if v_isShared_2217_ == 0 {
                                leanh::lean_ctor_set(v___x_2216_, 4, v_tree_2219_);
                                leanh::lean_ctor_set(v___x_2216_, 3, v_r_2051_);
                                leanh::lean_ctor_set(v___x_2216_, 2, v_v_2221_);
                                leanh::lean_ctor_set(v___x_2216_, 1, v_k_2220_);
                                leanh::lean_ctor_set(v___x_2216_, 0, v___x_2292_);
                                v___x_2294_ = v___x_2216_;
                                state = 59;
                                continue;
                            } else {
                                v_reuseFailAlloc_2298_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2292_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_k_2220_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 2, v_v_2221_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2298_, 3, v_r_2051_);
                                leanh::lean_ctor_set(
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
                        leanh::lean_dec_ref_known(v_l_2050_, 5);
                        leanh::lean_del_object(v___x_2233_);
                        leanh::lean_dec(v_v_2221_);
                        leanh::lean_dec(v_k_2220_);
                        leanh::lean_dec_ref_known(v_tree_2219_, 5);
                        leanh::lean_del_object(v___x_2216_);
                        leanh::lean_dec(v_v_2049_);
                        leanh::lean_dec(v_k_2048_);
                        leanh::lean_dec(v_size_2047_);
                        v___x_2299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3);
                        v___x_2300_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2299_);
                        return v___x_2300_;
                    }
                } else {
                    leanh::lean_del_object(v___x_2233_);
                    leanh::lean_dec(v_v_2221_);
                    leanh::lean_dec_ref_known(v_tree_2219_, 5);
                    leanh::lean_dec(v_k_2220_);
                    leanh::lean_del_object(v___x_2216_);
                    leanh::lean_dec(v_r_2051_);
                    leanh::lean_dec(v_v_2049_);
                    leanh::lean_dec(v_k_2048_);
                    leanh::lean_dec(v_size_2047_);
                    v___x_2301_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4);
                    v___x_2302_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2301_);
                    return v___x_2302_;
                }
            }
            52 => {
                v___x_2247_ = leanh::lean_unsigned_to_nat(1);
                v___x_2248_ = lean_nat_add(v___x_2247_, v_size_2047_);
                leanh::lean_dec(v_size_2047_);
                v___x_2249_ = lean_nat_add(v___x_2248_, v_size_2222_);
                leanh::lean_dec(v___x_2248_);
                v___x_2270_ = lean_nat_add(v___x_2247_, v_size_2235_);
                if leanh::lean_obj_tag(v_l_2239_) == 0 {
                    v_size_2280_ = leanh::lean_ctor_get(v_l_2239_, 0);
                    leanh::lean_inc(v_size_2280_);
                    v___y_2272_ = v_size_2280_;
                    state = 57;
                    continue;
                } else {
                    v___x_2281_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2272_ = v___x_2281_;
                    state = 57;
                    continue;
                }
            }
            53 => {
                v___x_2254_ = lean_nat_add(v___y_2252_, v___y_2253_);
                leanh::lean_dec(v___y_2253_);
                leanh::lean_dec(v___y_2252_);
                leanh::lean_inc_ref(v_tree_2219_);
                if v_isShared_2246_ == 0 {
                    leanh::lean_ctor_set(v___x_2245_, 4, v_tree_2219_);
                    leanh::lean_ctor_set(v___x_2245_, 3, v_r_2240_);
                    leanh::lean_ctor_set(v___x_2245_, 2, v_v_2221_);
                    leanh::lean_ctor_set(v___x_2245_, 1, v_k_2220_);
                    leanh::lean_ctor_set(v___x_2245_, 0, v___x_2254_);
                    v___x_2256_ = v___x_2245_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2254_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_k_2220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 2, v_v_2221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 3, v_r_2240_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2269_, 4, v_tree_2219_);
                    v___x_2256_ = v_reuseFailAlloc_2269_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                v_isSharedCheck_2263_ = (!leanh::lean_is_exclusive(v_tree_2219_)) as u8;
                if v_isSharedCheck_2263_ == 0 {
                    v_unused_2264_ = leanh::lean_ctor_get(v_tree_2219_, 4);
                    leanh::lean_dec(v_unused_2264_);
                    v_unused_2265_ = leanh::lean_ctor_get(v_tree_2219_, 3);
                    leanh::lean_dec(v_unused_2265_);
                    v_unused_2266_ = leanh::lean_ctor_get(v_tree_2219_, 2);
                    leanh::lean_dec(v_unused_2266_);
                    v_unused_2267_ = leanh::lean_ctor_get(v_tree_2219_, 1);
                    leanh::lean_dec(v_unused_2267_);
                    v_unused_2268_ = leanh::lean_ctor_get(v_tree_2219_, 0);
                    leanh::lean_dec(v_unused_2268_);
                    v___x_2258_ = v_tree_2219_;
                    v_isShared_2259_ = v_isSharedCheck_2263_;
                    state = 55;
                    continue;
                } else {
                    leanh::lean_dec(v_tree_2219_);
                    v___x_2258_ = leanh::lean_box(0);
                    v_isShared_2259_ = v_isSharedCheck_2263_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                if v_isShared_2259_ == 0 {
                    leanh::lean_ctor_set(v___x_2258_, 4, v___x_2256_);
                    leanh::lean_ctor_set(v___x_2258_, 3, v___y_2251_);
                    leanh::lean_ctor_set(v___x_2258_, 2, v_v_2238_);
                    leanh::lean_ctor_set(v___x_2258_, 1, v_k_2237_);
                    leanh::lean_ctor_set(v___x_2258_, 0, v___x_2249_);
                    v___x_2261_ = v___x_2258_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_2262_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2249_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 1, v_k_2237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 2, v_v_2238_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 3, v___y_2251_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2262_, 4, v___x_2256_);
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
                leanh::lean_dec(v___y_2272_);
                leanh::lean_dec(v___x_2270_);
                if v_isShared_2217_ == 0 {
                    leanh::lean_ctor_set(v___x_2216_, 4, v_l_2239_);
                    leanh::lean_ctor_set(v___x_2216_, 3, v_l_2050_);
                    leanh::lean_ctor_set(v___x_2216_, 2, v_v_2049_);
                    leanh::lean_ctor_set(v___x_2216_, 1, v_k_2048_);
                    leanh::lean_ctor_set(v___x_2216_, 0, v___x_2273_);
                    v___x_2275_ = v___x_2216_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_2279_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2273_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 1, v_k_2048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 2, v_v_2049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 3, v_l_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2279_, 4, v_l_2239_);
                    v___x_2275_ = v_reuseFailAlloc_2279_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                v___x_2276_ = lean_nat_add(v___x_2247_, v_size_2222_);
                if leanh::lean_obj_tag(v_r_2240_) == 0 {
                    v_size_2277_ = leanh::lean_ctor_get(v_r_2240_, 0);
                    leanh::lean_inc(v_size_2277_);
                    v___y_2251_ = v___x_2275_;
                    v___y_2252_ = v___x_2276_;
                    v___y_2253_ = v_size_2277_;
                    state = 53;
                    continue;
                } else {
                    v___x_2278_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2251_ = v___x_2275_;
                    v___y_2252_ = v___x_2276_;
                    v___y_2253_ = v___x_2278_;
                    state = 53;
                    continue;
                }
            }
            59 => {
                if v_isShared_2234_ == 0 {
                    leanh::lean_ctor_set(v___x_2233_, 4, v___x_2294_);
                    leanh::lean_ctor_set(v___x_2233_, 0, v___x_2290_);
                    v___x_2296_ = v___x_2233_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_2297_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2290_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_k_2048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 2, v_v_2049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 3, v_l_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2297_, 4, v___x_2294_);
                    v___x_2296_ = v_reuseFailAlloc_2297_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_2296_;
            }
            61 => {
                if leanh::lean_obj_tag(v_r_2051_) == 0 {
                    v_k_2312_ = leanh::lean_ctor_get(v_d_2218_, 0);
                    leanh::lean_inc(v_k_2312_);
                    v_v_2313_ = leanh::lean_ctor_get(v_d_2218_, 1);
                    leanh::lean_inc(v_v_2313_);
                    leanh::lean_dec_ref(v_d_2218_);
                    v_size_2314_ = leanh::lean_ctor_get(v_r_2051_, 0);
                    v___x_2315_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2316_ = lean_nat_add(v___x_2315_, v_size_2047_);
                    leanh::lean_dec(v_size_2047_);
                    v___x_2317_ = lean_nat_add(v___x_2315_, v_size_2314_);
                    if v_isShared_2217_ == 0 {
                        leanh::lean_ctor_set(v___x_2216_, 4, v_tree_2219_);
                        leanh::lean_ctor_set(v___x_2216_, 3, v_r_2051_);
                        leanh::lean_ctor_set(v___x_2216_, 2, v_v_2313_);
                        leanh::lean_ctor_set(v___x_2216_, 1, v_k_2312_);
                        leanh::lean_ctor_set(v___x_2216_, 0, v___x_2317_);
                        v___x_2319_ = v___x_2216_;
                        state = 62;
                        continue;
                    } else {
                        v_reuseFailAlloc_2323_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 0, v___x_2317_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 1, v_k_2312_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 2, v_v_2313_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 3, v_r_2051_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2323_, 4, v_tree_2219_);
                        v___x_2319_ = v_reuseFailAlloc_2323_;
                        state = 62;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_size_2047_);
                    v_k_2324_ = leanh::lean_ctor_get(v_d_2218_, 0);
                    leanh::lean_inc(v_k_2324_);
                    v_v_2325_ = leanh::lean_ctor_get(v_d_2218_, 1);
                    leanh::lean_inc(v_v_2325_);
                    leanh::lean_dec_ref(v_d_2218_);
                    v___x_2326_ = leanh::lean_unsigned_to_nat(3);
                    v___x_2327_ = leanh::lean_unsigned_to_nat(1);
                    if v_isShared_2217_ == 0 {
                        leanh::lean_ctor_set(v___x_2216_, 4, v_r_2051_);
                        leanh::lean_ctor_set(v___x_2216_, 3, v_r_2051_);
                        leanh::lean_ctor_set(v___x_2216_, 2, v_v_2325_);
                        leanh::lean_ctor_set(v___x_2216_, 1, v_k_2324_);
                        leanh::lean_ctor_set(v___x_2216_, 0, v___x_2327_);
                        v___x_2329_ = v___x_2216_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_2333_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 0, v___x_2327_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_k_2324_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_v_2325_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_r_2051_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 4, v_r_2051_);
                        v___x_2329_ = v_reuseFailAlloc_2333_;
                        state = 64;
                        continue;
                    }
                }
            }
            62 => {
                if v_isShared_2311_ == 0 {
                    leanh::lean_ctor_set(v___x_2310_, 4, v___x_2319_);
                    leanh::lean_ctor_set(v___x_2310_, 0, v___x_2316_);
                    v___x_2321_ = v___x_2310_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_2322_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 0, v___x_2316_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 1, v_k_2048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 2, v_v_2049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 3, v_l_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2322_, 4, v___x_2319_);
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
                    leanh::lean_ctor_set(v___x_2310_, 4, v___x_2329_);
                    leanh::lean_ctor_set(v___x_2310_, 0, v___x_2326_);
                    v___x_2331_ = v___x_2310_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_2332_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2326_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 1, v_k_2048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 2, v_v_2049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 3, v_l_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 4, v___x_2329_);
                    v___x_2331_ = v_reuseFailAlloc_2332_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_2331_;
            }
            66 => {
                v_k_2343_ = leanh::lean_ctor_get(v_d_2218_, 0);
                leanh::lean_inc(v_k_2343_);
                v_v_2344_ = leanh::lean_ctor_get(v_d_2218_, 1);
                leanh::lean_inc(v_v_2344_);
                leanh::lean_dec_ref(v_d_2218_);
                v_k_2345_ = leanh::lean_ctor_get(v_r_2051_, 1);
                v_v_2346_ = leanh::lean_ctor_get(v_r_2051_, 2);
                v_isSharedCheck_2361_ = (!leanh::lean_is_exclusive(v_r_2051_)) as u8;
                if v_isSharedCheck_2361_ == 0 {
                    v_unused_2362_ = leanh::lean_ctor_get(v_r_2051_, 4);
                    leanh::lean_dec(v_unused_2362_);
                    v_unused_2363_ = leanh::lean_ctor_get(v_r_2051_, 3);
                    leanh::lean_dec(v_unused_2363_);
                    v_unused_2364_ = leanh::lean_ctor_get(v_r_2051_, 0);
                    leanh::lean_dec(v_unused_2364_);
                    v___x_2348_ = v_r_2051_;
                    v_isShared_2349_ = v_isSharedCheck_2361_;
                    state = 67;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2346_);
                    leanh::lean_inc(v_k_2345_);
                    leanh::lean_dec(v_r_2051_);
                    v___x_2348_ = leanh::lean_box(0);
                    v_isShared_2349_ = v_isSharedCheck_2361_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                v___x_2350_ = leanh::lean_unsigned_to_nat(3);
                v___x_2351_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_2349_ == 0 {
                    leanh::lean_ctor_set(v___x_2348_, 4, v_l_2050_);
                    leanh::lean_ctor_set(v___x_2348_, 3, v_l_2050_);
                    leanh::lean_ctor_set(v___x_2348_, 2, v_v_2049_);
                    leanh::lean_ctor_set(v___x_2348_, 1, v_k_2048_);
                    leanh::lean_ctor_set(v___x_2348_, 0, v___x_2351_);
                    v___x_2353_ = v___x_2348_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_k_2048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 2, v_v_2049_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 3, v_l_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 4, v_l_2050_);
                    v___x_2353_ = v_reuseFailAlloc_2360_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                if v_isShared_2217_ == 0 {
                    leanh::lean_ctor_set(v___x_2216_, 4, v_l_2050_);
                    leanh::lean_ctor_set(v___x_2216_, 3, v_l_2050_);
                    leanh::lean_ctor_set(v___x_2216_, 2, v_v_2344_);
                    leanh::lean_ctor_set(v___x_2216_, 1, v_k_2343_);
                    leanh::lean_ctor_set(v___x_2216_, 0, v___x_2351_);
                    v___x_2355_ = v___x_2216_;
                    state = 69;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2351_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_k_2343_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 2, v_v_2344_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 3, v_l_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 4, v_l_2050_);
                    v___x_2355_ = v_reuseFailAlloc_2359_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                if v_isShared_2342_ == 0 {
                    leanh::lean_ctor_set(v___x_2341_, 4, v___x_2355_);
                    leanh::lean_ctor_set(v___x_2341_, 3, v___x_2353_);
                    leanh::lean_ctor_set(v___x_2341_, 2, v_v_2346_);
                    leanh::lean_ctor_set(v___x_2341_, 1, v_k_2345_);
                    leanh::lean_ctor_set(v___x_2341_, 0, v___x_2350_);
                    v___x_2357_ = v___x_2341_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2350_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_k_2345_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 2, v_v_2346_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 3, v___x_2353_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 4, v___x_2355_);
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
                if leanh::lean_obj_tag(v_l_2388_) == 0 {
                    if leanh::lean_obj_tag(v_r_2389_) == 0 {
                        v_size_2402_ = leanh::lean_ctor_get(v_l_2388_, 0);
                        v_size_2403_ = leanh::lean_ctor_get(v_r_2389_, 0);
                        v_k_2404_ = leanh::lean_ctor_get(v_r_2389_, 1);
                        v_v_2405_ = leanh::lean_ctor_get(v_r_2389_, 2);
                        v_l_2406_ = leanh::lean_ctor_get(v_r_2389_, 3);
                        v_r_2407_ = leanh::lean_ctor_get(v_r_2389_, 4);
                        v___x_2408_ = leanh::lean_unsigned_to_nat(2);
                        v___x_2409_ = lean_nat_mul(v___x_2408_, v_size_2402_);
                        v___x_2410_ = lean_nat_dec_lt(v_size_2403_, v___x_2409_);
                        leanh::lean_dec(v___x_2409_);
                        if v___x_2410_ == 0 {
                            leanh::lean_inc(v_r_2407_);
                            leanh::lean_inc(v_l_2406_);
                            leanh::lean_inc(v_v_2405_);
                            leanh::lean_inc(v_k_2404_);
                            v_isSharedCheck_2440_ =
                                (!leanh::lean_is_exclusive(v_r_2389_)) as u8;
                            if v_isSharedCheck_2440_ == 0 {
                                v_unused_2441_ = leanh::lean_ctor_get(v_r_2389_, 4);
                                leanh::lean_dec(v_unused_2441_);
                                v_unused_2442_ = leanh::lean_ctor_get(v_r_2389_, 3);
                                leanh::lean_dec(v_unused_2442_);
                                v_unused_2443_ = leanh::lean_ctor_get(v_r_2389_, 2);
                                leanh::lean_dec(v_unused_2443_);
                                v_unused_2444_ = leanh::lean_ctor_get(v_r_2389_, 1);
                                leanh::lean_dec(v_unused_2444_);
                                v_unused_2445_ = leanh::lean_ctor_get(v_r_2389_, 0);
                                leanh::lean_dec(v_unused_2445_);
                                v___x_2412_ = v_r_2389_;
                                v_isShared_2413_ = v_isSharedCheck_2440_;
                                state = 74;
                                continue;
                            } else {
                                leanh::lean_dec(v_r_2389_);
                                v___x_2412_ = leanh::lean_box(0);
                                v_isShared_2413_ = v_isSharedCheck_2440_;
                                state = 74;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_1871_);
                            v___x_2446_ = leanh::lean_unsigned_to_nat(1);
                            v___x_2447_ = lean_nat_add(v___x_2446_, v_size_2385_);
                            leanh::lean_dec(v_size_2385_);
                            v___x_2448_ = lean_nat_add(v___x_2447_, v_size_2384_);
                            leanh::lean_dec(v___x_2447_);
                            v___x_2449_ = lean_nat_add(v___x_2446_, v_size_2384_);
                            leanh::lean_dec(v_size_2384_);
                            v___x_2450_ = lean_nat_add(v___x_2449_, v_size_2403_);
                            leanh::lean_dec(v___x_2449_);
                            leanh::lean_inc_ref(v___x_2383_);
                            if v_isShared_2401_ == 0 {
                                leanh::lean_ctor_set(v___x_2400_, 4, v___x_2383_);
                                leanh::lean_ctor_set(v___x_2400_, 3, v_r_2389_);
                                leanh::lean_ctor_set(v___x_2400_, 2, v_v_1867_);
                                leanh::lean_ctor_set(v___x_2400_, 1, v_k_1866_);
                                leanh::lean_ctor_set(v___x_2400_, 0, v___x_2450_);
                                v___x_2452_ = v___x_2400_;
                                state = 80;
                                continue;
                            } else {
                                v_reuseFailAlloc_2465_ =
                                    leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 0, v___x_2450_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 1, v_k_1866_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 2, v_v_1867_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 3, v_r_2389_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2465_, 4, v___x_2383_);
                                v___x_2452_ = v_reuseFailAlloc_2465_;
                                state = 80;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_l_2388_, 5);
                        leanh::lean_del_object(v___x_2400_);
                        leanh::lean_dec(v_v_2387_);
                        leanh::lean_dec(v_k_2386_);
                        leanh::lean_dec(v_size_2385_);
                        leanh::lean_dec(v_size_2384_);
                        leanh::lean_dec_ref_known(v___x_2383_, 5);
                        leanh::lean_del_object(v___x_1871_);
                        leanh::lean_dec(v_v_1867_);
                        leanh::lean_dec(v_k_1866_);
                        v___x_2466_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__3);
                        v___x_2467_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2466_);
                        return v___x_2467_;
                    }
                } else {
                    leanh::lean_del_object(v___x_2400_);
                    leanh::lean_dec(v_r_2389_);
                    leanh::lean_dec(v_v_2387_);
                    leanh::lean_dec(v_k_2386_);
                    leanh::lean_dec(v_size_2385_);
                    leanh::lean_dec(v_size_2384_);
                    leanh::lean_dec_ref_known(v___x_2383_, 5);
                    leanh::lean_del_object(v___x_1871_);
                    leanh::lean_dec(v_v_1867_);
                    leanh::lean_dec(v_k_1866_);
                    v___x_2468_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4_once), _init_l_Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0___redArg___closed__4);
                    v___x_2469_ = l_panic___at___00Std_DTreeMap_Internal_Impl_insert_x21___at___00Lake_JsonObject_insertJson_spec__0_spec__0___redArg(v___x_2468_);
                    return v___x_2469_;
                }
            }
            74 => {
                v___x_2414_ = leanh::lean_unsigned_to_nat(1);
                v___x_2415_ = lean_nat_add(v___x_2414_, v_size_2385_);
                leanh::lean_dec(v_size_2385_);
                v___x_2416_ = lean_nat_add(v___x_2415_, v_size_2384_);
                leanh::lean_dec(v___x_2415_);
                v___x_2428_ = lean_nat_add(v___x_2414_, v_size_2402_);
                if leanh::lean_obj_tag(v_l_2406_) == 0 {
                    v_size_2438_ = leanh::lean_ctor_get(v_l_2406_, 0);
                    leanh::lean_inc(v_size_2438_);
                    v___y_2430_ = v_size_2438_;
                    state = 78;
                    continue;
                } else {
                    v___x_2439_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2430_ = v___x_2439_;
                    state = 78;
                    continue;
                }
            }
            75 => {
                v___x_2421_ = lean_nat_add(v___y_2418_, v___y_2420_);
                leanh::lean_dec(v___y_2420_);
                leanh::lean_dec(v___y_2418_);
                if v_isShared_2413_ == 0 {
                    leanh::lean_ctor_set(v___x_2412_, 4, v___x_2383_);
                    leanh::lean_ctor_set(v___x_2412_, 3, v_r_2407_);
                    leanh::lean_ctor_set(v___x_2412_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v___x_2412_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v___x_2412_, 0, v___x_2421_);
                    v___x_2423_ = v___x_2412_;
                    state = 76;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2421_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 3, v_r_2407_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 4, v___x_2383_);
                    v___x_2423_ = v_reuseFailAlloc_2427_;
                    state = 76;
                    continue;
                }
            }
            76 => {
                if v_isShared_2401_ == 0 {
                    leanh::lean_ctor_set(v___x_2400_, 4, v___x_2423_);
                    leanh::lean_ctor_set(v___x_2400_, 3, v___y_2419_);
                    leanh::lean_ctor_set(v___x_2400_, 2, v_v_2405_);
                    leanh::lean_ctor_set(v___x_2400_, 1, v_k_2404_);
                    leanh::lean_ctor_set(v___x_2400_, 0, v___x_2416_);
                    v___x_2425_ = v___x_2400_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2416_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_k_2404_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 2, v_v_2405_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 3, v___y_2419_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 4, v___x_2423_);
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
                leanh::lean_dec(v___y_2430_);
                leanh::lean_dec(v___x_2428_);
                if v_isShared_1872_ == 0 {
                    leanh::lean_ctor_set(v___x_1871_, 4, v_l_2406_);
                    leanh::lean_ctor_set(v___x_1871_, 3, v_l_2388_);
                    leanh::lean_ctor_set(v___x_1871_, 2, v_v_2387_);
                    leanh::lean_ctor_set(v___x_1871_, 1, v_k_2386_);
                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_2431_);
                    v___x_2433_ = v___x_1871_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_2437_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2431_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_k_2386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 2, v_v_2387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 3, v_l_2388_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 4, v_l_2406_);
                    v___x_2433_ = v_reuseFailAlloc_2437_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                v___x_2434_ = lean_nat_add(v___x_2414_, v_size_2384_);
                leanh::lean_dec(v_size_2384_);
                if leanh::lean_obj_tag(v_r_2407_) == 0 {
                    v_size_2435_ = leanh::lean_ctor_get(v_r_2407_, 0);
                    leanh::lean_inc(v_size_2435_);
                    v___y_2418_ = v___x_2434_;
                    v___y_2419_ = v___x_2433_;
                    v___y_2420_ = v_size_2435_;
                    state = 75;
                    continue;
                } else {
                    v___x_2436_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2418_ = v___x_2434_;
                    v___y_2419_ = v___x_2433_;
                    v___y_2420_ = v___x_2436_;
                    state = 75;
                    continue;
                }
            }
            80 => {
                v_isSharedCheck_2459_ = (!leanh::lean_is_exclusive(v___x_2383_)) as u8;
                if v_isSharedCheck_2459_ == 0 {
                    v_unused_2460_ = leanh::lean_ctor_get(v___x_2383_, 4);
                    leanh::lean_dec(v_unused_2460_);
                    v_unused_2461_ = leanh::lean_ctor_get(v___x_2383_, 3);
                    leanh::lean_dec(v_unused_2461_);
                    v_unused_2462_ = leanh::lean_ctor_get(v___x_2383_, 2);
                    leanh::lean_dec(v_unused_2462_);
                    v_unused_2463_ = leanh::lean_ctor_get(v___x_2383_, 1);
                    leanh::lean_dec(v_unused_2463_);
                    v_unused_2464_ = leanh::lean_ctor_get(v___x_2383_, 0);
                    leanh::lean_dec(v_unused_2464_);
                    v___x_2454_ = v___x_2383_;
                    v_isShared_2455_ = v_isSharedCheck_2459_;
                    state = 81;
                    continue;
                } else {
                    leanh::lean_dec(v___x_2383_);
                    v___x_2454_ = leanh::lean_box(0);
                    v_isShared_2455_ = v_isSharedCheck_2459_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                if v_isShared_2455_ == 0 {
                    leanh::lean_ctor_set(v___x_2454_, 4, v___x_2452_);
                    leanh::lean_ctor_set(v___x_2454_, 3, v_l_2388_);
                    leanh::lean_ctor_set(v___x_2454_, 2, v_v_2387_);
                    leanh::lean_ctor_set(v___x_2454_, 1, v_k_2386_);
                    leanh::lean_ctor_set(v___x_2454_, 0, v___x_2448_);
                    v___x_2457_ = v___x_2454_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 1, v_k_2386_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 2, v_v_2387_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 3, v_l_2388_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 4, v___x_2452_);
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
                v_size_2490_ = leanh::lean_ctor_get(v_r_2483_, 0);
                v___x_2491_ = leanh::lean_unsigned_to_nat(1);
                v___x_2492_ = lean_nat_add(v___x_2491_, v_size_2484_);
                leanh::lean_dec(v_size_2484_);
                v___x_2493_ = lean_nat_add(v___x_2491_, v_size_2490_);
                if v_isShared_2489_ == 0 {
                    leanh::lean_ctor_set(v___x_2488_, 4, v___x_2383_);
                    leanh::lean_ctor_set(v___x_2488_, 3, v_r_2483_);
                    leanh::lean_ctor_set(v___x_2488_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v___x_2488_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v___x_2488_, 0, v___x_2493_);
                    v___x_2495_ = v___x_2488_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_2499_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 3, v_r_2483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 4, v___x_2383_);
                    v___x_2495_ = v_reuseFailAlloc_2499_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                if v_isShared_1872_ == 0 {
                    leanh::lean_ctor_set(v___x_1871_, 4, v___x_2495_);
                    leanh::lean_ctor_set(v___x_1871_, 3, v_l_2482_);
                    leanh::lean_ctor_set(v___x_1871_, 2, v_v_2486_);
                    leanh::lean_ctor_set(v___x_1871_, 1, v_k_2485_);
                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_2492_);
                    v___x_2497_ = v___x_1871_;
                    state = 86;
                    continue;
                } else {
                    v_reuseFailAlloc_2498_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2492_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 1, v_k_2485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 2, v_v_2486_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 3, v_l_2482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 4, v___x_2495_);
                    v___x_2497_ = v_reuseFailAlloc_2498_;
                    state = 86;
                    continue;
                }
            }
            86 => {
                return v___x_2497_;
            }
            87 => {
                v___x_2508_ = leanh::lean_unsigned_to_nat(3);
                v___x_2509_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_2507_ == 0 {
                    leanh::lean_ctor_set(v___x_2506_, 3, v_r_2483_);
                    leanh::lean_ctor_set(v___x_2506_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v___x_2506_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v___x_2506_, 0, v___x_2509_);
                    v___x_2511_ = v___x_2506_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_2515_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___x_2509_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 3, v_r_2483_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2515_, 4, v_r_2483_);
                    v___x_2511_ = v_reuseFailAlloc_2515_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                if v_isShared_1872_ == 0 {
                    leanh::lean_ctor_set(v___x_1871_, 4, v___x_2511_);
                    leanh::lean_ctor_set(v___x_1871_, 3, v_l_2482_);
                    leanh::lean_ctor_set(v___x_1871_, 2, v_v_2504_);
                    leanh::lean_ctor_set(v___x_1871_, 1, v_k_2503_);
                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_2508_);
                    v___x_2513_ = v___x_1871_;
                    state = 89;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_k_2503_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 2, v_v_2504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 3, v_l_2482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2514_, 4, v___x_2511_);
                    v___x_2513_ = v_reuseFailAlloc_2514_;
                    state = 89;
                    continue;
                }
            }
            89 => {
                return v___x_2513_;
            }
            90 => {
                v_k_2526_ = leanh::lean_ctor_get(v_r_2520_, 1);
                v_v_2527_ = leanh::lean_ctor_get(v_r_2520_, 2);
                v_isSharedCheck_2542_ = (!leanh::lean_is_exclusive(v_r_2520_)) as u8;
                if v_isSharedCheck_2542_ == 0 {
                    v_unused_2543_ = leanh::lean_ctor_get(v_r_2520_, 4);
                    leanh::lean_dec(v_unused_2543_);
                    v_unused_2544_ = leanh::lean_ctor_get(v_r_2520_, 3);
                    leanh::lean_dec(v_unused_2544_);
                    v_unused_2545_ = leanh::lean_ctor_get(v_r_2520_, 0);
                    leanh::lean_dec(v_unused_2545_);
                    v___x_2529_ = v_r_2520_;
                    v_isShared_2530_ = v_isSharedCheck_2542_;
                    state = 91;
                    continue;
                } else {
                    leanh::lean_inc(v_v_2527_);
                    leanh::lean_inc(v_k_2526_);
                    leanh::lean_dec(v_r_2520_);
                    v___x_2529_ = leanh::lean_box(0);
                    v_isShared_2530_ = v_isSharedCheck_2542_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                v___x_2531_ = leanh::lean_unsigned_to_nat(3);
                v___x_2532_ = leanh::lean_unsigned_to_nat(1);
                if v_isShared_2530_ == 0 {
                    leanh::lean_ctor_set(v___x_2529_, 4, v_l_2482_);
                    leanh::lean_ctor_set(v___x_2529_, 3, v_l_2482_);
                    leanh::lean_ctor_set(v___x_2529_, 2, v_v_2522_);
                    leanh::lean_ctor_set(v___x_2529_, 1, v_k_2521_);
                    leanh::lean_ctor_set(v___x_2529_, 0, v___x_2532_);
                    v___x_2534_ = v___x_2529_;
                    state = 92;
                    continue;
                } else {
                    v_reuseFailAlloc_2541_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2532_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_k_2521_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 2, v_v_2522_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 3, v_l_2482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2541_, 4, v_l_2482_);
                    v___x_2534_ = v_reuseFailAlloc_2541_;
                    state = 92;
                    continue;
                }
            }
            92 => {
                if v_isShared_2525_ == 0 {
                    leanh::lean_ctor_set(v___x_2524_, 4, v_l_2482_);
                    leanh::lean_ctor_set(v___x_2524_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v___x_2524_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v___x_2524_, 0, v___x_2532_);
                    v___x_2536_ = v___x_2524_;
                    state = 93;
                    continue;
                } else {
                    v_reuseFailAlloc_2540_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2532_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_k_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 2, v_v_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 3, v_l_2482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2540_, 4, v_l_2482_);
                    v___x_2536_ = v_reuseFailAlloc_2540_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                if v_isShared_1872_ == 0 {
                    leanh::lean_ctor_set(v___x_1871_, 4, v___x_2536_);
                    leanh::lean_ctor_set(v___x_1871_, 3, v___x_2534_);
                    leanh::lean_ctor_set(v___x_1871_, 2, v_v_2527_);
                    leanh::lean_ctor_set(v___x_1871_, 1, v_k_2526_);
                    leanh::lean_ctor_set(v___x_1871_, 0, v___x_2531_);
                    v___x_2538_ = v___x_1871_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_2539_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_k_2526_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_v_2527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 3, v___x_2534_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2539_, 4, v___x_2536_);
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
    mut v_k_2560_: *mut leanh::LeanObject,
    mut v_t_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2562_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(
            v_k_2560_, v_t_2561_,
        );
    leanh::lean_dec_ref(v_k_2560_);
    return v_res_2562_;
}
pub unsafe fn l_Lake_JsonObject_erase(
    mut v_obj_2563_: *mut leanh::LeanObject,
    mut v_prop_2564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2565_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(
            v_prop_2564_,
            v_obj_2563_,
        );
    return v___x_2565_;
}
pub unsafe fn l_Lake_JsonObject_erase___boxed(
    mut v_obj_2566_: *mut leanh::LeanObject,
    mut v_prop_2567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Lake_JsonObject_erase(v_obj_2566_, v_prop_2567_);
    leanh::lean_dec_ref(v_prop_2567_);
    return v_res_2568_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0(
    mut v_00_u03b2_2569_: *mut leanh::LeanObject,
    mut v_k_2570_: *mut leanh::LeanObject,
    mut v_t_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2572_ =
        l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___redArg(
            v_k_2570_, v_t_2571_,
        );
    return v___x_2572_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0___boxed(
    mut v_00_u03b2_2573_: *mut leanh::LeanObject,
    mut v_k_2574_: *mut leanh::LeanObject,
    mut v_t_2575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2576_ = l_Std_DTreeMap_Internal_Impl_erase_x21___at___00Lake_JsonObject_erase_spec__0(
        v_00_u03b2_2573_,
        v_k_2574_,
        v_t_2575_,
    );
    leanh::lean_dec_ref(v_k_2574_);
    return v_res_2576_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(
    mut v_t_2577_: *mut leanh::LeanObject,
    mut v_k_2578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: u8 = 0;
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_2577_) == 0 {
                    v_k_2579_ = leanh::lean_ctor_get(v_t_2577_, 1);
                    v_v_2580_ = leanh::lean_ctor_get(v_t_2577_, 2);
                    v_l_2581_ = leanh::lean_ctor_get(v_t_2577_, 3);
                    v_r_2582_ = leanh::lean_ctor_get(v_t_2577_, 4);
                    v___x_2583_ = lean_string_compare(v_k_2578_, v_k_2579_);
                    match v___x_2583_ {
                        0 => {
                            v_t_2577_ = v_l_2581_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            leanh::lean_inc(v_v_2580_);
                            v___x_2585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2585_, 0, v_v_2580_);
                            return v___x_2585_;
                        }
                        _ => {
                            v_t_2577_ = v_r_2582_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2587_ = leanh::lean_box(0);
                    return v___x_2587_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg___boxed(
    mut v_t_2588_: *mut leanh::LeanObject,
    mut v_k_2589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_t_2588_, v_k_2589_);
    leanh::lean_dec_ref(v_k_2589_);
    leanh::lean_dec(v_t_2588_);
    return v_res_2590_;
}
pub unsafe fn l_Lake_JsonObject_getJson_x3f(
    mut v_obj_2591_: *mut leanh::LeanObject,
    mut v_prop_2592_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2591_, v_prop_2592_);
    return v___x_2593_;
}
pub unsafe fn l_Lake_JsonObject_getJson_x3f___boxed(
    mut v_obj_2594_: *mut leanh::LeanObject,
    mut v_prop_2595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2596_ = l_Lake_JsonObject_getJson_x3f(v_obj_2594_, v_prop_2595_);
    leanh::lean_dec_ref(v_prop_2595_);
    leanh::lean_dec(v_obj_2594_);
    return v_res_2596_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0(
    mut v_00_u03b4_2597_: *mut leanh::LeanObject,
    mut v_t_2598_: *mut leanh::LeanObject,
    mut v_k_2599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2600_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_t_2598_, v_k_2599_);
    return v___x_2600_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___boxed(
    mut v_00_u03b4_2601_: *mut leanh::LeanObject,
    mut v_t_2602_: *mut leanh::LeanObject,
    mut v_k_2603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2604_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0(
            v_00_u03b4_2601_,
            v_t_2602_,
            v_k_2603_,
        );
    leanh::lean_dec_ref(v_k_2603_);
    leanh::lean_dec(v_t_2602_);
    return v_res_2604_;
}
pub unsafe fn l_Lake_JsonObject_get___redArg(
    mut v_inst_2607_: *mut leanh::LeanObject,
    mut v_obj_2608_: *mut leanh::LeanObject,
    mut v_prop_2609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2626_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2610_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2608_, v_prop_2609_);
                if leanh::lean_obj_tag(v___x_2610_) == 0 {
                    leanh::lean_dec_ref(v_inst_2607_);
                    v___x_2611_ = l_Lake_JsonObject_get___redArg___closed__0;
                    v___x_2612_ = lean_string_append(v___x_2611_, v_prop_2609_);
                    leanh::lean_dec_ref(v_prop_2609_);
                    v___x_2613_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2613_, 0, v___x_2612_);
                    return v___x_2613_;
                } else {
                    v_val_2614_ = leanh::lean_ctor_get(v___x_2610_, 0);
                    leanh::lean_inc(v_val_2614_);
                    leanh::lean_dec_ref_known(v___x_2610_, 1);
                    v___x_2615_ = leanh::lean_apply_1(v_inst_2607_, v_val_2614_);
                    if leanh::lean_obj_tag(v___x_2615_) == 0 {
                        v_a_2616_ = leanh::lean_ctor_get(v___x_2615_, 0);
                        v_isSharedCheck_2626_ =
                            (!leanh::lean_is_exclusive(v___x_2615_)) as u8;
                        if v_isSharedCheck_2626_ == 0 {
                            v___x_2618_ = v___x_2615_;
                            v_isShared_2619_ = v_isSharedCheck_2626_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2616_);
                            leanh::lean_dec(v___x_2615_);
                            v___x_2618_ = leanh::lean_box(0);
                            v_isShared_2619_ = v_isSharedCheck_2626_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_prop_2609_);
                        return v___x_2615_;
                    }
                }
            }
            1 => {
                v___x_2620_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2621_ = lean_string_append(v_prop_2609_, v___x_2620_);
                v___x_2622_ = lean_string_append(v___x_2621_, v_a_2616_);
                leanh::lean_dec(v_a_2616_);
                if v_isShared_2619_ == 0 {
                    leanh::lean_ctor_set(v___x_2618_, 0, v___x_2622_);
                    v___x_2624_ = v___x_2618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2625_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2625_, 0, v___x_2622_);
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
    mut v_inst_2627_: *mut leanh::LeanObject,
    mut v_obj_2628_: *mut leanh::LeanObject,
    mut v_prop_2629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2630_ = l_Lake_JsonObject_get___redArg(v_inst_2627_, v_obj_2628_, v_prop_2629_);
    leanh::lean_dec(v_obj_2628_);
    return v_res_2630_;
}
pub unsafe fn l_Lake_JsonObject_get(
    mut v_00_u03b1_2631_: *mut leanh::LeanObject,
    mut v_inst_2632_: *mut leanh::LeanObject,
    mut v_obj_2633_: *mut leanh::LeanObject,
    mut v_prop_2634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2644_: u8 = 0;
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2651_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2633_, v_prop_2634_);
                if leanh::lean_obj_tag(v___x_2635_) == 0 {
                    leanh::lean_dec_ref(v_inst_2632_);
                    v___x_2636_ = l_Lake_JsonObject_get___redArg___closed__0;
                    v___x_2637_ = lean_string_append(v___x_2636_, v_prop_2634_);
                    leanh::lean_dec_ref(v_prop_2634_);
                    v___x_2638_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2638_, 0, v___x_2637_);
                    return v___x_2638_;
                } else {
                    v_val_2639_ = leanh::lean_ctor_get(v___x_2635_, 0);
                    leanh::lean_inc(v_val_2639_);
                    leanh::lean_dec_ref_known(v___x_2635_, 1);
                    v___x_2640_ = leanh::lean_apply_1(v_inst_2632_, v_val_2639_);
                    if leanh::lean_obj_tag(v___x_2640_) == 0 {
                        v_a_2641_ = leanh::lean_ctor_get(v___x_2640_, 0);
                        v_isSharedCheck_2651_ =
                            (!leanh::lean_is_exclusive(v___x_2640_)) as u8;
                        if v_isSharedCheck_2651_ == 0 {
                            v___x_2643_ = v___x_2640_;
                            v_isShared_2644_ = v_isSharedCheck_2651_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2641_);
                            leanh::lean_dec(v___x_2640_);
                            v___x_2643_ = leanh::lean_box(0);
                            v_isShared_2644_ = v_isSharedCheck_2651_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_prop_2634_);
                        return v___x_2640_;
                    }
                }
            }
            1 => {
                v___x_2645_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2646_ = lean_string_append(v_prop_2634_, v___x_2645_);
                v___x_2647_ = lean_string_append(v___x_2646_, v_a_2641_);
                leanh::lean_dec(v_a_2641_);
                if v_isShared_2644_ == 0 {
                    leanh::lean_ctor_set(v___x_2643_, 0, v___x_2647_);
                    v___x_2649_ = v___x_2643_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2650_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
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
    mut v_00_u03b1_2652_: *mut leanh::LeanObject,
    mut v_inst_2653_: *mut leanh::LeanObject,
    mut v_obj_2654_: *mut leanh::LeanObject,
    mut v_prop_2655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2656_ = l_Lake_JsonObject_get(v_00_u03b1_2652_, v_inst_2653_, v_obj_2654_, v_prop_2655_);
    leanh::lean_dec(v_obj_2654_);
    return v_res_2656_;
}
pub unsafe fn l_Lake_JsonObject_getAs___redArg(
    mut v_inst_2657_: *mut leanh::LeanObject,
    mut v_obj_2658_: *mut leanh::LeanObject,
    mut v_prop_2659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2676_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2660_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2658_, v_prop_2659_);
                if leanh::lean_obj_tag(v___x_2660_) == 0 {
                    leanh::lean_dec_ref(v_inst_2657_);
                    v___x_2661_ = l_Lake_JsonObject_get___redArg___closed__0;
                    v___x_2662_ = lean_string_append(v___x_2661_, v_prop_2659_);
                    leanh::lean_dec_ref(v_prop_2659_);
                    v___x_2663_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2663_, 0, v___x_2662_);
                    return v___x_2663_;
                } else {
                    v_val_2664_ = leanh::lean_ctor_get(v___x_2660_, 0);
                    leanh::lean_inc(v_val_2664_);
                    leanh::lean_dec_ref_known(v___x_2660_, 1);
                    v___x_2665_ = leanh::lean_apply_1(v_inst_2657_, v_val_2664_);
                    if leanh::lean_obj_tag(v___x_2665_) == 0 {
                        v_a_2666_ = leanh::lean_ctor_get(v___x_2665_, 0);
                        v_isSharedCheck_2676_ =
                            (!leanh::lean_is_exclusive(v___x_2665_)) as u8;
                        if v_isSharedCheck_2676_ == 0 {
                            v___x_2668_ = v___x_2665_;
                            v_isShared_2669_ = v_isSharedCheck_2676_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2666_);
                            leanh::lean_dec(v___x_2665_);
                            v___x_2668_ = leanh::lean_box(0);
                            v_isShared_2669_ = v_isSharedCheck_2676_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_prop_2659_);
                        return v___x_2665_;
                    }
                }
            }
            1 => {
                v___x_2670_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2671_ = lean_string_append(v_prop_2659_, v___x_2670_);
                v___x_2672_ = lean_string_append(v___x_2671_, v_a_2666_);
                leanh::lean_dec(v_a_2666_);
                if v_isShared_2669_ == 0 {
                    leanh::lean_ctor_set(v___x_2668_, 0, v___x_2672_);
                    v___x_2674_ = v___x_2668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2675_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2675_, 0, v___x_2672_);
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
    mut v_inst_2677_: *mut leanh::LeanObject,
    mut v_obj_2678_: *mut leanh::LeanObject,
    mut v_prop_2679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2680_ = l_Lake_JsonObject_getAs___redArg(v_inst_2677_, v_obj_2678_, v_prop_2679_);
    leanh::lean_dec(v_obj_2678_);
    return v_res_2680_;
}
pub unsafe fn l_Lake_JsonObject_getAs(
    mut v_00_u03b1_2681_: *mut leanh::LeanObject,
    mut v_inst_2682_: *mut leanh::LeanObject,
    mut v_obj_2683_: *mut leanh::LeanObject,
    mut v_prop_2684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2694_: u8 = 0;
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2685_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2683_, v_prop_2684_);
                if leanh::lean_obj_tag(v___x_2685_) == 0 {
                    leanh::lean_dec_ref(v_inst_2682_);
                    v___x_2686_ = l_Lake_JsonObject_get___redArg___closed__0;
                    v___x_2687_ = lean_string_append(v___x_2686_, v_prop_2684_);
                    leanh::lean_dec_ref(v_prop_2684_);
                    v___x_2688_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2688_, 0, v___x_2687_);
                    return v___x_2688_;
                } else {
                    v_val_2689_ = leanh::lean_ctor_get(v___x_2685_, 0);
                    leanh::lean_inc(v_val_2689_);
                    leanh::lean_dec_ref_known(v___x_2685_, 1);
                    v___x_2690_ = leanh::lean_apply_1(v_inst_2682_, v_val_2689_);
                    if leanh::lean_obj_tag(v___x_2690_) == 0 {
                        v_a_2691_ = leanh::lean_ctor_get(v___x_2690_, 0);
                        v_isSharedCheck_2701_ =
                            (!leanh::lean_is_exclusive(v___x_2690_)) as u8;
                        if v_isSharedCheck_2701_ == 0 {
                            v___x_2693_ = v___x_2690_;
                            v_isShared_2694_ = v_isSharedCheck_2701_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2691_);
                            leanh::lean_dec(v___x_2690_);
                            v___x_2693_ = leanh::lean_box(0);
                            v_isShared_2694_ = v_isSharedCheck_2701_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_prop_2684_);
                        return v___x_2690_;
                    }
                }
            }
            1 => {
                v___x_2695_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2696_ = lean_string_append(v_prop_2684_, v___x_2695_);
                v___x_2697_ = lean_string_append(v___x_2696_, v_a_2691_);
                leanh::lean_dec(v_a_2691_);
                if v_isShared_2694_ == 0 {
                    leanh::lean_ctor_set(v___x_2693_, 0, v___x_2697_);
                    v___x_2699_ = v___x_2693_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2700_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
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
    mut v_00_u03b1_2702_: *mut leanh::LeanObject,
    mut v_inst_2703_: *mut leanh::LeanObject,
    mut v_obj_2704_: *mut leanh::LeanObject,
    mut v_prop_2705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2706_ =
        l_Lake_JsonObject_getAs(v_00_u03b1_2702_, v_inst_2703_, v_obj_2704_, v_prop_2705_);
    leanh::lean_dec(v_obj_2704_);
    return v_res_2706_;
}
pub unsafe fn l_Lake_JsonObject_get_x3f___redArg(
    mut v_inst_2709_: *mut leanh::LeanObject,
    mut v_obj_2710_: *mut leanh::LeanObject,
    mut v_prop_2711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2712_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2710_, v_prop_2711_);
                if leanh::lean_obj_tag(v___x_2712_) == 0 {
                    leanh::lean_dec_ref(v_prop_2711_);
                    leanh::lean_dec_ref(v_inst_2709_);
                    v___x_2713_ = l_Lake_JsonObject_get_x3f___redArg___closed__0;
                    return v___x_2713_;
                } else {
                    v_val_2714_ = leanh::lean_ctor_get(v___x_2712_, 0);
                    leanh::lean_inc(v_val_2714_);
                    leanh::lean_dec_ref_known(v___x_2712_, 1);
                    v___x_2715_ = l_Option_fromJson_x3f___redArg(v_inst_2709_, v_val_2714_);
                    if leanh::lean_obj_tag(v___x_2715_) == 0 {
                        v_a_2716_ = leanh::lean_ctor_get(v___x_2715_, 0);
                        v_isSharedCheck_2726_ =
                            (!leanh::lean_is_exclusive(v___x_2715_)) as u8;
                        if v_isSharedCheck_2726_ == 0 {
                            v___x_2718_ = v___x_2715_;
                            v_isShared_2719_ = v_isSharedCheck_2726_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2716_);
                            leanh::lean_dec(v___x_2715_);
                            v___x_2718_ = leanh::lean_box(0);
                            v_isShared_2719_ = v_isSharedCheck_2726_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_prop_2711_);
                        return v___x_2715_;
                    }
                }
            }
            1 => {
                v___x_2720_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2721_ = lean_string_append(v_prop_2711_, v___x_2720_);
                v___x_2722_ = lean_string_append(v___x_2721_, v_a_2716_);
                leanh::lean_dec(v_a_2716_);
                if v_isShared_2719_ == 0 {
                    leanh::lean_ctor_set(v___x_2718_, 0, v___x_2722_);
                    v___x_2724_ = v___x_2718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2725_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2725_, 0, v___x_2722_);
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
    mut v_inst_2727_: *mut leanh::LeanObject,
    mut v_obj_2728_: *mut leanh::LeanObject,
    mut v_prop_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2730_ = l_Lake_JsonObject_get_x3f___redArg(v_inst_2727_, v_obj_2728_, v_prop_2729_);
    leanh::lean_dec(v_obj_2728_);
    return v_res_2730_;
}
pub unsafe fn l_Lake_JsonObject_get_x3f(
    mut v_00_u03b1_2731_: *mut leanh::LeanObject,
    mut v_inst_2732_: *mut leanh::LeanObject,
    mut v_obj_2733_: *mut leanh::LeanObject,
    mut v_prop_2734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2742_: u8 = 0;
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2735_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2733_, v_prop_2734_);
                if leanh::lean_obj_tag(v___x_2735_) == 0 {
                    leanh::lean_dec_ref(v_prop_2734_);
                    leanh::lean_dec_ref(v_inst_2732_);
                    v___x_2736_ = l_Lake_JsonObject_get_x3f___redArg___closed__0;
                    return v___x_2736_;
                } else {
                    v_val_2737_ = leanh::lean_ctor_get(v___x_2735_, 0);
                    leanh::lean_inc(v_val_2737_);
                    leanh::lean_dec_ref_known(v___x_2735_, 1);
                    v___x_2738_ = l_Option_fromJson_x3f___redArg(v_inst_2732_, v_val_2737_);
                    if leanh::lean_obj_tag(v___x_2738_) == 0 {
                        v_a_2739_ = leanh::lean_ctor_get(v___x_2738_, 0);
                        v_isSharedCheck_2749_ =
                            (!leanh::lean_is_exclusive(v___x_2738_)) as u8;
                        if v_isSharedCheck_2749_ == 0 {
                            v___x_2741_ = v___x_2738_;
                            v_isShared_2742_ = v_isSharedCheck_2749_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2739_);
                            leanh::lean_dec(v___x_2738_);
                            v___x_2741_ = leanh::lean_box(0);
                            v_isShared_2742_ = v_isSharedCheck_2749_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_prop_2734_);
                        return v___x_2738_;
                    }
                }
            }
            1 => {
                v___x_2743_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2744_ = lean_string_append(v_prop_2734_, v___x_2743_);
                v___x_2745_ = lean_string_append(v___x_2744_, v_a_2739_);
                leanh::lean_dec(v_a_2739_);
                if v_isShared_2742_ == 0 {
                    leanh::lean_ctor_set(v___x_2741_, 0, v___x_2745_);
                    v___x_2747_ = v___x_2741_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
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
    mut v_00_u03b1_2750_: *mut leanh::LeanObject,
    mut v_inst_2751_: *mut leanh::LeanObject,
    mut v_obj_2752_: *mut leanh::LeanObject,
    mut v_prop_2753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2754_ =
        l_Lake_JsonObject_get_x3f(v_00_u03b1_2750_, v_inst_2751_, v_obj_2752_, v_prop_2753_);
    leanh::lean_dec(v_obj_2752_);
    return v_res_2754_;
}
pub unsafe fn l_Lake_JsonObject_getAs_x3f___redArg(
    mut v_inst_2755_: *mut leanh::LeanObject,
    mut v_obj_2756_: *mut leanh::LeanObject,
    mut v_prop_2757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2765_: u8 = 0;
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2758_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2756_, v_prop_2757_);
                if leanh::lean_obj_tag(v___x_2758_) == 0 {
                    leanh::lean_dec_ref(v_prop_2757_);
                    leanh::lean_dec_ref(v_inst_2755_);
                    v___x_2759_ = l_Lake_JsonObject_get_x3f___redArg___closed__0;
                    return v___x_2759_;
                } else {
                    v_val_2760_ = leanh::lean_ctor_get(v___x_2758_, 0);
                    leanh::lean_inc(v_val_2760_);
                    leanh::lean_dec_ref_known(v___x_2758_, 1);
                    v___x_2761_ = l_Option_fromJson_x3f___redArg(v_inst_2755_, v_val_2760_);
                    if leanh::lean_obj_tag(v___x_2761_) == 0 {
                        v_a_2762_ = leanh::lean_ctor_get(v___x_2761_, 0);
                        v_isSharedCheck_2772_ =
                            (!leanh::lean_is_exclusive(v___x_2761_)) as u8;
                        if v_isSharedCheck_2772_ == 0 {
                            v___x_2764_ = v___x_2761_;
                            v_isShared_2765_ = v_isSharedCheck_2772_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2762_);
                            leanh::lean_dec(v___x_2761_);
                            v___x_2764_ = leanh::lean_box(0);
                            v_isShared_2765_ = v_isSharedCheck_2772_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_prop_2757_);
                        return v___x_2761_;
                    }
                }
            }
            1 => {
                v___x_2766_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2767_ = lean_string_append(v_prop_2757_, v___x_2766_);
                v___x_2768_ = lean_string_append(v___x_2767_, v_a_2762_);
                leanh::lean_dec(v_a_2762_);
                if v_isShared_2765_ == 0 {
                    leanh::lean_ctor_set(v___x_2764_, 0, v___x_2768_);
                    v___x_2770_ = v___x_2764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2771_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
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
    mut v_inst_2773_: *mut leanh::LeanObject,
    mut v_obj_2774_: *mut leanh::LeanObject,
    mut v_prop_2775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2776_ = l_Lake_JsonObject_getAs_x3f___redArg(v_inst_2773_, v_obj_2774_, v_prop_2775_);
    leanh::lean_dec(v_obj_2774_);
    return v_res_2776_;
}
pub unsafe fn l_Lake_JsonObject_getAs_x3f(
    mut v_00_u03b1_2777_: *mut leanh::LeanObject,
    mut v_inst_2778_: *mut leanh::LeanObject,
    mut v_obj_2779_: *mut leanh::LeanObject,
    mut v_prop_2780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2781_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lake_JsonObject_getJson_x3f_spec__0___redArg(v_obj_2779_, v_prop_2780_);
                if leanh::lean_obj_tag(v___x_2781_) == 0 {
                    leanh::lean_dec_ref(v_prop_2780_);
                    leanh::lean_dec_ref(v_inst_2778_);
                    v___x_2782_ = l_Lake_JsonObject_get_x3f___redArg___closed__0;
                    return v___x_2782_;
                } else {
                    v_val_2783_ = leanh::lean_ctor_get(v___x_2781_, 0);
                    leanh::lean_inc(v_val_2783_);
                    leanh::lean_dec_ref_known(v___x_2781_, 1);
                    v___x_2784_ = l_Option_fromJson_x3f___redArg(v_inst_2778_, v_val_2783_);
                    if leanh::lean_obj_tag(v___x_2784_) == 0 {
                        v_a_2785_ = leanh::lean_ctor_get(v___x_2784_, 0);
                        v_isSharedCheck_2795_ =
                            (!leanh::lean_is_exclusive(v___x_2784_)) as u8;
                        if v_isSharedCheck_2795_ == 0 {
                            v___x_2787_ = v___x_2784_;
                            v_isShared_2788_ = v_isSharedCheck_2795_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2785_);
                            leanh::lean_dec(v___x_2784_);
                            v___x_2787_ = leanh::lean_box(0);
                            v_isShared_2788_ = v_isSharedCheck_2795_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_prop_2780_);
                        return v___x_2784_;
                    }
                }
            }
            1 => {
                v___x_2789_ = l_Lake_JsonObject_get___redArg___closed__1;
                v___x_2790_ = lean_string_append(v_prop_2780_, v___x_2789_);
                v___x_2791_ = lean_string_append(v___x_2790_, v_a_2785_);
                leanh::lean_dec(v_a_2785_);
                if v_isShared_2788_ == 0 {
                    leanh::lean_ctor_set(v___x_2787_, 0, v___x_2791_);
                    v___x_2793_ = v___x_2787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2794_, 0, v___x_2791_);
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
    mut v_00_u03b1_2796_: *mut leanh::LeanObject,
    mut v_inst_2797_: *mut leanh::LeanObject,
    mut v_obj_2798_: *mut leanh::LeanObject,
    mut v_prop_2799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2800_ =
        l_Lake_JsonObject_getAs_x3f(v_00_u03b1_2796_, v_inst_2797_, v_obj_2798_, v_prop_2799_);
    leanh::lean_dec(v_obj_2798_);
    return v_res_2800_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_JsonObject(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lake_JsonObject_empty = _init_l_Lake_JsonObject_empty();
    leanh::lean_mark_persistent(l_Lake_JsonObject_empty);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_JsonObject(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_JsonObject(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_JsonObject(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_JsonObject(builtin);
}