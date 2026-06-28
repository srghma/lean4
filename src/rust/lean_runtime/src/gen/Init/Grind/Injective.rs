// Lean compiler output
// Module: Init.Grind.Injective
// Imports: Init.Data.Function Init.NotationExtra Init.Classical
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Function::{
    initialize_Init_Data_Function, runtime_initialize_Init_Data_Function,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_inc_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_unsigned_to_nat,
};
pub static l_Lean_Grind_leftInvUnexpander___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__1_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__2_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__3_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [97, 112, 112, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__3_value) as *mut LeanObject;
static l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__2_value) as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Grind_leftInvUnexpander___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__3_value) as *mut LeanObject,
        12966880221525079621 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_leftInvUnexpander___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__5_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 7,
        m_data: [116, 101, 114, 109, 95, 226, 129, 187, 194, 185, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__5_value) as *mut LeanObject,
        11732532314184152362 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_leftInvUnexpander___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__7_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 2,
        m_data: [226, 129, 187, 194, 185, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__8_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__8_value) as *mut LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__8_value) as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_leftInvUnexpander___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__9_value) as *mut LeanObject;
pub unsafe fn l_Lean_Grind_leftInvUnexpander(
    mut v_stx_72_: *mut LeanObject,
    mut v_a_73_: *mut LeanObject,
    mut v_a_74_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_76_: u8 = 0;
    v___x_75_ = l_Lean_Grind_leftInvUnexpander___closed__4;
    lean_inc(v_stx_72_);
    v___x_76_ = l_Lean_Syntax_isOfKind(v_stx_72_, v___x_75_);
    if v___x_76_ == 0 {
        let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_72_);
        v___x_77_ = lean_box(0);
        v___x_78_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_78_, 0, v___x_77_);
        lean_ctor_set(v___x_78_, 1, v_a_74_);
        return v___x_78_;
    } else {
        let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_80_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_81_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_83_: u8 = 0;
        v___x_79_ = lean_unsigned_to_nat(0);
        v___x_80_ = lean_unsigned_to_nat(1);
        v___x_81_ = l_Lean_Syntax_getArg(v_stx_72_, v___x_80_);
        lean_dec(v_stx_72_);
        v___x_82_ = lean_unsigned_to_nat(2);
        lean_inc(v___x_81_);
        v___x_83_ = l_Lean_Syntax_matchesNull(v___x_81_, v___x_82_);
        if v___x_83_ == 0 {
            let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_85_: u8 = 0;
            v___x_84_ = lean_unsigned_to_nat(3);
            lean_inc(v___x_81_);
            v___x_85_ = l_Lean_Syntax_matchesNull(v___x_81_, v___x_84_);
            if v___x_85_ == 0 {
                let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_87_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v___x_81_);
                v___x_86_ = lean_box(0);
                v___x_87_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_87_, 0, v___x_86_);
                lean_ctor_set(v___x_87_, 1, v_a_74_);
                return v___x_87_;
            } else {
                let mut v___x_88_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_90_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_92_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
                v___x_88_ = l_Lean_Syntax_getArg(v___x_81_, v___x_79_);
                v___x_89_ = l_Lean_Syntax_getArg(v___x_81_, v___x_82_);
                lean_dec(v___x_81_);
                v___x_90_ = l_Lean_SourceInfo_fromRef(v_a_73_, v___x_83_);
                v___x_91_ = l_Lean_Grind_leftInvUnexpander___closed__6;
                v___x_92_ = l_Lean_Grind_leftInvUnexpander___closed__7;
                lean_inc_n(v___x_90_, 3);
                v___x_93_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_93_, 0, v___x_90_);
                lean_ctor_set(v___x_93_, 1, v___x_92_);
                v___x_94_ = l_Lean_Syntax_node2(v___x_90_, v___x_91_, v___x_88_, v___x_93_);
                v___x_95_ = l_Lean_Grind_leftInvUnexpander___closed__9;
                v___x_96_ = l_Lean_Syntax_node1(v___x_90_, v___x_95_, v___x_89_);
                v___x_97_ = l_Lean_Syntax_node2(v___x_90_, v___x_75_, v___x_94_, v___x_96_);
                v___x_98_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_98_, 0, v___x_97_);
                lean_ctor_set(v___x_98_, 1, v_a_74_);
                return v___x_98_;
            }
        } else {
            let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_100_: u8 = 0;
            let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
            v___x_99_ = l_Lean_Syntax_getArg(v___x_81_, v___x_79_);
            lean_dec(v___x_81_);
            v___x_100_ = 0;
            v___x_101_ = l_Lean_SourceInfo_fromRef(v_a_73_, v___x_100_);
            v___x_102_ = l_Lean_Grind_leftInvUnexpander___closed__6;
            v___x_103_ = l_Lean_Grind_leftInvUnexpander___closed__7;
            lean_inc(v___x_101_);
            v___x_104_ = lean_alloc_ctor(2, 2, (0) as u32);
            lean_ctor_set(v___x_104_, 0, v___x_101_);
            lean_ctor_set(v___x_104_, 1, v___x_103_);
            v___x_105_ = l_Lean_Syntax_node2(v___x_101_, v___x_102_, v___x_99_, v___x_104_);
            v___x_106_ = lean_alloc_ctor(0, 2, (0) as u32);
            lean_ctor_set(v___x_106_, 0, v___x_105_);
            lean_ctor_set(v___x_106_, 1, v_a_74_);
            return v___x_106_;
        }
    }
}
pub unsafe fn l_Lean_Grind_leftInvUnexpander___boxed(
    mut v_stx_107_: *mut LeanObject,
    mut v_a_108_: *mut LeanObject,
    mut v_a_109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_110_: *mut LeanObject = core::ptr::null_mut();
    v_res_110_ = l_Lean_Grind_leftInvUnexpander(v_stx_107_, v_a_108_, v_a_109_);
    lean_dec(v_a_108_);
    return v_res_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Injective(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Injective(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Injective(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Function(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Injective(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_Injective(builtin);
}
