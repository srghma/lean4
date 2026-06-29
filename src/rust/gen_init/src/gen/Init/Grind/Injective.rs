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
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
};
pub static l_Lean_Grind_leftInvUnexpander___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__3_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [97, 112, 112, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Grind_leftInvUnexpander___closed__4_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__3_value)
                as *mut crate::leanh::LeanObject,
            12966880221525079621 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__5_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__6_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__5_value)
                as *mut crate::leanh::LeanObject,
            11732532314184152362 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__7_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__8_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__9_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__8_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Grind_leftInvUnexpander(
    mut v_stx_72_: *mut crate::leanh::LeanObject,
    mut v_a_73_: *mut crate::leanh::LeanObject,
    mut v_a_74_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: u8 = 0;
    v___x_75_ = l_Lean_Grind_leftInvUnexpander___closed__4;
    crate::leanh::lean_inc(v_stx_72_);
    v___x_76_ = l_Lean_Syntax_isOfKind(v_stx_72_, v___x_75_);
    if v___x_76_ == 0 {
        let mut v___x_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_72_);
        v___x_77_ = crate::leanh::lean_box(0);
        v___x_78_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_78_, 0, v___x_77_);
        crate::leanh::lean_ctor_set(v___x_78_, 1, v_a_74_);
        return v___x_78_;
    } else {
        let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_83_: u8 = 0;
        v___x_79_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_80_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_81_ = l_Lean_Syntax_getArg(v_stx_72_, v___x_80_);
        crate::leanh::lean_dec(v_stx_72_);
        v___x_82_ = crate::leanh::lean_unsigned_to_nat(2);
        crate::leanh::lean_inc(v___x_81_);
        v___x_83_ = l_Lean_Syntax_matchesNull(v___x_81_, v___x_82_);
        if v___x_83_ == 0 {
            let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_85_: u8 = 0;
            v___x_84_ = crate::leanh::lean_unsigned_to_nat(3);
            crate::leanh::lean_inc(v___x_81_);
            v___x_85_ = l_Lean_Syntax_matchesNull(v___x_81_, v___x_84_);
            if v___x_85_ == 0 {
                let mut v___x_86_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_81_);
                v___x_86_ = crate::leanh::lean_box(0);
                v___x_87_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_87_, 0, v___x_86_);
                crate::leanh::lean_ctor_set(v___x_87_, 1, v_a_74_);
                return v___x_87_;
            } else {
                let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_91_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_93_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_98_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_88_ = l_Lean_Syntax_getArg(v___x_81_, v___x_79_);
                v___x_89_ = l_Lean_Syntax_getArg(v___x_81_, v___x_82_);
                crate::leanh::lean_dec(v___x_81_);
                v___x_90_ = l_Lean_SourceInfo_fromRef(v_a_73_, v___x_83_);
                v___x_91_ = l_Lean_Grind_leftInvUnexpander___closed__6;
                v___x_92_ = l_Lean_Grind_leftInvUnexpander___closed__7;
                crate::leanh::lean_inc_n(v___x_90_, 3);
                v___x_93_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_93_, 0, v___x_90_);
                crate::leanh::lean_ctor_set(v___x_93_, 1, v___x_92_);
                v___x_94_ = l_Lean_Syntax_node2(v___x_90_, v___x_91_, v___x_88_, v___x_93_);
                v___x_95_ = l_Lean_Grind_leftInvUnexpander___closed__9;
                v___x_96_ = l_Lean_Syntax_node1(v___x_90_, v___x_95_, v___x_89_);
                v___x_97_ = l_Lean_Syntax_node2(v___x_90_, v___x_75_, v___x_94_, v___x_96_);
                v___x_98_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_98_, 0, v___x_97_);
                crate::leanh::lean_ctor_set(v___x_98_, 1, v_a_74_);
                return v___x_98_;
            }
        } else {
            let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_100_: u8 = 0;
            let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_99_ = l_Lean_Syntax_getArg(v___x_81_, v___x_79_);
            crate::leanh::lean_dec(v___x_81_);
            v___x_100_ = 0;
            v___x_101_ = l_Lean_SourceInfo_fromRef(v_a_73_, v___x_100_);
            v___x_102_ = l_Lean_Grind_leftInvUnexpander___closed__6;
            v___x_103_ = l_Lean_Grind_leftInvUnexpander___closed__7;
            crate::leanh::lean_inc(v___x_101_);
            v___x_104_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_104_, 0, v___x_101_);
            crate::leanh::lean_ctor_set(v___x_104_, 1, v___x_103_);
            v___x_105_ = l_Lean_Syntax_node2(v___x_101_, v___x_102_, v___x_99_, v___x_104_);
            v___x_106_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_106_, 0, v___x_105_);
            crate::leanh::lean_ctor_set(v___x_106_, 1, v_a_74_);
            return v___x_106_;
        }
    }
}
pub unsafe fn l_Lean_Grind_leftInvUnexpander___boxed(
    mut v_stx_107_: *mut crate::leanh::LeanObject,
    mut v_a_108_: *mut crate::leanh::LeanObject,
    mut v_a_109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_110_ = l_Lean_Grind_leftInvUnexpander(v_stx_107_, v_a_108_, v_a_109_);
    crate::leanh::lean_dec(v_a_108_);
    return v_res_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Injective(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Injective(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Injective(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Injective(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Injective(builtin);
}
