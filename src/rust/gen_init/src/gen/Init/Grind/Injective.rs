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
pub static l_Lean_Grind_leftInvUnexpander___closed__0_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__1_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__3_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__0_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__1_value)
                as *mut leanh::LeanObject,
            8018486133748762727 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__2_value)
                as *mut leanh::LeanObject,
            16572064140653406795 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Grind_leftInvUnexpander___closed__4_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__3_value)
                as *mut leanh::LeanObject,
            12966880221525079621 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__5_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__6_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__5_value)
                as *mut leanh::LeanObject,
            11732532314184152362 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__7_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__8_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Grind_leftInvUnexpander___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_leftInvUnexpander___closed__9_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__8_value)
                as *mut leanh::LeanObject,
            9855511589286918680 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Grind_leftInvUnexpander___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_leftInvUnexpander___closed__9_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Grind_leftInvUnexpander(
    mut v_stx_72_: *mut leanh::LeanObject,
    mut v_a_73_: *mut leanh::LeanObject,
    mut v_a_74_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: u8 = 0;
    v___x_75_ = l_Lean_Grind_leftInvUnexpander___closed__4;
    leanh::lean_inc(v_stx_72_);
    v___x_76_ = l_Lean_Syntax_isOfKind(v_stx_72_, v___x_75_);
    if v___x_76_ == 0 {
        let mut v___x_77_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_78_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_72_);
        v___x_77_ = leanh::lean_box(0);
        v___x_78_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_78_, 0, v___x_77_);
        leanh::lean_ctor_set(v___x_78_, 1, v_a_74_);
        return v___x_78_;
    } else {
        let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_80_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_81_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_82_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_83_: u8 = 0;
        v___x_79_ = leanh::lean_unsigned_to_nat(0);
        v___x_80_ = leanh::lean_unsigned_to_nat(1);
        v___x_81_ = l_Lean_Syntax_getArg(v_stx_72_, v___x_80_);
        leanh::lean_dec(v_stx_72_);
        v___x_82_ = leanh::lean_unsigned_to_nat(2);
        leanh::lean_inc(v___x_81_);
        v___x_83_ = l_Lean_Syntax_matchesNull(v___x_81_, v___x_82_);
        if v___x_83_ == 0 {
            let mut v___x_84_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_85_: u8 = 0;
            v___x_84_ = leanh::lean_unsigned_to_nat(3);
            leanh::lean_inc(v___x_81_);
            v___x_85_ = l_Lean_Syntax_matchesNull(v___x_81_, v___x_84_);
            if v___x_85_ == 0 {
                let mut v___x_86_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_87_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v___x_81_);
                v___x_86_ = leanh::lean_box(0);
                v___x_87_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_87_, 0, v___x_86_);
                leanh::lean_ctor_set(v___x_87_, 1, v_a_74_);
                return v___x_87_;
            } else {
                let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_90_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_91_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_92_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_93_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_94_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_95_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_97_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_98_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_88_ = l_Lean_Syntax_getArg(v___x_81_, v___x_79_);
                v___x_89_ = l_Lean_Syntax_getArg(v___x_81_, v___x_82_);
                leanh::lean_dec(v___x_81_);
                v___x_90_ = l_Lean_SourceInfo_fromRef(v_a_73_, v___x_83_);
                v___x_91_ = l_Lean_Grind_leftInvUnexpander___closed__6;
                v___x_92_ = l_Lean_Grind_leftInvUnexpander___closed__7;
                leanh::lean_inc_n(v___x_90_, 3);
                v___x_93_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_93_, 0, v___x_90_);
                leanh::lean_ctor_set(v___x_93_, 1, v___x_92_);
                v___x_94_ = l_Lean_Syntax_node2(v___x_90_, v___x_91_, v___x_88_, v___x_93_);
                v___x_95_ = l_Lean_Grind_leftInvUnexpander___closed__9;
                v___x_96_ = l_Lean_Syntax_node1(v___x_90_, v___x_95_, v___x_89_);
                v___x_97_ = l_Lean_Syntax_node2(v___x_90_, v___x_75_, v___x_94_, v___x_96_);
                v___x_98_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_98_, 0, v___x_97_);
                leanh::lean_ctor_set(v___x_98_, 1, v_a_74_);
                return v___x_98_;
            }
        } else {
            let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_100_: u8 = 0;
            let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_105_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_99_ = l_Lean_Syntax_getArg(v___x_81_, v___x_79_);
            leanh::lean_dec(v___x_81_);
            v___x_100_ = 0;
            v___x_101_ = l_Lean_SourceInfo_fromRef(v_a_73_, v___x_100_);
            v___x_102_ = l_Lean_Grind_leftInvUnexpander___closed__6;
            v___x_103_ = l_Lean_Grind_leftInvUnexpander___closed__7;
            leanh::lean_inc(v___x_101_);
            v___x_104_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_104_, 0, v___x_101_);
            leanh::lean_ctor_set(v___x_104_, 1, v___x_103_);
            v___x_105_ = l_Lean_Syntax_node2(v___x_101_, v___x_102_, v___x_99_, v___x_104_);
            v___x_106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_106_, 0, v___x_105_);
            leanh::lean_ctor_set(v___x_106_, 1, v_a_74_);
            return v___x_106_;
        }
    }
}
pub unsafe fn l_Lean_Grind_leftInvUnexpander___boxed(
    mut v_stx_107_: *mut leanh::LeanObject,
    mut v_a_108_: *mut leanh::LeanObject,
    mut v_a_109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_110_ = l_Lean_Grind_leftInvUnexpander(v_stx_107_, v_a_108_, v_a_109_);
    leanh::lean_dec(v_a_108_);
    return v_res_110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_Injective(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_Injective(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_Injective(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Function(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Injective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_Injective(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Grind_Injective(builtin);
}