// Lean compiler output
// Module: Init.Grind.PP
// Imports: Init.Data.String.Defs Init.Grind.Tactics
use crate::ffi::lean_string_append;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_TSyntax_getNat, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_str___override, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull,
};
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value)
            as *mut leanh::LeanObject,
        16572064140653406795 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value)
            as *mut leanh::LeanObject,
        12966880221525079621 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 117, 109, 0],
};
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__6_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value)
            as *mut leanh::LeanObject,
        6110315075117401315 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__7_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [35, 0],
};
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [78, 111, 100, 101, 68, 101, 102, 0],
};
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Grind_NodeDefUnexpander___redArg___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value)
            as *mut leanh::LeanObject,
        12258881440525736719 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_NodeDef_toCtorIdx(
    mut v_x_74_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_75_ = leanh::lean_unsigned_to_nat(0);
    return v___x_75_;
}
pub unsafe fn l_Lean_Grind_node__def(
    mut v_x_76_: *mut leanh::LeanObject,
    mut v_00_u03b1_77_: *mut leanh::LeanObject,
    mut v_a_78_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_79_ = leanh::lean_box(0);
    return v___x_79_;
}
pub unsafe fn l_Lean_Grind_node__def___boxed(
    mut v_x_80_: *mut leanh::LeanObject,
    mut v_00_u03b1_81_: *mut leanh::LeanObject,
    mut v_a_82_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_83_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_83_ = l_Lean_Grind_node__def(v_x_80_, v_00_u03b1_81_, v_a_82_);
    leanh::lean_dec(v_a_82_);
    leanh::lean_dec(v_x_80_);
    return v_res_83_;
}
pub unsafe fn l_Lean_Grind_nodeDefUnexpander___redArg(
    mut v_stx_97_: *mut leanh::LeanObject,
    mut v_a_98_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_99_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: u8 = 0;
    v___x_99_ = l_Lean_Grind_nodeDefUnexpander___redArg___closed__4;
    leanh::lean_inc(v_stx_97_);
    v___x_100_ = l_Lean_Syntax_isOfKind(v_stx_97_, v___x_99_);
    if v___x_100_ == 0 {
        let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_97_);
        v___x_101_ = leanh::lean_box(0);
        v___x_102_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_102_, 0, v___x_101_);
        leanh::lean_ctor_set(v___x_102_, 1, v_a_98_);
        return v___x_102_;
    } else {
        let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_105_: u8 = 0;
        v___x_103_ = leanh::lean_unsigned_to_nat(1);
        v___x_104_ = l_Lean_Syntax_getArg(v_stx_97_, v___x_103_);
        leanh::lean_dec(v_stx_97_);
        leanh::lean_inc(v___x_104_);
        v___x_105_ = l_Lean_Syntax_matchesNull(v___x_104_, v___x_103_);
        if v___x_105_ == 0 {
            let mut v___x_106_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_104_);
            v___x_106_ = leanh::lean_box(0);
            v___x_107_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_107_, 0, v___x_106_);
            leanh::lean_ctor_set(v___x_107_, 1, v_a_98_);
            return v___x_107_;
        } else {
            let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_109_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_111_: u8 = 0;
            v___x_108_ = leanh::lean_unsigned_to_nat(0);
            v_id_109_ = l_Lean_Syntax_getArg(v___x_104_, v___x_108_);
            leanh::lean_dec(v___x_104_);
            v___x_110_ = l_Lean_Grind_nodeDefUnexpander___redArg___closed__6;
            leanh::lean_inc(v_id_109_);
            v___x_111_ = l_Lean_Syntax_isOfKind(v_id_109_, v___x_110_);
            if v___x_111_ == 0 {
                let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_id_109_);
                v___x_112_ = leanh::lean_box(0);
                v___x_113_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_113_, 0, v___x_112_);
                leanh::lean_ctor_set(v___x_113_, 1, v_a_98_);
                return v___x_113_;
            } else {
                let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_117_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_121_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_114_ = l_Lean_Grind_nodeDefUnexpander___redArg___closed__7;
                v___x_115_ = l_Lean_TSyntax_getNat(v_id_109_);
                leanh::lean_dec(v_id_109_);
                v___x_116_ = l_Nat_reprFast(v___x_115_);
                v___x_117_ = lean_string_append(v___x_114_, v___x_116_);
                leanh::lean_dec_ref(v___x_116_);
                v___x_118_ = leanh::lean_box(0);
                v___x_119_ = l_Lean_Name_str___override(v___x_118_, v___x_117_);
                v___x_120_ = lean_mk_syntax_ident(v___x_119_);
                v___x_121_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_121_, 0, v___x_120_);
                leanh::lean_ctor_set(v___x_121_, 1, v_a_98_);
                return v___x_121_;
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_nodeDefUnexpander(
    mut v_stx_122_: *mut leanh::LeanObject,
    mut v_a_123_: *mut leanh::LeanObject,
    mut v_a_124_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_125_ = l_Lean_Grind_nodeDefUnexpander___redArg(v_stx_122_, v_a_124_);
    return v___x_125_;
}
pub unsafe fn l_Lean_Grind_nodeDefUnexpander___boxed(
    mut v_stx_126_: *mut leanh::LeanObject,
    mut v_a_127_: *mut leanh::LeanObject,
    mut v_a_128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_129_ = l_Lean_Grind_nodeDefUnexpander(v_stx_126_, v_a_127_, v_a_128_);
    leanh::lean_dec(v_a_127_);
    return v_res_129_;
}
pub unsafe fn _init_l_Lean_Grind_NodeDefUnexpander___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_134_ = l_Lean_Grind_NodeDefUnexpander___redArg___closed__1;
    v___x_135_ = lean_mk_syntax_ident(v___x_134_);
    return v___x_135_;
}
pub unsafe fn l_Lean_Grind_NodeDefUnexpander___redArg(
    mut v_a_136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_137_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__2_once),
        _init_l_Lean_Grind_NodeDefUnexpander___redArg___closed__2,
    );
    v___x_138_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_138_, 0, v___x_137_);
    leanh::lean_ctor_set(v___x_138_, 1, v_a_136_);
    return v___x_138_;
}
pub unsafe fn l_Lean_Grind_NodeDefUnexpander(
    mut v_x_139_: *mut leanh::LeanObject,
    mut v_a_140_: *mut leanh::LeanObject,
    mut v_a_141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = l_Lean_Grind_NodeDefUnexpander___redArg(v_a_141_);
    return v___x_142_;
}
pub unsafe fn l_Lean_Grind_NodeDefUnexpander___boxed(
    mut v_x_143_: *mut leanh::LeanObject,
    mut v_a_144_: *mut leanh::LeanObject,
    mut v_a_145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_146_ = l_Lean_Grind_NodeDefUnexpander(v_x_143_, v_a_144_, v_a_145_);
    leanh::lean_dec(v_a_144_);
    leanh::lean_dec(v_x_143_);
    return v_res_146_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_PP(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_PP(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_PP(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_PP(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Grind_PP(builtin);
}