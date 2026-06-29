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
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12966880221525079621 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__6_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value)
            as *mut crate::leanh::LeanObject,
        6110315075117401315 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__7_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Grind_NodeDefUnexpander___redArg___closed__1_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12258881440525736719 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_NodeDef_toCtorIdx(
    mut v_x_74_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_75_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_75_;
}
pub unsafe fn l_Lean_Grind_node__def(
    mut v_x_76_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_77_: *mut crate::leanh::LeanObject,
    mut v_a_78_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_79_ = crate::leanh::lean_box(0);
    return v___x_79_;
}
pub unsafe fn l_Lean_Grind_node__def___boxed(
    mut v_x_80_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_81_: *mut crate::leanh::LeanObject,
    mut v_a_82_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_83_ = l_Lean_Grind_node__def(v_x_80_, v_00_u03b1_81_, v_a_82_);
    crate::leanh::lean_dec(v_a_82_);
    crate::leanh::lean_dec(v_x_80_);
    return v_res_83_;
}
pub unsafe fn l_Lean_Grind_nodeDefUnexpander___redArg(
    mut v_stx_97_: *mut crate::leanh::LeanObject,
    mut v_a_98_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_99_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_100_: u8 = 0;
    v___x_99_ = l_Lean_Grind_nodeDefUnexpander___redArg___closed__4;
    crate::leanh::lean_inc(v_stx_97_);
    v___x_100_ = l_Lean_Syntax_isOfKind(v_stx_97_, v___x_99_);
    if v___x_100_ == 0 {
        let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_97_);
        v___x_101_ = crate::leanh::lean_box(0);
        v___x_102_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_102_, 0, v___x_101_);
        crate::leanh::lean_ctor_set(v___x_102_, 1, v_a_98_);
        return v___x_102_;
    } else {
        let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_105_: u8 = 0;
        v___x_103_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_104_ = l_Lean_Syntax_getArg(v_stx_97_, v___x_103_);
        crate::leanh::lean_dec(v_stx_97_);
        crate::leanh::lean_inc(v___x_104_);
        v___x_105_ = l_Lean_Syntax_matchesNull(v___x_104_, v___x_103_);
        if v___x_105_ == 0 {
            let mut v___x_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_104_);
            v___x_106_ = crate::leanh::lean_box(0);
            v___x_107_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_107_, 0, v___x_106_);
            crate::leanh::lean_ctor_set(v___x_107_, 1, v_a_98_);
            return v___x_107_;
        } else {
            let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_id_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_111_: u8 = 0;
            v___x_108_ = crate::leanh::lean_unsigned_to_nat(0);
            v_id_109_ = l_Lean_Syntax_getArg(v___x_104_, v___x_108_);
            crate::leanh::lean_dec(v___x_104_);
            v___x_110_ = l_Lean_Grind_nodeDefUnexpander___redArg___closed__6;
            crate::leanh::lean_inc(v_id_109_);
            v___x_111_ = l_Lean_Syntax_isOfKind(v_id_109_, v___x_110_);
            if v___x_111_ == 0 {
                let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_id_109_);
                v___x_112_ = crate::leanh::lean_box(0);
                v___x_113_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_113_, 0, v___x_112_);
                crate::leanh::lean_ctor_set(v___x_113_, 1, v_a_98_);
                return v___x_113_;
            } else {
                let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_114_ = l_Lean_Grind_nodeDefUnexpander___redArg___closed__7;
                v___x_115_ = l_Lean_TSyntax_getNat(v_id_109_);
                crate::leanh::lean_dec(v_id_109_);
                v___x_116_ = l_Nat_reprFast(v___x_115_);
                v___x_117_ = lean_string_append(v___x_114_, v___x_116_);
                crate::leanh::lean_dec_ref(v___x_116_);
                v___x_118_ = crate::leanh::lean_box(0);
                v___x_119_ = l_Lean_Name_str___override(v___x_118_, v___x_117_);
                v___x_120_ = lean_mk_syntax_ident(v___x_119_);
                v___x_121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_121_, 0, v___x_120_);
                crate::leanh::lean_ctor_set(v___x_121_, 1, v_a_98_);
                return v___x_121_;
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_nodeDefUnexpander(
    mut v_stx_122_: *mut crate::leanh::LeanObject,
    mut v_a_123_: *mut crate::leanh::LeanObject,
    mut v_a_124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_125_ = l_Lean_Grind_nodeDefUnexpander___redArg(v_stx_122_, v_a_124_);
    return v___x_125_;
}
pub unsafe fn l_Lean_Grind_nodeDefUnexpander___boxed(
    mut v_stx_126_: *mut crate::leanh::LeanObject,
    mut v_a_127_: *mut crate::leanh::LeanObject,
    mut v_a_128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_129_ = l_Lean_Grind_nodeDefUnexpander(v_stx_126_, v_a_127_, v_a_128_);
    crate::leanh::lean_dec(v_a_127_);
    return v_res_129_;
}
pub unsafe fn _init_l_Lean_Grind_NodeDefUnexpander___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_134_ = l_Lean_Grind_NodeDefUnexpander___redArg___closed__1;
    v___x_135_ = lean_mk_syntax_ident(v___x_134_);
    return v___x_135_;
}
pub unsafe fn l_Lean_Grind_NodeDefUnexpander___redArg(
    mut v_a_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_137_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__2_once),
        _init_l_Lean_Grind_NodeDefUnexpander___redArg___closed__2,
    );
    v___x_138_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_138_, 0, v___x_137_);
    crate::leanh::lean_ctor_set(v___x_138_, 1, v_a_136_);
    return v___x_138_;
}
pub unsafe fn l_Lean_Grind_NodeDefUnexpander(
    mut v_x_139_: *mut crate::leanh::LeanObject,
    mut v_a_140_: *mut crate::leanh::LeanObject,
    mut v_a_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = l_Lean_Grind_NodeDefUnexpander___redArg(v_a_141_);
    return v___x_142_;
}
pub unsafe fn l_Lean_Grind_NodeDefUnexpander___boxed(
    mut v_x_143_: *mut crate::leanh::LeanObject,
    mut v_a_144_: *mut crate::leanh::LeanObject,
    mut v_a_145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_146_ = l_Lean_Grind_NodeDefUnexpander(v_x_143_, v_a_144_, v_a_145_);
    crate::leanh::lean_dec(v_a_144_);
    crate::leanh::lean_dec(v_x_143_);
    return v_res_146_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_PP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_PP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_PP(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Grind_PP(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Grind_PP(builtin);
}
