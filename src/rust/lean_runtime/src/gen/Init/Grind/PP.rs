// Lean compiler output
// Module: Init.Grind.PP
// Imports: Init.Data.String.Defs Init.Grind.Tactics
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, meta_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Grind::Tactics::{
    initialize_Init_Grind_Tactics, runtime_initialize_Init_Grind_Tactics,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_TSyntax_getNat, lean_mk_syntax_ident};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Name_str___override, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once,
    lean_unsigned_to_nat,
};
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value: LeanStringObject<5> =
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value: LeanStringObject<7> =
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value: LeanStringObject<5> =
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value: LeanStringObject<4> =
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
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value)
        as *mut LeanObject;
static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__1_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__2_value)
                as *mut LeanObject,
            16572064140653406795 as *mut LeanObject,
        ],
    };
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__3_value)
                as *mut LeanObject,
            12966880221525079621 as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value: LeanStringObject<4> =
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
        m_data: [110, 117, 109, 0],
    };
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__6_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__5_value)
                as *mut LeanObject,
            6110315075117401315 as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Grind_nodeDefUnexpander___redArg___closed__7_value: LeanStringObject<2> =
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
        m_data: [35, 0],
    };
static mut l_Lean_Grind_nodeDefUnexpander___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_nodeDefUnexpander___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_NodeDefUnexpander___redArg___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__0_value)
                as *mut LeanObject,
            12258881440525736719 as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_NodeDefUnexpander___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_NodeDef_toCtorIdx(mut v_x_74_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_75_: *mut LeanObject = core::ptr::null_mut();
    v___x_75_ = lean_unsigned_to_nat(0);
    return v___x_75_;
}
pub unsafe fn l_Lean_Grind_node__def(
    mut v_x_76_: *mut LeanObject,
    mut v_00_u03b1_77_: *mut LeanObject,
    mut v_a_78_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_79_: *mut LeanObject = core::ptr::null_mut();
    v___x_79_ = lean_box(0);
    return v___x_79_;
}
pub unsafe fn l_Lean_Grind_node__def___boxed(
    mut v_x_80_: *mut LeanObject,
    mut v_00_u03b1_81_: *mut LeanObject,
    mut v_a_82_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_83_: *mut LeanObject = core::ptr::null_mut();
    v_res_83_ = l_Lean_Grind_node__def(v_x_80_, v_00_u03b1_81_, v_a_82_);
    lean_dec(v_a_82_);
    lean_dec(v_x_80_);
    return v_res_83_;
}
pub unsafe fn l_Lean_Grind_nodeDefUnexpander___redArg(
    mut v_stx_97_: *mut LeanObject,
    mut v_a_98_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_100_: u8 = 0;
    v___x_99_ = l_Lean_Grind_nodeDefUnexpander___redArg___closed__4;
    lean_inc(v_stx_97_);
    v___x_100_ = l_Lean_Syntax_isOfKind(v_stx_97_, v___x_99_);
    if v___x_100_ == 0 {
        let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_97_);
        v___x_101_ = lean_box(0);
        v___x_102_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_102_, 0, v___x_101_);
        lean_ctor_set(v___x_102_, 1, v_a_98_);
        return v___x_102_;
    } else {
        let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_105_: u8 = 0;
        v___x_103_ = lean_unsigned_to_nat(1);
        v___x_104_ = l_Lean_Syntax_getArg(v_stx_97_, v___x_103_);
        lean_dec(v_stx_97_);
        lean_inc(v___x_104_);
        v___x_105_ = l_Lean_Syntax_matchesNull(v___x_104_, v___x_103_);
        if v___x_105_ == 0 {
            let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_104_);
            v___x_106_ = lean_box(0);
            v___x_107_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_107_, 0, v___x_106_);
            lean_ctor_set(v___x_107_, 1, v_a_98_);
            return v___x_107_;
        } else {
            let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
            let mut v_id_109_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_111_: u8 = 0;
            v___x_108_ = lean_unsigned_to_nat(0);
            v_id_109_ = l_Lean_Syntax_getArg(v___x_104_, v___x_108_);
            lean_dec(v___x_104_);
            v___x_110_ = l_Lean_Grind_nodeDefUnexpander___redArg___closed__6;
            lean_inc(v_id_109_);
            v___x_111_ = l_Lean_Syntax_isOfKind(v_id_109_, v___x_110_);
            if v___x_111_ == 0 {
                let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_id_109_);
                v___x_112_ = lean_box(0);
                v___x_113_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_113_, 0, v___x_112_);
                lean_ctor_set(v___x_113_, 1, v_a_98_);
                return v___x_113_;
            } else {
                let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
                v___x_114_ = l_Lean_Grind_nodeDefUnexpander___redArg___closed__7;
                v___x_115_ = l_Lean_TSyntax_getNat(v_id_109_);
                lean_dec(v_id_109_);
                v___x_116_ = l_Nat_reprFast(v___x_115_);
                v___x_117_ = lean_string_append(v___x_114_, v___x_116_);
                lean_dec_ref(v___x_116_);
                v___x_118_ = lean_box(0);
                v___x_119_ = l_Lean_Name_str___override(v___x_118_, v___x_117_);
                v___x_120_ = lean_mk_syntax_ident(v___x_119_);
                v___x_121_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_121_, 0, v___x_120_);
                lean_ctor_set(v___x_121_, 1, v_a_98_);
                return v___x_121_;
            }
        }
    }
}
pub unsafe fn l_Lean_Grind_nodeDefUnexpander(
    mut v_stx_122_: *mut LeanObject,
    mut v_a_123_: *mut LeanObject,
    mut v_a_124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
    v___x_125_ = l_Lean_Grind_nodeDefUnexpander___redArg(v_stx_122_, v_a_124_);
    return v___x_125_;
}
pub unsafe fn l_Lean_Grind_nodeDefUnexpander___boxed(
    mut v_stx_126_: *mut LeanObject,
    mut v_a_127_: *mut LeanObject,
    mut v_a_128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_129_: *mut LeanObject = core::ptr::null_mut();
    v_res_129_ = l_Lean_Grind_nodeDefUnexpander(v_stx_126_, v_a_127_, v_a_128_);
    lean_dec(v_a_127_);
    return v_res_129_;
}
pub unsafe fn _init_l_Lean_Grind_NodeDefUnexpander___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
    v___x_134_ = l_Lean_Grind_NodeDefUnexpander___redArg___closed__1;
    v___x_135_ = lean_mk_syntax_ident(v___x_134_);
    return v___x_135_;
}
pub unsafe fn l_Lean_Grind_NodeDefUnexpander___redArg(
    mut v_a_136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
    v___x_137_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Grind_NodeDefUnexpander___redArg___closed__2_once),
        _init_l_Lean_Grind_NodeDefUnexpander___redArg___closed__2,
    );
    v___x_138_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_138_, 0, v___x_137_);
    lean_ctor_set(v___x_138_, 1, v_a_136_);
    return v___x_138_;
}
pub unsafe fn l_Lean_Grind_NodeDefUnexpander(
    mut v_x_139_: *mut LeanObject,
    mut v_a_140_: *mut LeanObject,
    mut v_a_141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
    v___x_142_ = l_Lean_Grind_NodeDefUnexpander___redArg(v_a_141_);
    return v___x_142_;
}
pub unsafe fn l_Lean_Grind_NodeDefUnexpander___boxed(
    mut v_x_143_: *mut LeanObject,
    mut v_a_144_: *mut LeanObject,
    mut v_a_145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_146_: *mut LeanObject = core::ptr::null_mut();
    v_res_146_ = l_Lean_Grind_NodeDefUnexpander(v_x_143_, v_a_144_, v_a_145_);
    lean_dec(v_a_144_);
    lean_dec(v_x_143_);
    return v_res_146_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_PP(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_PP(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_PP(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Defs(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Tactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_PP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_PP(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_PP(builtin);
}
