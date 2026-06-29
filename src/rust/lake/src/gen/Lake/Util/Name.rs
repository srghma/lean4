// Lean compiler output
// Module: Lake.Util.Name
// Imports: Lean.Data.Json Lake.Util.RBArray Init.Data.Ord.UInt Init.Prelude Lean.Data.Name
use crate::r#gen::Init::Data::Ord::UInt::{
    initialize_Init_Data_Ord_UInt, runtime_initialize_Init_Data_Ord_UInt,
};
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_copyHeadTailInfoFrom,
    l_Lean_Syntax_mkNameLit, l_Lean_Syntax_setHeadInfo, l_Lean_quoteNameMk, l_String_toName,
};
use crate::r#gen::Init::Prelude::{
    initialize_Init_Prelude, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_SourceInfo_fromRef, l_id___boxed, runtime_initialize_Init_Prelude,
};
use crate::r#gen::Lake::Util::RBArray::{
    initialize_Lake_Util_RBArray, l_Lake_RBArray_empty, runtime_initialize_Lake_Util_RBArray,
};
use crate::r#gen::Lean::Data::Json::{
    initialize_Lean_Data_Json, runtime_initialize_Lean_Data_Json,
};
use crate::r#gen::Lean::Data::Name::{
    initialize_Lean_Data_Name, l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed,
    l_Lean_Name_isAnonymous, runtime_initialize_Lean_Data_Name,
};
use crate::ffi::{
    lean_string_append, lean_string_intercalate,
};
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity};
pub static l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0_value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_id___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_OrdNameMap_empty___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_OrdNameMap_empty___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_OrdNameMap_empty___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_OrdNameMap_empty___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_OrdNameMap_empty___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lake_Name_quoteFrom___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_Name_quoteFrom___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Name_quoteFrom___closed__1_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lake_Name_quoteFrom___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Name_quoteFrom___closed__2_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lake_Name_quoteFrom___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Name_quoteFrom___closed__3_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0],
    };
static mut l_Lake_Name_quoteFrom___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__3_value) as *mut crate::leanh::LeanObject;
static l_Lake_Name_quoteFrom___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Name_quoteFrom___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lake_Name_quoteFrom___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__2_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lake_Name_quoteFrom___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__3_value)
                as *mut crate::leanh::LeanObject,
            9368229134555052249 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_Name_quoteFrom___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Name_quoteFrom___closed__5_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lake_Name_quoteFrom___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_Name_quoteFrom___closed__6_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lake_Name_quoteFrom___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Name_quoteFrom___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_stringToLegalOrSimpleName(
    mut v_s_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: u8 = 0;
    crate::leanh::lean_inc_ref(v_s_225_);
    v___x_226_ = l_String_toName(v_s_225_);
    v___x_227_ = l_Lean_Name_isAnonymous(v___x_226_);
    if v___x_227_ == 0 {
        crate::leanh::lean_dec_ref(v_s_225_);
        return v___x_226_;
    } else {
        let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_226_);
        v___x_228_ = crate::leanh::lean_box(0);
        v___x_229_ = l_Lean_Name_str___override(v___x_228_, v_s_225_);
        return v___x_229_;
    }
}
pub unsafe fn l_Lake_NameMap_empty(
    mut v___y_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = crate::leanh::lean_box(1);
    return v___x_231_;
}
pub unsafe fn l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake(
    mut v_00_u03b1_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ =
        l___private_Lake_Util_Name_0__Lake_instCoeTreeMapNameQuickCmpNameMap__lake___closed__0;
    return v___x_234_;
}
pub unsafe fn _init_l_Lake_OrdNameMap_empty___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_236_ = l_Lake_OrdNameMap_empty___closed__0;
    v___x_237_ = l_Lake_RBArray_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_236_,
    );
    return v___x_237_;
}
pub unsafe fn l_Lake_OrdNameMap_empty(
    mut v_00_u03b1_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_239_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdNameMap_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_OrdNameMap_empty___closed__1_once),
        _init_l_Lake_OrdNameMap_empty___closed__1,
    );
    return v___x_239_;
}
pub unsafe fn l_Lake_mkOrdNameMap(
    mut v_00_u03b1_240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_241_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_OrdNameMap_empty___closed__1),
        core::ptr::addr_of_mut!(l_Lake_OrdNameMap_empty___closed__1_once),
        _init_l_Lake_OrdNameMap_empty___closed__1,
    );
    return v___x_241_;
}
pub unsafe fn l_Lake_DNameMap_empty(
    mut v_00_u03b1_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_243_ = crate::leanh::lean_box(1);
    return v___x_243_;
}
pub unsafe fn l_Lake_Name_eraseHead(
    mut v_x_244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_244_) {
        0 => {
            return v_x_244_;
        }
        1 => {
            let mut v_pre_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pre_245_ = crate::leanh::lean_ctor_get(v_x_244_, 0);
            crate::leanh::lean_inc(v_pre_245_);
            if crate::leanh::lean_obj_tag(v_pre_245_) == 0 {
                crate::leanh::lean_dec_ref_known(v_x_244_, 2);
                return v_pre_245_;
            } else {
                let mut v_str_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_str_246_ = crate::leanh::lean_ctor_get(v_x_244_, 1);
                crate::leanh::lean_inc_ref(v_str_246_);
                crate::leanh::lean_dec_ref_known(v_x_244_, 2);
                v___x_247_ = l_Lake_Name_eraseHead(v_pre_245_);
                v___x_248_ = l_Lean_Name_str___override(v___x_247_, v_str_246_);
                return v___x_248_;
            }
        }
        _ => {
            let mut v_pre_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pre_249_ = crate::leanh::lean_ctor_get(v_x_244_, 0);
            crate::leanh::lean_inc(v_pre_249_);
            if crate::leanh::lean_obj_tag(v_pre_249_) == 0 {
                crate::leanh::lean_dec_ref_known(v_x_244_, 2);
                return v_pre_249_;
            } else {
                let mut v_i_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_i_250_ = crate::leanh::lean_ctor_get(v_x_244_, 1);
                crate::leanh::lean_inc(v_i_250_);
                crate::leanh::lean_dec_ref_known(v_x_244_, 2);
                v___x_251_ = l_Lake_Name_eraseHead(v_pre_249_);
                v___x_252_ = l_Lean_Name_num___override(v___x_251_, v_i_250_);
                return v___x_252_;
            }
        }
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter___redArg(
    mut v_x_253_: *mut crate::leanh::LeanObject,
    mut v_h__1_254_: *mut crate::leanh::LeanObject,
    mut v_h__2_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_253_) == 0 {
        let mut v___x_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_255_);
        v___x_256_ = crate::leanh::lean_box(0);
        v___x_257_ = crate::leanh::lean_apply_1(v_h__1_254_, v___x_256_);
        return v___x_257_;
    } else {
        let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_254_);
        v___x_258_ = crate::leanh::lean_apply_2(v_h__2_255_, v_x_253_, crate::leanh::lean_box(0));
        return v___x_258_;
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_isAnonymous_match__1_splitter(
    mut v_motive_259_: *mut crate::leanh::LeanObject,
    mut v_x_260_: *mut crate::leanh::LeanObject,
    mut v_h__1_261_: *mut crate::leanh::LeanObject,
    mut v_h__2_262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_260_) == 0 {
        let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_262_);
        v___x_263_ = crate::leanh::lean_box(0);
        v___x_264_ = crate::leanh::lean_apply_1(v_h__1_261_, v___x_263_);
        return v___x_264_;
    } else {
        let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_261_);
        v___x_265_ = crate::leanh::lean_apply_2(v_h__2_262_, v_x_260_, crate::leanh::lean_box(0));
        return v___x_265_;
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter___redArg(
    mut v_x_266_: *mut crate::leanh::LeanObject,
    mut v_x_267_: *mut crate::leanh::LeanObject,
    mut v_h__1_268_: *mut crate::leanh::LeanObject,
    mut v_h__2_269_: *mut crate::leanh::LeanObject,
    mut v_h__3_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_267_) {
        0 => {
            let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_270_);
            crate::leanh::lean_dec(v_h__2_269_);
            v___x_271_ = crate::leanh::lean_apply_1(v_h__1_268_, v_x_266_);
            return v___x_271_;
        }
        1 => {
            let mut v_pre_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_269_);
            crate::leanh::lean_dec(v_h__1_268_);
            v_pre_272_ = crate::leanh::lean_ctor_get(v_x_267_, 0);
            crate::leanh::lean_inc(v_pre_272_);
            v_str_273_ = crate::leanh::lean_ctor_get(v_x_267_, 1);
            crate::leanh::lean_inc_ref(v_str_273_);
            crate::leanh::lean_dec_ref_known(v_x_267_, 2);
            v___x_274_ = crate::leanh::lean_apply_3(v_h__3_270_, v_x_266_, v_pre_272_, v_str_273_);
            return v___x_274_;
        }
        _ => {
            let mut v_pre_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_270_);
            crate::leanh::lean_dec(v_h__1_268_);
            v_pre_275_ = crate::leanh::lean_ctor_get(v_x_267_, 0);
            crate::leanh::lean_inc(v_pre_275_);
            v_i_276_ = crate::leanh::lean_ctor_get(v_x_267_, 1);
            crate::leanh::lean_inc(v_i_276_);
            crate::leanh::lean_dec_ref_known(v_x_267_, 2);
            v___x_277_ = crate::leanh::lean_apply_3(v_h__2_269_, v_x_266_, v_pre_275_, v_i_276_);
            return v___x_277_;
        }
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_isPrefixOf_match__1_splitter(
    mut v_motive_278_: *mut crate::leanh::LeanObject,
    mut v_x_279_: *mut crate::leanh::LeanObject,
    mut v_x_280_: *mut crate::leanh::LeanObject,
    mut v_h__1_281_: *mut crate::leanh::LeanObject,
    mut v_h__2_282_: *mut crate::leanh::LeanObject,
    mut v_h__3_283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_280_) {
        0 => {
            let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_283_);
            crate::leanh::lean_dec(v_h__2_282_);
            v___x_284_ = crate::leanh::lean_apply_1(v_h__1_281_, v_x_279_);
            return v___x_284_;
        }
        1 => {
            let mut v_pre_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_282_);
            crate::leanh::lean_dec(v_h__1_281_);
            v_pre_285_ = crate::leanh::lean_ctor_get(v_x_280_, 0);
            crate::leanh::lean_inc(v_pre_285_);
            v_str_286_ = crate::leanh::lean_ctor_get(v_x_280_, 1);
            crate::leanh::lean_inc_ref(v_str_286_);
            crate::leanh::lean_dec_ref_known(v_x_280_, 2);
            v___x_287_ = crate::leanh::lean_apply_3(v_h__3_283_, v_x_279_, v_pre_285_, v_str_286_);
            return v___x_287_;
        }
        _ => {
            let mut v_pre_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_283_);
            crate::leanh::lean_dec(v_h__1_281_);
            v_pre_288_ = crate::leanh::lean_ctor_get(v_x_280_, 0);
            crate::leanh::lean_inc(v_pre_288_);
            v_i_289_ = crate::leanh::lean_ctor_get(v_x_280_, 1);
            crate::leanh::lean_inc(v_i_289_);
            crate::leanh::lean_dec_ref_known(v_x_280_, 2);
            v___x_290_ = crate::leanh::lean_apply_3(v_h__2_282_, v_x_279_, v_pre_288_, v_i_289_);
            return v___x_290_;
        }
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter___redArg(
    mut v_x_291_: *mut crate::leanh::LeanObject,
    mut v_x_292_: *mut crate::leanh::LeanObject,
    mut v_h__1_293_: *mut crate::leanh::LeanObject,
    mut v_h__2_294_: *mut crate::leanh::LeanObject,
    mut v_h__3_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_292_) {
        0 => {
            let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_295_);
            crate::leanh::lean_dec(v_h__2_294_);
            v___x_296_ = crate::leanh::lean_apply_1(v_h__1_293_, v_x_291_);
            return v___x_296_;
        }
        1 => {
            let mut v_pre_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_295_);
            crate::leanh::lean_dec(v_h__1_293_);
            v_pre_297_ = crate::leanh::lean_ctor_get(v_x_292_, 0);
            crate::leanh::lean_inc(v_pre_297_);
            v_str_298_ = crate::leanh::lean_ctor_get(v_x_292_, 1);
            crate::leanh::lean_inc_ref(v_str_298_);
            crate::leanh::lean_dec_ref_known(v_x_292_, 2);
            v___x_299_ = crate::leanh::lean_apply_3(v_h__2_294_, v_x_291_, v_pre_297_, v_str_298_);
            return v___x_299_;
        }
        _ => {
            let mut v_pre_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_294_);
            crate::leanh::lean_dec(v_h__1_293_);
            v_pre_300_ = crate::leanh::lean_ctor_get(v_x_292_, 0);
            crate::leanh::lean_inc(v_pre_300_);
            v_i_301_ = crate::leanh::lean_ctor_get(v_x_292_, 1);
            crate::leanh::lean_inc(v_i_301_);
            crate::leanh::lean_dec_ref_known(v_x_292_, 2);
            v___x_302_ = crate::leanh::lean_apply_3(v_h__3_295_, v_x_291_, v_pre_300_, v_i_301_);
            return v___x_302_;
        }
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_appendCore_match__1_splitter(
    mut v_motive_303_: *mut crate::leanh::LeanObject,
    mut v_x_304_: *mut crate::leanh::LeanObject,
    mut v_x_305_: *mut crate::leanh::LeanObject,
    mut v_h__1_306_: *mut crate::leanh::LeanObject,
    mut v_h__2_307_: *mut crate::leanh::LeanObject,
    mut v_h__3_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_305_) {
        0 => {
            let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_308_);
            crate::leanh::lean_dec(v_h__2_307_);
            v___x_309_ = crate::leanh::lean_apply_1(v_h__1_306_, v_x_304_);
            return v___x_309_;
        }
        1 => {
            let mut v_pre_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_str_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_308_);
            crate::leanh::lean_dec(v_h__1_306_);
            v_pre_310_ = crate::leanh::lean_ctor_get(v_x_305_, 0);
            crate::leanh::lean_inc(v_pre_310_);
            v_str_311_ = crate::leanh::lean_ctor_get(v_x_305_, 1);
            crate::leanh::lean_inc_ref(v_str_311_);
            crate::leanh::lean_dec_ref_known(v_x_305_, 2);
            v___x_312_ = crate::leanh::lean_apply_3(v_h__2_307_, v_x_304_, v_pre_310_, v_str_311_);
            return v___x_312_;
        }
        _ => {
            let mut v_pre_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_i_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_307_);
            crate::leanh::lean_dec(v_h__1_306_);
            v_pre_313_ = crate::leanh::lean_ctor_get(v_x_305_, 0);
            crate::leanh::lean_inc(v_pre_313_);
            v_i_314_ = crate::leanh::lean_ctor_get(v_x_305_, 1);
            crate::leanh::lean_inc(v_i_314_);
            crate::leanh::lean_dec_ref_known(v_x_305_, 2);
            v___x_315_ = crate::leanh::lean_apply_3(v_h__3_308_, v_x_304_, v_pre_313_, v_i_314_);
            return v___x_315_;
        }
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter___redArg(
    mut v_x_316_: *mut crate::leanh::LeanObject,
    mut v_x_317_: *mut crate::leanh::LeanObject,
    mut v_h__1_318_: *mut crate::leanh::LeanObject,
    mut v_h__2_319_: *mut crate::leanh::LeanObject,
    mut v_h__3_320_: *mut crate::leanh::LeanObject,
    mut v_h__4_321_: *mut crate::leanh::LeanObject,
    mut v_h__5_322_: *mut crate::leanh::LeanObject,
    mut v_h__6_323_: *mut crate::leanh::LeanObject,
    mut v_h__7_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_316_) {
        0 => {
            crate::leanh::lean_dec(v_h__7_324_);
            crate::leanh::lean_dec(v_h__6_323_);
            crate::leanh::lean_dec(v_h__5_322_);
            crate::leanh::lean_dec(v_h__4_321_);
            crate::leanh::lean_dec(v_h__3_320_);
            if crate::leanh::lean_obj_tag(v_x_317_) == 0 {
                let mut v___x_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__2_319_);
                v___x_325_ = crate::leanh::lean_box(0);
                v___x_326_ = crate::leanh::lean_apply_1(v_h__1_318_, v___x_325_);
                return v___x_326_;
            } else {
                let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__1_318_);
                v___x_327_ =
                    crate::leanh::lean_apply_2(v_h__2_319_, v_x_317_, crate::leanh::lean_box(0));
                return v___x_327_;
            }
        }
        1 => {
            crate::leanh::lean_dec(v_h__5_322_);
            crate::leanh::lean_dec(v_h__4_321_);
            crate::leanh::lean_dec(v_h__2_319_);
            crate::leanh::lean_dec(v_h__1_318_);
            match crate::leanh::lean_obj_tag(v_x_317_) {
                0 => {
                    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_324_);
                    crate::leanh::lean_dec(v_h__6_323_);
                    v___x_328_ = crate::leanh::lean_apply_2(
                        v_h__3_320_,
                        v_x_316_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_328_;
                }
                1 => {
                    let mut v_pre_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_str_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_pre_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_str_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_323_);
                    crate::leanh::lean_dec(v_h__3_320_);
                    v_pre_329_ = crate::leanh::lean_ctor_get(v_x_316_, 0);
                    crate::leanh::lean_inc(v_pre_329_);
                    v_str_330_ = crate::leanh::lean_ctor_get(v_x_316_, 1);
                    crate::leanh::lean_inc_ref(v_str_330_);
                    crate::leanh::lean_dec_ref_known(v_x_316_, 2);
                    v_pre_331_ = crate::leanh::lean_ctor_get(v_x_317_, 0);
                    crate::leanh::lean_inc(v_pre_331_);
                    v_str_332_ = crate::leanh::lean_ctor_get(v_x_317_, 1);
                    crate::leanh::lean_inc_ref(v_str_332_);
                    crate::leanh::lean_dec_ref_known(v_x_317_, 2);
                    v___x_333_ = crate::leanh::lean_apply_4(
                        v_h__7_324_,
                        v_pre_329_,
                        v_str_330_,
                        v_pre_331_,
                        v_str_332_,
                    );
                    return v___x_333_;
                }
                _ => {
                    let mut v_pre_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_str_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_pre_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_i_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_324_);
                    crate::leanh::lean_dec(v_h__3_320_);
                    v_pre_334_ = crate::leanh::lean_ctor_get(v_x_316_, 0);
                    crate::leanh::lean_inc(v_pre_334_);
                    v_str_335_ = crate::leanh::lean_ctor_get(v_x_316_, 1);
                    crate::leanh::lean_inc_ref(v_str_335_);
                    crate::leanh::lean_dec_ref_known(v_x_316_, 2);
                    v_pre_336_ = crate::leanh::lean_ctor_get(v_x_317_, 0);
                    crate::leanh::lean_inc(v_pre_336_);
                    v_i_337_ = crate::leanh::lean_ctor_get(v_x_317_, 1);
                    crate::leanh::lean_inc(v_i_337_);
                    crate::leanh::lean_dec_ref_known(v_x_317_, 2);
                    v___x_338_ = crate::leanh::lean_apply_4(
                        v_h__6_323_,
                        v_pre_334_,
                        v_str_335_,
                        v_pre_336_,
                        v_i_337_,
                    );
                    return v___x_338_;
                }
            }
        }
        _ => {
            crate::leanh::lean_dec(v_h__7_324_);
            crate::leanh::lean_dec(v_h__6_323_);
            crate::leanh::lean_dec(v_h__2_319_);
            crate::leanh::lean_dec(v_h__1_318_);
            match crate::leanh::lean_obj_tag(v_x_317_) {
                0 => {
                    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_322_);
                    crate::leanh::lean_dec(v_h__4_321_);
                    v___x_339_ = crate::leanh::lean_apply_2(
                        v_h__3_320_,
                        v_x_316_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_339_;
                }
                1 => {
                    let mut v_pre_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_i_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_pre_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_str_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_321_);
                    crate::leanh::lean_dec(v_h__3_320_);
                    v_pre_340_ = crate::leanh::lean_ctor_get(v_x_316_, 0);
                    crate::leanh::lean_inc(v_pre_340_);
                    v_i_341_ = crate::leanh::lean_ctor_get(v_x_316_, 1);
                    crate::leanh::lean_inc(v_i_341_);
                    crate::leanh::lean_dec_ref_known(v_x_316_, 2);
                    v_pre_342_ = crate::leanh::lean_ctor_get(v_x_317_, 0);
                    crate::leanh::lean_inc(v_pre_342_);
                    v_str_343_ = crate::leanh::lean_ctor_get(v_x_317_, 1);
                    crate::leanh::lean_inc_ref(v_str_343_);
                    crate::leanh::lean_dec_ref_known(v_x_317_, 2);
                    v___x_344_ = crate::leanh::lean_apply_4(
                        v_h__5_322_,
                        v_pre_340_,
                        v_i_341_,
                        v_pre_342_,
                        v_str_343_,
                    );
                    return v___x_344_;
                }
                _ => {
                    let mut v_pre_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_i_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_pre_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_i_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_322_);
                    crate::leanh::lean_dec(v_h__3_320_);
                    v_pre_345_ = crate::leanh::lean_ctor_get(v_x_316_, 0);
                    crate::leanh::lean_inc(v_pre_345_);
                    v_i_346_ = crate::leanh::lean_ctor_get(v_x_316_, 1);
                    crate::leanh::lean_inc(v_i_346_);
                    crate::leanh::lean_dec_ref_known(v_x_316_, 2);
                    v_pre_347_ = crate::leanh::lean_ctor_get(v_x_317_, 0);
                    crate::leanh::lean_inc(v_pre_347_);
                    v_i_348_ = crate::leanh::lean_ctor_get(v_x_317_, 1);
                    crate::leanh::lean_inc(v_i_348_);
                    crate::leanh::lean_dec_ref_known(v_x_317_, 2);
                    v___x_349_ = crate::leanh::lean_apply_4(
                        v_h__4_321_,
                        v_pre_345_,
                        v_i_346_,
                        v_pre_347_,
                        v_i_348_,
                    );
                    return v___x_349_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_cmp_match__4_splitter(
    mut v_motive_350_: *mut crate::leanh::LeanObject,
    mut v_x_351_: *mut crate::leanh::LeanObject,
    mut v_x_352_: *mut crate::leanh::LeanObject,
    mut v_h__1_353_: *mut crate::leanh::LeanObject,
    mut v_h__2_354_: *mut crate::leanh::LeanObject,
    mut v_h__3_355_: *mut crate::leanh::LeanObject,
    mut v_h__4_356_: *mut crate::leanh::LeanObject,
    mut v_h__5_357_: *mut crate::leanh::LeanObject,
    mut v_h__6_358_: *mut crate::leanh::LeanObject,
    mut v_h__7_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_351_) {
        0 => {
            crate::leanh::lean_dec(v_h__7_359_);
            crate::leanh::lean_dec(v_h__6_358_);
            crate::leanh::lean_dec(v_h__5_357_);
            crate::leanh::lean_dec(v_h__4_356_);
            crate::leanh::lean_dec(v_h__3_355_);
            if crate::leanh::lean_obj_tag(v_x_352_) == 0 {
                let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__2_354_);
                v___x_360_ = crate::leanh::lean_box(0);
                v___x_361_ = crate::leanh::lean_apply_1(v_h__1_353_, v___x_360_);
                return v___x_361_;
            } else {
                let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_h__1_353_);
                v___x_362_ =
                    crate::leanh::lean_apply_2(v_h__2_354_, v_x_352_, crate::leanh::lean_box(0));
                return v___x_362_;
            }
        }
        1 => {
            crate::leanh::lean_dec(v_h__5_357_);
            crate::leanh::lean_dec(v_h__4_356_);
            crate::leanh::lean_dec(v_h__2_354_);
            crate::leanh::lean_dec(v_h__1_353_);
            match crate::leanh::lean_obj_tag(v_x_352_) {
                0 => {
                    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_359_);
                    crate::leanh::lean_dec(v_h__6_358_);
                    v___x_363_ = crate::leanh::lean_apply_2(
                        v_h__3_355_,
                        v_x_351_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_363_;
                }
                1 => {
                    let mut v_pre_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_str_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_pre_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_str_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__6_358_);
                    crate::leanh::lean_dec(v_h__3_355_);
                    v_pre_364_ = crate::leanh::lean_ctor_get(v_x_351_, 0);
                    crate::leanh::lean_inc(v_pre_364_);
                    v_str_365_ = crate::leanh::lean_ctor_get(v_x_351_, 1);
                    crate::leanh::lean_inc_ref(v_str_365_);
                    crate::leanh::lean_dec_ref_known(v_x_351_, 2);
                    v_pre_366_ = crate::leanh::lean_ctor_get(v_x_352_, 0);
                    crate::leanh::lean_inc(v_pre_366_);
                    v_str_367_ = crate::leanh::lean_ctor_get(v_x_352_, 1);
                    crate::leanh::lean_inc_ref(v_str_367_);
                    crate::leanh::lean_dec_ref_known(v_x_352_, 2);
                    v___x_368_ = crate::leanh::lean_apply_4(
                        v_h__7_359_,
                        v_pre_364_,
                        v_str_365_,
                        v_pre_366_,
                        v_str_367_,
                    );
                    return v___x_368_;
                }
                _ => {
                    let mut v_pre_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_str_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_pre_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_i_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__7_359_);
                    crate::leanh::lean_dec(v_h__3_355_);
                    v_pre_369_ = crate::leanh::lean_ctor_get(v_x_351_, 0);
                    crate::leanh::lean_inc(v_pre_369_);
                    v_str_370_ = crate::leanh::lean_ctor_get(v_x_351_, 1);
                    crate::leanh::lean_inc_ref(v_str_370_);
                    crate::leanh::lean_dec_ref_known(v_x_351_, 2);
                    v_pre_371_ = crate::leanh::lean_ctor_get(v_x_352_, 0);
                    crate::leanh::lean_inc(v_pre_371_);
                    v_i_372_ = crate::leanh::lean_ctor_get(v_x_352_, 1);
                    crate::leanh::lean_inc(v_i_372_);
                    crate::leanh::lean_dec_ref_known(v_x_352_, 2);
                    v___x_373_ = crate::leanh::lean_apply_4(
                        v_h__6_358_,
                        v_pre_369_,
                        v_str_370_,
                        v_pre_371_,
                        v_i_372_,
                    );
                    return v___x_373_;
                }
            }
        }
        _ => {
            crate::leanh::lean_dec(v_h__7_359_);
            crate::leanh::lean_dec(v_h__6_358_);
            crate::leanh::lean_dec(v_h__2_354_);
            crate::leanh::lean_dec(v_h__1_353_);
            match crate::leanh::lean_obj_tag(v_x_352_) {
                0 => {
                    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_357_);
                    crate::leanh::lean_dec(v_h__4_356_);
                    v___x_374_ = crate::leanh::lean_apply_2(
                        v_h__3_355_,
                        v_x_351_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_374_;
                }
                1 => {
                    let mut v_pre_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_i_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_pre_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_str_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__4_356_);
                    crate::leanh::lean_dec(v_h__3_355_);
                    v_pre_375_ = crate::leanh::lean_ctor_get(v_x_351_, 0);
                    crate::leanh::lean_inc(v_pre_375_);
                    v_i_376_ = crate::leanh::lean_ctor_get(v_x_351_, 1);
                    crate::leanh::lean_inc(v_i_376_);
                    crate::leanh::lean_dec_ref_known(v_x_351_, 2);
                    v_pre_377_ = crate::leanh::lean_ctor_get(v_x_352_, 0);
                    crate::leanh::lean_inc(v_pre_377_);
                    v_str_378_ = crate::leanh::lean_ctor_get(v_x_352_, 1);
                    crate::leanh::lean_inc_ref(v_str_378_);
                    crate::leanh::lean_dec_ref_known(v_x_352_, 2);
                    v___x_379_ = crate::leanh::lean_apply_4(
                        v_h__5_357_,
                        v_pre_375_,
                        v_i_376_,
                        v_pre_377_,
                        v_str_378_,
                    );
                    return v___x_379_;
                }
                _ => {
                    let mut v_pre_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_i_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_pre_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v_i_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_h__5_357_);
                    crate::leanh::lean_dec(v_h__3_355_);
                    v_pre_380_ = crate::leanh::lean_ctor_get(v_x_351_, 0);
                    crate::leanh::lean_inc(v_pre_380_);
                    v_i_381_ = crate::leanh::lean_ctor_get(v_x_351_, 1);
                    crate::leanh::lean_inc(v_i_381_);
                    crate::leanh::lean_dec_ref_known(v_x_351_, 2);
                    v_pre_382_ = crate::leanh::lean_ctor_get(v_x_352_, 0);
                    crate::leanh::lean_inc(v_pre_382_);
                    v_i_383_ = crate::leanh::lean_ctor_get(v_x_352_, 1);
                    crate::leanh::lean_inc(v_i_383_);
                    crate::leanh::lean_dec_ref_known(v_x_352_, 2);
                    v___x_384_ = crate::leanh::lean_apply_4(
                        v_h__4_356_,
                        v_pre_380_,
                        v_i_381_,
                        v_pre_382_,
                        v_i_383_,
                    );
                    return v___x_384_;
                }
            }
        }
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(
    mut v_x_385_: u8,
    mut v_h__1_386_: *mut crate::leanh::LeanObject,
    mut v_h__2_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_385_ == 1 {
        let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_387_);
        v___x_388_ = crate::leanh::lean_box(0);
        v___x_389_ = crate::leanh::lean_apply_1(v_h__1_386_, v___x_388_);
        return v___x_389_;
    } else {
        let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_386_);
        v___x_390_ = crate::leanh::lean_box((v_x_385_) as usize);
        v___x_391_ = crate::leanh::lean_apply_2(v_h__2_387_, v___x_390_, crate::leanh::lean_box(0));
        return v___x_391_;
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg___boxed(
    mut v_x_392_: *mut crate::leanh::LeanObject,
    mut v_h__1_393_: *mut crate::leanh::LeanObject,
    mut v_h__2_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_395_: u8 = 0;
    let mut v_res_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_395_ = (crate::leanh::lean_unbox(v_x_392_) as u8);
    v_res_396_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___redArg(
        v_x_17__boxed_395_,
        v_h__1_393_,
        v_h__2_394_,
    );
    return v_res_396_;
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(
    mut v_motive_397_: *mut crate::leanh::LeanObject,
    mut v_x_398_: u8,
    mut v_h__1_399_: *mut crate::leanh::LeanObject,
    mut v_h__2_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_398_ == 1 {
        let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_400_);
        v___x_401_ = crate::leanh::lean_box(0);
        v___x_402_ = crate::leanh::lean_apply_1(v_h__1_399_, v___x_401_);
        return v___x_402_;
    } else {
        let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_399_);
        v___x_403_ = crate::leanh::lean_box((v_x_398_) as usize);
        v___x_404_ = crate::leanh::lean_apply_2(v_h__2_400_, v___x_403_, crate::leanh::lean_box(0));
        return v___x_404_;
    }
}
pub unsafe fn l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter___boxed(
    mut v_motive_405_: *mut crate::leanh::LeanObject,
    mut v_x_406_: *mut crate::leanh::LeanObject,
    mut v_h__1_407_: *mut crate::leanh::LeanObject,
    mut v_h__2_408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_28__boxed_409_: u8 = 0;
    let mut v_res_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_28__boxed_409_ = (crate::leanh::lean_unbox(v_x_406_) as u8);
    v_res_410_ = l___private_Lake_Util_Name_0__Lean_Name_cmp_match__1_splitter(
        v_motive_405_,
        v_x_28__boxed_409_,
        v_h__1_407_,
        v_h__2_408_,
    );
    return v_res_410_;
}
pub unsafe fn l_Lake_Name_quoteFrom(
    mut v_ref_422_: *mut crate::leanh::LeanObject,
    mut v_n_423_: *mut crate::leanh::LeanObject,
    mut v_canonical_424_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_425_ = l_Lean_SourceInfo_fromRef(v_ref_422_, v_canonical_424_);
    v_ref_426_ = l_Lean_Syntax_setHeadInfo(v_ref_422_, v___x_425_);
    v___x_427_ = crate::leanh::lean_box(0);
    crate::leanh::lean_inc(v_n_423_);
    v___x_428_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_427_, v_n_423_);
    if crate::leanh::lean_obj_tag(v___x_428_) == 0 {
        let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_stx_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_429_ = l_Lean_quoteNameMk(v_n_423_);
        v_stx_430_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_429_, v_ref_426_);
        crate::leanh::lean_dec(v_ref_426_);
        return v_stx_430_;
    } else {
        let mut v_val_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_stx_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_n_423_);
        v_val_431_ = crate::leanh::lean_ctor_get(v___x_428_, 0);
        crate::leanh::lean_inc(v_val_431_);
        crate::leanh::lean_dec_ref_known(v___x_428_, 1);
        v___x_432_ = l_Lake_Name_quoteFrom___closed__4;
        v___x_433_ = l_Lake_Name_quoteFrom___closed__5;
        v___x_434_ = l_Lake_Name_quoteFrom___closed__6;
        v___x_435_ = lean_string_intercalate(v___x_434_, v_val_431_);
        v___x_436_ = lean_string_append(v___x_433_, v___x_435_);
        crate::leanh::lean_dec_ref(v___x_435_);
        v___x_437_ = crate::leanh::lean_box(2);
        v___x_438_ = l_Lean_Syntax_mkNameLit(v___x_436_, v___x_437_);
        v___x_439_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_440_ = lean_mk_empty_array_with_capacity(v___x_439_);
        v___x_441_ = lean_array_push(v___x_440_, v___x_438_);
        v___x_442_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_442_, 0, v___x_437_);
        crate::leanh::lean_ctor_set(v___x_442_, 1, v___x_432_);
        crate::leanh::lean_ctor_set(v___x_442_, 2, v___x_441_);
        v_stx_443_ = l_Lean_Syntax_copyHeadTailInfoFrom(v___x_442_, v_ref_426_);
        crate::leanh::lean_dec(v_ref_426_);
        return v_stx_443_;
    }
}
pub unsafe fn l_Lake_Name_quoteFrom___boxed(
    mut v_ref_444_: *mut crate::leanh::LeanObject,
    mut v_n_445_: *mut crate::leanh::LeanObject,
    mut v_canonical_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonical_boxed_447_: u8 = 0;
    let mut v_res_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonical_boxed_447_ = (crate::leanh::lean_unbox(v_canonical_446_) as u8);
    v_res_448_ = l_Lake_Name_quoteFrom(v_ref_444_, v_n_445_, v_canonical_boxed_447_);
    return v_res_448_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Name(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lake_Util_RBArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Name(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Name(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lake_Util_RBArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Ord_UInt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Prelude(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Name(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Name(builtin);
}
