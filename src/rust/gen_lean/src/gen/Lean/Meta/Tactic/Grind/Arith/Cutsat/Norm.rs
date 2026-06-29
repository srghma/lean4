// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.IntInstTesters
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp,
    l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::IntInstTesters::{
    initialize_Lean_Meta_IntInstTesters, l_Lean_Meta_Structural_isInstHAddInt___redArg,
    l_Lean_Meta_Structural_isInstHMulInt___redArg, l_Lean_Meta_Structural_isInstHSubInt___redArg,
    l_Lean_Meta_Structural_isInstNegInt___redArg, runtime_initialize_Lean_Meta_IntInstTesters,
};
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getIntValue_x3f;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_alreadyInternalized___redArg;
use crate::ffi::lean_grind_cutsat_mk_var;
use crate::ffi::lean_grind_internalize;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value:
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
    m_data: [78, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value:
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
    m_data: [110, 101, 103, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9626815015619986526 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__1_value)
            as *mut crate::leanh::LeanObject,
        17185717442815859305 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [79, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [111, 102, 78, 97, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__3_value)
            as *mut crate::leanh::LeanObject,
        17636616155771105671 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__4_value)
            as *mut crate::leanh::LeanObject,
        15578568367168711682 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value:
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
    m_data: [72, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value:
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
    m_data: [104, 77, 117, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__6_value)
            as *mut crate::leanh::LeanObject,
        2929883540436775422 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__7_value)
            as *mut crate::leanh::LeanObject,
        1611444129324655608 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value:
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
    m_data: [72, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value:
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
    m_data: [104, 83, 117, 98, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__9_value)
            as *mut crate::leanh::LeanObject,
        16856108565602861689 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__10_value)
            as *mut crate::leanh::LeanObject,
        4187025665268973031 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value:
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
    m_data: [72, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value:
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
    m_data: [104, 65, 100, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__12_value)
            as *mut crate::leanh::LeanObject,
        10393083817453678557 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__13_value)
            as *mut crate::leanh::LeanObject,
        10680564408669940870 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
    mut v_e_343_: *mut crate::leanh::LeanObject,
    mut v_generation_344_: *mut crate::leanh::LeanObject,
    mut v_a_345_: *mut crate::leanh::LeanObject,
    mut v_a_346_: *mut crate::leanh::LeanObject,
    mut v_a_347_: *mut crate::leanh::LeanObject,
    mut v_a_348_: *mut crate::leanh::LeanObject,
    mut v_a_349_: *mut crate::leanh::LeanObject,
    mut v_a_350_: *mut crate::leanh::LeanObject,
    mut v_a_351_: *mut crate::leanh::LeanObject,
    mut v_a_352_: *mut crate::leanh::LeanObject,
    mut v_a_353_: *mut crate::leanh::LeanObject,
    mut v_a_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_e_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: u8 = 0;
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_379_: u8 = 0;
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_384_: u8 = 0;
    let mut v_a_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_388_: u8 = 0;
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_392_: u8 = 0;
    let mut v_a_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_396_: u8 = 0;
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_400_: u8 = 0;
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_405_: u8 = 0;
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_410_: u8 = 0;
    let mut v_a_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_414_: u8 = 0;
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_418_: u8 = 0;
    let mut v_a_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_422_: u8 = 0;
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_426_: u8 = 0;
    let mut v_a_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_430_: u8 = 0;
    let mut v___x_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_434_: u8 = 0;
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: u8 = 0;
    let mut v_arg_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: u8 = 0;
    let mut v_arg_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: u8 = 0;
    let mut v_arg_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: u8 = 0;
    let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: u8 = 0;
    let mut v___x_451_: u8 = 0;
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_453_: u8 = 0;
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: u8 = 0;
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u8 = 0;
    let mut v___x_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: u8 = 0;
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: u8 = 0;
    let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_465_: u8 = 0;
    let mut v___x_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_473_: u8 = 0;
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_478_: u8 = 0;
    let mut v_a_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_482_: u8 = 0;
    let mut v___x_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_486_: u8 = 0;
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: u8 = 0;
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_497_: u8 = 0;
    let mut v___x_498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_502_: u8 = 0;
    let mut v_a_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_506_: u8 = 0;
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_510_: u8 = 0;
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: u8 = 0;
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_524_: u8 = 0;
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_529_: u8 = 0;
    let mut v_a_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_533_: u8 = 0;
    let mut v___x_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_537_: u8 = 0;
    let mut v_val_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_544_: u8 = 0;
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_549_: u8 = 0;
    let mut v_a_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_553_: u8 = 0;
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_a_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_561_: u8 = 0;
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_565_: u8 = 0;
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_570_: u8 = 0;
    let mut v_val_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_574_: u8 = 0;
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_581_: u8 = 0;
    let mut v_isSharedCheck_582_: u8 = 0;
    let mut v_a_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_586_: u8 = 0;
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v___x_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: u8 = 0;
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_599_: u8 = 0;
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_604_: u8 = 0;
    let mut v_a_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_608_: u8 = 0;
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_612_: u8 = 0;
    let mut v_a_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_616_: u8 = 0;
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_343_);
                v___x_435_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_343_, v_a_352_);
                if crate::leanh::lean_obj_tag(v___x_435_) == 0 {
                    v_a_436_ = crate::leanh::lean_ctor_get(v___x_435_, 0);
                    crate::leanh::lean_inc(v_a_436_);
                    crate::leanh::lean_dec_ref_known(v___x_435_, 1);
                    v___x_437_ = l_Lean_Expr_cleanupAnnotations(v_a_436_);
                    v___x_438_ = l_Lean_Expr_isApp(v___x_437_);
                    if v___x_438_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_437_);
                        v_e_357_ = v_e_343_;
                        v___y_358_ = v_a_345_;
                        v___y_359_ = v_a_346_;
                        v___y_360_ = v_a_347_;
                        v___y_361_ = v_a_348_;
                        v___y_362_ = v_a_349_;
                        v___y_363_ = v_a_350_;
                        v___y_364_ = v_a_351_;
                        v___y_365_ = v_a_352_;
                        v___y_366_ = v_a_353_;
                        v___y_367_ = v_a_354_;
                        state = 1;
                        continue;
                    } else {
                        v_arg_439_ = crate::leanh::lean_ctor_get(v___x_437_, 1);
                        crate::leanh::lean_inc_ref(v_arg_439_);
                        v___x_440_ = l_Lean_Expr_appFnCleanup___redArg(v___x_437_);
                        v___x_441_ = l_Lean_Expr_isApp(v___x_440_);
                        if v___x_441_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_440_);
                            crate::leanh::lean_dec_ref(v_arg_439_);
                            v_e_357_ = v_e_343_;
                            v___y_358_ = v_a_345_;
                            v___y_359_ = v_a_346_;
                            v___y_360_ = v_a_347_;
                            v___y_361_ = v_a_348_;
                            v___y_362_ = v_a_349_;
                            v___y_363_ = v_a_350_;
                            v___y_364_ = v_a_351_;
                            v___y_365_ = v_a_352_;
                            v___y_366_ = v_a_353_;
                            v___y_367_ = v_a_354_;
                            state = 1;
                            continue;
                        } else {
                            v_arg_442_ = crate::leanh::lean_ctor_get(v___x_440_, 1);
                            crate::leanh::lean_inc_ref(v_arg_442_);
                            v___x_443_ = l_Lean_Expr_appFnCleanup___redArg(v___x_440_);
                            v___x_444_ = l_Lean_Expr_isApp(v___x_443_);
                            if v___x_444_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_443_);
                                crate::leanh::lean_dec_ref(v_arg_442_);
                                crate::leanh::lean_dec_ref(v_arg_439_);
                                v_e_357_ = v_e_343_;
                                v___y_358_ = v_a_345_;
                                v___y_359_ = v_a_346_;
                                v___y_360_ = v_a_347_;
                                v___y_361_ = v_a_348_;
                                v___y_362_ = v_a_349_;
                                v___y_363_ = v_a_350_;
                                v___y_364_ = v_a_351_;
                                v___y_365_ = v_a_352_;
                                v___y_366_ = v_a_353_;
                                v___y_367_ = v_a_354_;
                                state = 1;
                                continue;
                            } else {
                                v_arg_445_ = crate::leanh::lean_ctor_get(v___x_443_, 1);
                                crate::leanh::lean_inc_ref(v_arg_445_);
                                v___x_446_ = l_Lean_Expr_appFnCleanup___redArg(v___x_443_);
                                v___x_447_ =
                                    l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__2;
                                v___x_448_ = l_Lean_Expr_isConstOf(v___x_446_, v___x_447_);
                                if v___x_448_ == 0 {
                                    v___x_449_ =
                                        l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__5;
                                    v___x_450_ = l_Lean_Expr_isConstOf(v___x_446_, v___x_449_);
                                    if v___x_450_ == 0 {
                                        v___x_451_ = l_Lean_Expr_isApp(v___x_446_);
                                        if v___x_451_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_446_);
                                            crate::leanh::lean_dec_ref(v_arg_445_);
                                            crate::leanh::lean_dec_ref(v_arg_442_);
                                            crate::leanh::lean_dec_ref(v_arg_439_);
                                            v_e_357_ = v_e_343_;
                                            v___y_358_ = v_a_345_;
                                            v___y_359_ = v_a_346_;
                                            v___y_360_ = v_a_347_;
                                            v___y_361_ = v_a_348_;
                                            v___y_362_ = v_a_349_;
                                            v___y_363_ = v_a_350_;
                                            v___y_364_ = v_a_351_;
                                            v___y_365_ = v_a_352_;
                                            v___y_366_ = v_a_353_;
                                            v___y_367_ = v_a_354_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_452_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_446_);
                                            v___x_453_ = l_Lean_Expr_isApp(v___x_452_);
                                            if v___x_453_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_452_);
                                                crate::leanh::lean_dec_ref(v_arg_445_);
                                                crate::leanh::lean_dec_ref(v_arg_442_);
                                                crate::leanh::lean_dec_ref(v_arg_439_);
                                                v_e_357_ = v_e_343_;
                                                v___y_358_ = v_a_345_;
                                                v___y_359_ = v_a_346_;
                                                v___y_360_ = v_a_347_;
                                                v___y_361_ = v_a_348_;
                                                v___y_362_ = v_a_349_;
                                                v___y_363_ = v_a_350_;
                                                v___y_364_ = v_a_351_;
                                                v___y_365_ = v_a_352_;
                                                v___y_366_ = v_a_353_;
                                                v___y_367_ = v_a_354_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_454_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_452_);
                                                v___x_455_ = l_Lean_Expr_isApp(v___x_454_);
                                                if v___x_455_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_454_);
                                                    crate::leanh::lean_dec_ref(v_arg_445_);
                                                    crate::leanh::lean_dec_ref(v_arg_442_);
                                                    crate::leanh::lean_dec_ref(v_arg_439_);
                                                    v_e_357_ = v_e_343_;
                                                    v___y_358_ = v_a_345_;
                                                    v___y_359_ = v_a_346_;
                                                    v___y_360_ = v_a_347_;
                                                    v___y_361_ = v_a_348_;
                                                    v___y_362_ = v_a_349_;
                                                    v___y_363_ = v_a_350_;
                                                    v___y_364_ = v_a_351_;
                                                    v___y_365_ = v_a_352_;
                                                    v___y_366_ = v_a_353_;
                                                    v___y_367_ = v_a_354_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_456_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_454_,
                                                    );
                                                    v___x_457_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__8;
                                                    v___x_458_ = l_Lean_Expr_isConstOf(
                                                        v___x_456_, v___x_457_,
                                                    );
                                                    if v___x_458_ == 0 {
                                                        v___x_459_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__11;
                                                        v___x_460_ = l_Lean_Expr_isConstOf(
                                                            v___x_456_, v___x_459_,
                                                        );
                                                        if v___x_460_ == 0 {
                                                            v___x_461_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___closed__14;
                                                            v___x_462_ = l_Lean_Expr_isConstOf(
                                                                v___x_456_, v___x_461_,
                                                            );
                                                            crate::leanh::lean_dec_ref(v___x_456_);
                                                            if v___x_462_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_445_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_442_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_439_,
                                                                );
                                                                v_e_357_ = v_e_343_;
                                                                v___y_358_ = v_a_345_;
                                                                v___y_359_ = v_a_346_;
                                                                v___y_360_ = v_a_347_;
                                                                v___y_361_ = v_a_348_;
                                                                v___y_362_ = v_a_349_;
                                                                v___y_363_ = v_a_350_;
                                                                v___y_364_ = v_a_351_;
                                                                v___y_365_ = v_a_352_;
                                                                v___y_366_ = v_a_353_;
                                                                v___y_367_ = v_a_354_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_463_ = l_Lean_Meta_Structural_isInstHAddInt___redArg(v_arg_445_, v_a_352_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_463_,
                                                                ) == 0
                                                                {
                                                                    v_a_464_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_463_, 0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_464_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_463_, 1);
                                                                    v___x_465_ =
                                                                        (crate::leanh::lean_unbox(
                                                                            v_a_464_,
                                                                        )
                                                                            as u8);
                                                                    crate::leanh::lean_dec(
                                                                        v_a_464_,
                                                                    );
                                                                    if v___x_465_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_442_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_439_,
                                                                        );
                                                                        v_e_357_ = v_e_343_;
                                                                        v___y_358_ = v_a_345_;
                                                                        v___y_359_ = v_a_346_;
                                                                        v___y_360_ = v_a_347_;
                                                                        v___y_361_ = v_a_348_;
                                                                        v___y_362_ = v_a_349_;
                                                                        v___y_363_ = v_a_350_;
                                                                        v___y_364_ = v_a_351_;
                                                                        v___y_365_ = v_a_352_;
                                                                        v___y_366_ = v_a_353_;
                                                                        v___y_367_ = v_a_354_;
                                                                        state = 1;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_dec(
                                                                            v_generation_344_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_343_,
                                                                        );
                                                                        v___x_466_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                        v___x_467_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_442_, v___x_466_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
                                                                        if crate::leanh::lean_obj_tag(v___x_467_) == 0 {
v_a_468_ = crate::leanh::lean_ctor_get(v___x_467_, 0);
crate::leanh::lean_inc(v_a_468_);
crate::leanh::lean_dec_ref_known(v___x_467_, 1);
v___x_469_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_439_, v___x_466_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if crate::leanh::lean_obj_tag(v___x_469_) == 0 {
v_a_470_ = crate::leanh::lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_478_ = (!crate::leanh::lean_is_exclusive(v___x_469_)) as u8;
if v_isSharedCheck_478_ == 0 {
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_478_;
state = 16; continue;
} else {
crate::leanh::lean_inc(v_a_470_);
crate::leanh::lean_dec(v___x_469_);
v___x_472_ = crate::leanh::lean_box(0);
v_isShared_473_ = v_isSharedCheck_478_;
state = 16; continue;
}
} else {
crate::leanh::lean_dec(v_a_468_);
return v___x_469_;
}
} else {
crate::leanh::lean_dec_ref(v_arg_439_);
return v___x_467_;
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_442_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_439_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_generation_344_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_343_,
                                                                    );
                                                                    v_a_479_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_463_, 0,
                                                                        );
                                                                    v_isSharedCheck_486_ = (!crate::leanh::lean_is_exclusive(v___x_463_)) as u8;
                                                                    if v_isSharedCheck_486_ == 0 {
                                                                        v___x_481_ = v___x_463_;
                                                                        v_isShared_482_ =
                                                                            v_isSharedCheck_486_;
                                                                        state = 18;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_479_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_463_,
                                                                        );
                                                                        v___x_481_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_482_ =
                                                                            v_isSharedCheck_486_;
                                                                        state = 18;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_456_);
                                                            v___x_487_ = l_Lean_Meta_Structural_isInstHSubInt___redArg(v_arg_445_, v_a_352_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_487_,
                                                            ) == 0
                                                            {
                                                                v_a_488_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_487_, 0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_488_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_487_, 1,
                                                                );
                                                                v___x_489_ =
                                                                    (crate::leanh::lean_unbox(
                                                                        v_a_488_,
                                                                    )
                                                                        as u8);
                                                                crate::leanh::lean_dec(v_a_488_);
                                                                if v___x_489_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_442_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_439_,
                                                                    );
                                                                    v_e_357_ = v_e_343_;
                                                                    v___y_358_ = v_a_345_;
                                                                    v___y_359_ = v_a_346_;
                                                                    v___y_360_ = v_a_347_;
                                                                    v___y_361_ = v_a_348_;
                                                                    v___y_362_ = v_a_349_;
                                                                    v___y_363_ = v_a_350_;
                                                                    v___y_364_ = v_a_351_;
                                                                    v___y_365_ = v_a_352_;
                                                                    v___y_366_ = v_a_353_;
                                                                    v___y_367_ = v_a_354_;
                                                                    state = 1;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_generation_344_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_343_,
                                                                    );
                                                                    v___x_490_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                    v___x_491_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_442_, v___x_490_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_491_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_492_ = crate::leanh::lean_ctor_get(v___x_491_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_492_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v___x_491_, 1);
                                                                        v___x_493_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_439_, v___x_490_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
                                                                        if crate::leanh::lean_obj_tag(v___x_493_) == 0 {
v_a_494_ = crate::leanh::lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_502_ = (!crate::leanh::lean_is_exclusive(v___x_493_)) as u8;
if v_isSharedCheck_502_ == 0 {
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_502_;
state = 20; continue;
} else {
crate::leanh::lean_inc(v_a_494_);
crate::leanh::lean_dec(v___x_493_);
v___x_496_ = crate::leanh::lean_box(0);
v_isShared_497_ = v_isSharedCheck_502_;
state = 20; continue;
}
} else {
crate::leanh::lean_dec(v_a_492_);
return v___x_493_;
}
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_439_,
                                                                        );
                                                                        return v___x_491_;
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_442_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_439_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_generation_344_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_343_,
                                                                );
                                                                v_a_503_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_487_, 0,
                                                                    );
                                                                v_isSharedCheck_510_ = (!crate::leanh::lean_is_exclusive(v___x_487_)) as u8;
                                                                if v_isSharedCheck_510_ == 0 {
                                                                    v___x_505_ = v___x_487_;
                                                                    v_isShared_506_ =
                                                                        v_isSharedCheck_510_;
                                                                    state = 22;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_503_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_487_,
                                                                    );
                                                                    v___x_505_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_506_ =
                                                                        v_isSharedCheck_510_;
                                                                    state = 22;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_456_);
                                                        v___x_511_ = l_Lean_Meta_Structural_isInstHMulInt___redArg(v_arg_445_, v_a_352_);
                                                        if crate::leanh::lean_obj_tag(v___x_511_)
                                                            == 0
                                                        {
                                                            v_a_512_ = crate::leanh::lean_ctor_get(
                                                                v___x_511_, 0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_512_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_511_, 1,
                                                            );
                                                            v___x_513_ =
                                                                (crate::leanh::lean_unbox(v_a_512_)
                                                                    as u8);
                                                            crate::leanh::lean_dec(v_a_512_);
                                                            if v___x_513_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_442_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_439_,
                                                                );
                                                                v_e_357_ = v_e_343_;
                                                                v___y_358_ = v_a_345_;
                                                                v___y_359_ = v_a_346_;
                                                                v___y_360_ = v_a_347_;
                                                                v___y_361_ = v_a_348_;
                                                                v___y_362_ = v_a_349_;
                                                                v___y_363_ = v_a_350_;
                                                                v___y_364_ = v_a_351_;
                                                                v___y_365_ = v_a_352_;
                                                                v___y_366_ = v_a_353_;
                                                                v___y_367_ = v_a_354_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc_ref(
                                                                    v_arg_442_,
                                                                );
                                                                v___x_514_ =
                                                                    l_Lean_Meta_getIntValue_x3f(
                                                                        v_arg_442_, v_a_351_,
                                                                        v_a_352_, v_a_353_,
                                                                        v_a_354_,
                                                                    );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_514_,
                                                                ) == 0
                                                                {
                                                                    v_a_515_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_514_, 0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_515_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_514_, 1);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v_a_515_,
                                                                    ) == 0
                                                                    {
                                                                        v___x_516_ = l_Lean_Meta_getIntValue_x3f(v_arg_439_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
                                                                        if crate::leanh::lean_obj_tag(v___x_516_) == 0 {
v_a_517_ = crate::leanh::lean_ctor_get(v___x_516_, 0);
crate::leanh::lean_inc(v_a_517_);
crate::leanh::lean_dec_ref_known(v___x_516_, 1);
if crate::leanh::lean_obj_tag(v_a_517_) == 0 {
crate::leanh::lean_dec_ref(v_arg_442_);
v_e_357_ = v_e_343_;
v___y_358_ = v_a_345_;
v___y_359_ = v_a_346_;
v___y_360_ = v_a_347_;
v___y_361_ = v_a_348_;
v___y_362_ = v_a_349_;
v___y_363_ = v_a_350_;
v___y_364_ = v_a_351_;
v___y_365_ = v_a_352_;
v___y_366_ = v_a_353_;
v___y_367_ = v_a_354_;
state = 1; continue;
} else {
crate::leanh::lean_dec(v_generation_344_);
crate::leanh::lean_dec_ref(v_e_343_);
v_val_518_ = crate::leanh::lean_ctor_get(v_a_517_, 0);
crate::leanh::lean_inc(v_val_518_);
crate::leanh::lean_dec_ref_known(v_a_517_, 1);
v___x_519_ = crate::leanh::lean_unsigned_to_nat(0);
v___x_520_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_442_, v___x_519_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
if crate::leanh::lean_obj_tag(v___x_520_) == 0 {
v_a_521_ = crate::leanh::lean_ctor_get(v___x_520_, 0);
v_isSharedCheck_529_ = (!crate::leanh::lean_is_exclusive(v___x_520_)) as u8;
if v_isSharedCheck_529_ == 0 {
v___x_523_ = v___x_520_;
v_isShared_524_ = v_isSharedCheck_529_;
state = 24; continue;
} else {
crate::leanh::lean_inc(v_a_521_);
crate::leanh::lean_dec(v___x_520_);
v___x_523_ = crate::leanh::lean_box(0);
v_isShared_524_ = v_isSharedCheck_529_;
state = 24; continue;
}
} else {
crate::leanh::lean_dec(v_val_518_);
return v___x_520_;
}
}
} else {
crate::leanh::lean_dec_ref(v_arg_442_);
crate::leanh::lean_dec(v_generation_344_);
crate::leanh::lean_dec_ref(v_e_343_);
v_a_530_ = crate::leanh::lean_ctor_get(v___x_516_, 0);
v_isSharedCheck_537_ = (!crate::leanh::lean_is_exclusive(v___x_516_)) as u8;
if v_isSharedCheck_537_ == 0 {
v___x_532_ = v___x_516_;
v_isShared_533_ = v_isSharedCheck_537_;
state = 26; continue;
} else {
crate::leanh::lean_inc(v_a_530_);
crate::leanh::lean_dec(v___x_516_);
v___x_532_ = crate::leanh::lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
state = 26; continue;
}
}
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_442_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v_generation_344_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_e_343_,
                                                                        );
                                                                        v_val_538_ = crate::leanh::lean_ctor_get(v_a_515_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_val_538_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_a_515_, 1);
                                                                        v___x_539_ = crate::leanh::lean_unsigned_to_nat(0);
                                                                        v___x_540_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_439_, v___x_539_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v_a_352_, v_a_353_, v_a_354_);
                                                                        if crate::leanh::lean_obj_tag(v___x_540_) == 0 {
v_a_541_ = crate::leanh::lean_ctor_get(v___x_540_, 0);
v_isSharedCheck_549_ = (!crate::leanh::lean_is_exclusive(v___x_540_)) as u8;
if v_isSharedCheck_549_ == 0 {
v___x_543_ = v___x_540_;
v_isShared_544_ = v_isSharedCheck_549_;
state = 28; continue;
} else {
crate::leanh::lean_inc(v_a_541_);
crate::leanh::lean_dec(v___x_540_);
v___x_543_ = crate::leanh::lean_box(0);
v_isShared_544_ = v_isSharedCheck_549_;
state = 28; continue;
}
} else {
crate::leanh::lean_dec(v_val_538_);
return v___x_540_;
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_442_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_439_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_generation_344_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_e_343_,
                                                                    );
                                                                    v_a_550_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_514_, 0,
                                                                        );
                                                                    v_isSharedCheck_557_ = (!crate::leanh::lean_is_exclusive(v___x_514_)) as u8;
                                                                    if v_isSharedCheck_557_ == 0 {
                                                                        v___x_552_ = v___x_514_;
                                                                        v_isShared_553_ =
                                                                            v_isSharedCheck_557_;
                                                                        state = 30;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_550_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_514_,
                                                                        );
                                                                        v___x_552_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_553_ =
                                                                            v_isSharedCheck_557_;
                                                                        state = 30;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_442_);
                                                            crate::leanh::lean_dec_ref(v_arg_439_);
                                                            crate::leanh::lean_dec(
                                                                v_generation_344_,
                                                            );
                                                            crate::leanh::lean_dec_ref(v_e_343_);
                                                            v_a_558_ = crate::leanh::lean_ctor_get(
                                                                v___x_511_, 0,
                                                            );
                                                            v_isSharedCheck_565_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_511_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_565_ == 0 {
                                                                v___x_560_ = v___x_511_;
                                                                v_isShared_561_ =
                                                                    v_isSharedCheck_565_;
                                                                state = 32;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_558_);
                                                                crate::leanh::lean_dec(v___x_511_);
                                                                v___x_560_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_561_ =
                                                                    v_isSharedCheck_565_;
                                                                state = 32;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_446_);
                                        crate::leanh::lean_dec_ref(v_arg_445_);
                                        crate::leanh::lean_dec_ref(v_arg_442_);
                                        crate::leanh::lean_dec_ref(v_arg_439_);
                                        crate::leanh::lean_inc_ref(v_e_343_);
                                        v___x_566_ = l_Lean_Meta_getIntValue_x3f(
                                            v_e_343_, v_a_351_, v_a_352_, v_a_353_, v_a_354_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_566_) == 0 {
                                            v_a_567_ = crate::leanh::lean_ctor_get(v___x_566_, 0);
                                            v_isSharedCheck_582_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_566_))
                                                    as u8;
                                            if v_isSharedCheck_582_ == 0 {
                                                v___x_569_ = v___x_566_;
                                                v_isShared_570_ = v_isSharedCheck_582_;
                                                state = 34;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_567_);
                                                crate::leanh::lean_dec(v___x_566_);
                                                v___x_569_ = crate::leanh::lean_box(0);
                                                v_isShared_570_ = v_isSharedCheck_582_;
                                                state = 34;
                                                continue;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_generation_344_);
                                            crate::leanh::lean_dec_ref(v_e_343_);
                                            v_a_583_ = crate::leanh::lean_ctor_get(v___x_566_, 0);
                                            v_isSharedCheck_590_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_566_))
                                                    as u8;
                                            if v_isSharedCheck_590_ == 0 {
                                                v___x_585_ = v___x_566_;
                                                v_isShared_586_ = v_isSharedCheck_590_;
                                                state = 38;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_583_);
                                                crate::leanh::lean_dec(v___x_566_);
                                                v___x_585_ = crate::leanh::lean_box(0);
                                                v_isShared_586_ = v_isSharedCheck_590_;
                                                state = 38;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_446_);
                                    crate::leanh::lean_dec_ref(v_arg_445_);
                                    v___x_591_ = l_Lean_Meta_Structural_isInstNegInt___redArg(
                                        v_arg_442_, v_a_352_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_591_) == 0 {
                                        v_a_592_ = crate::leanh::lean_ctor_get(v___x_591_, 0);
                                        crate::leanh::lean_inc(v_a_592_);
                                        crate::leanh::lean_dec_ref_known(v___x_591_, 1);
                                        v___x_593_ = (crate::leanh::lean_unbox(v_a_592_) as u8);
                                        crate::leanh::lean_dec(v_a_592_);
                                        if v___x_593_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_439_);
                                            v_e_357_ = v_e_343_;
                                            v___y_358_ = v_a_345_;
                                            v___y_359_ = v_a_346_;
                                            v___y_360_ = v_a_347_;
                                            v___y_361_ = v_a_348_;
                                            v___y_362_ = v_a_349_;
                                            v___y_363_ = v_a_350_;
                                            v___y_364_ = v_a_351_;
                                            v___y_365_ = v_a_352_;
                                            v___y_366_ = v_a_353_;
                                            v___y_367_ = v_a_354_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_generation_344_);
                                            crate::leanh::lean_dec_ref(v_e_343_);
                                            v___x_594_ = crate::leanh::lean_unsigned_to_nat(0);
                                            v___x_595_ =
                                                l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
                                                    v_arg_439_, v___x_594_, v_a_345_, v_a_346_,
                                                    v_a_347_, v_a_348_, v_a_349_, v_a_350_,
                                                    v_a_351_, v_a_352_, v_a_353_, v_a_354_,
                                                );
                                            if crate::leanh::lean_obj_tag(v___x_595_) == 0 {
                                                v_a_596_ =
                                                    crate::leanh::lean_ctor_get(v___x_595_, 0);
                                                v_isSharedCheck_604_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_595_))
                                                        as u8;
                                                if v_isSharedCheck_604_ == 0 {
                                                    v___x_598_ = v___x_595_;
                                                    v_isShared_599_ = v_isSharedCheck_604_;
                                                    state = 40;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_596_);
                                                    crate::leanh::lean_dec(v___x_595_);
                                                    v___x_598_ = crate::leanh::lean_box(0);
                                                    v_isShared_599_ = v_isSharedCheck_604_;
                                                    state = 40;
                                                    continue;
                                                }
                                            } else {
                                                return v___x_595_;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_arg_439_);
                                        crate::leanh::lean_dec(v_generation_344_);
                                        crate::leanh::lean_dec_ref(v_e_343_);
                                        v_a_605_ = crate::leanh::lean_ctor_get(v___x_591_, 0);
                                        v_isSharedCheck_612_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_591_)) as u8;
                                        if v_isSharedCheck_612_ == 0 {
                                            v___x_607_ = v___x_591_;
                                            v_isShared_608_ = v_isSharedCheck_612_;
                                            state = 42;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_605_);
                                            crate::leanh::lean_dec(v___x_591_);
                                            v___x_607_ = crate::leanh::lean_box(0);
                                            v_isShared_608_ = v_isSharedCheck_612_;
                                            state = 42;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_generation_344_);
                    crate::leanh::lean_dec_ref(v_e_343_);
                    v_a_613_ = crate::leanh::lean_ctor_get(v___x_435_, 0);
                    v_isSharedCheck_620_ = (!crate::leanh::lean_is_exclusive(v___x_435_)) as u8;
                    if v_isSharedCheck_620_ == 0 {
                        v___x_615_ = v___x_435_;
                        v_isShared_616_ = v_isSharedCheck_620_;
                        state = 44;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_613_);
                        crate::leanh::lean_dec(v___x_435_);
                        v___x_615_ = crate::leanh::lean_box(0);
                        v_isShared_616_ = v_isSharedCheck_620_;
                        state = 44;
                        continue;
                    }
                }
            }
            1 => {
                v___x_368_ = l_Lean_Meta_Sym_shareCommon___redArg(v_e_357_, v___y_363_);
                if crate::leanh::lean_obj_tag(v___x_368_) == 0 {
                    v_a_369_ = crate::leanh::lean_ctor_get(v___x_368_, 0);
                    crate::leanh::lean_inc(v_a_369_);
                    crate::leanh::lean_dec_ref_known(v___x_368_, 1);
                    v___x_370_ =
                        l_Lean_Meta_Grind_alreadyInternalized___redArg(v_a_369_, v___y_358_);
                    if crate::leanh::lean_obj_tag(v___x_370_) == 0 {
                        v_a_371_ = crate::leanh::lean_ctor_get(v___x_370_, 0);
                        crate::leanh::lean_inc(v_a_371_);
                        crate::leanh::lean_dec_ref_known(v___x_370_, 1);
                        v___x_372_ = (crate::leanh::lean_unbox(v_a_371_) as u8);
                        crate::leanh::lean_dec(v_a_371_);
                        if v___x_372_ == 0 {
                            v___x_373_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_367_);
                            crate::leanh::lean_inc_ref(v___y_366_);
                            crate::leanh::lean_inc(v___y_365_);
                            crate::leanh::lean_inc_ref(v___y_364_);
                            crate::leanh::lean_inc(v___y_363_);
                            crate::leanh::lean_inc_ref(v___y_362_);
                            crate::leanh::lean_inc(v___y_361_);
                            crate::leanh::lean_inc_ref(v___y_360_);
                            crate::leanh::lean_inc(v___y_359_);
                            crate::leanh::lean_inc(v___y_358_);
                            crate::leanh::lean_inc(v_a_369_);
                            v___x_374_ = lean_grind_internalize(
                                v_a_369_,
                                v_generation_344_,
                                v___x_373_,
                                v___y_358_,
                                v___y_359_,
                                v___y_360_,
                                v___y_361_,
                                v___y_362_,
                                v___y_363_,
                                v___y_364_,
                                v___y_365_,
                                v___y_366_,
                                v___y_367_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_374_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_374_, 1);
                                crate::leanh::lean_inc(v___y_367_);
                                crate::leanh::lean_inc_ref(v___y_366_);
                                crate::leanh::lean_inc(v___y_365_);
                                crate::leanh::lean_inc_ref(v___y_364_);
                                crate::leanh::lean_inc(v___y_363_);
                                crate::leanh::lean_inc_ref(v___y_362_);
                                crate::leanh::lean_inc(v___y_361_);
                                crate::leanh::lean_inc_ref(v___y_360_);
                                crate::leanh::lean_inc(v___y_359_);
                                crate::leanh::lean_inc(v___y_358_);
                                v___x_375_ = lean_grind_cutsat_mk_var(
                                    v_a_369_, v___y_358_, v___y_359_, v___y_360_, v___y_361_,
                                    v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_,
                                    v___y_367_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_375_) == 0 {
                                    v_a_376_ = crate::leanh::lean_ctor_get(v___x_375_, 0);
                                    v_isSharedCheck_384_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_375_)) as u8;
                                    if v_isSharedCheck_384_ == 0 {
                                        v___x_378_ = v___x_375_;
                                        v_isShared_379_ = v_isSharedCheck_384_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_376_);
                                        crate::leanh::lean_dec(v___x_375_);
                                        v___x_378_ = crate::leanh::lean_box(0);
                                        v_isShared_379_ = v_isSharedCheck_384_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    v_a_385_ = crate::leanh::lean_ctor_get(v___x_375_, 0);
                                    v_isSharedCheck_392_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_375_)) as u8;
                                    if v_isSharedCheck_392_ == 0 {
                                        v___x_387_ = v___x_375_;
                                        v_isShared_388_ = v_isSharedCheck_392_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_385_);
                                        crate::leanh::lean_dec(v___x_375_);
                                        v___x_387_ = crate::leanh::lean_box(0);
                                        v_isShared_388_ = v_isSharedCheck_392_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_369_);
                                v_a_393_ = crate::leanh::lean_ctor_get(v___x_374_, 0);
                                v_isSharedCheck_400_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_374_)) as u8;
                                if v_isSharedCheck_400_ == 0 {
                                    v___x_395_ = v___x_374_;
                                    v_isShared_396_ = v_isSharedCheck_400_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_393_);
                                    crate::leanh::lean_dec(v___x_374_);
                                    v___x_395_ = crate::leanh::lean_box(0);
                                    v_isShared_396_ = v_isSharedCheck_400_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_generation_344_);
                            crate::leanh::lean_inc(v___y_367_);
                            crate::leanh::lean_inc_ref(v___y_366_);
                            crate::leanh::lean_inc(v___y_365_);
                            crate::leanh::lean_inc_ref(v___y_364_);
                            crate::leanh::lean_inc(v___y_363_);
                            crate::leanh::lean_inc_ref(v___y_362_);
                            crate::leanh::lean_inc(v___y_361_);
                            crate::leanh::lean_inc_ref(v___y_360_);
                            crate::leanh::lean_inc(v___y_359_);
                            crate::leanh::lean_inc(v___y_358_);
                            v___x_401_ = lean_grind_cutsat_mk_var(
                                v_a_369_, v___y_358_, v___y_359_, v___y_360_, v___y_361_,
                                v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_,
                                v___y_367_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_401_) == 0 {
                                v_a_402_ = crate::leanh::lean_ctor_get(v___x_401_, 0);
                                v_isSharedCheck_410_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_401_)) as u8;
                                if v_isSharedCheck_410_ == 0 {
                                    v___x_404_ = v___x_401_;
                                    v_isShared_405_ = v_isSharedCheck_410_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_402_);
                                    crate::leanh::lean_dec(v___x_401_);
                                    v___x_404_ = crate::leanh::lean_box(0);
                                    v_isShared_405_ = v_isSharedCheck_410_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                v_a_411_ = crate::leanh::lean_ctor_get(v___x_401_, 0);
                                v_isSharedCheck_418_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_401_)) as u8;
                                if v_isSharedCheck_418_ == 0 {
                                    v___x_413_ = v___x_401_;
                                    v_isShared_414_ = v_isSharedCheck_418_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_411_);
                                    crate::leanh::lean_dec(v___x_401_);
                                    v___x_413_ = crate::leanh::lean_box(0);
                                    v_isShared_414_ = v_isSharedCheck_418_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_369_);
                        crate::leanh::lean_dec(v_generation_344_);
                        v_a_419_ = crate::leanh::lean_ctor_get(v___x_370_, 0);
                        v_isSharedCheck_426_ = (!crate::leanh::lean_is_exclusive(v___x_370_)) as u8;
                        if v_isSharedCheck_426_ == 0 {
                            v___x_421_ = v___x_370_;
                            v_isShared_422_ = v_isSharedCheck_426_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_419_);
                            crate::leanh::lean_dec(v___x_370_);
                            v___x_421_ = crate::leanh::lean_box(0);
                            v_isShared_422_ = v_isSharedCheck_426_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_generation_344_);
                    v_a_427_ = crate::leanh::lean_ctor_get(v___x_368_, 0);
                    v_isSharedCheck_434_ = (!crate::leanh::lean_is_exclusive(v___x_368_)) as u8;
                    if v_isSharedCheck_434_ == 0 {
                        v___x_429_ = v___x_368_;
                        v_isShared_430_ = v_isSharedCheck_434_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_427_);
                        crate::leanh::lean_dec(v___x_368_);
                        v___x_429_ = crate::leanh::lean_box(0);
                        v_isShared_430_ = v_isSharedCheck_434_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v___x_380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_380_, 0, v_a_376_);
                if v_isShared_379_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_378_, 0, v___x_380_);
                    v___x_382_ = v___x_378_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_383_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_380_);
                    v___x_382_ = v_reuseFailAlloc_383_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_382_;
            }
            4 => {
                if v_isShared_388_ == 0 {
                    v___x_390_ = v___x_387_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_391_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_391_, 0, v_a_385_);
                    v___x_390_ = v_reuseFailAlloc_391_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_390_;
            }
            6 => {
                if v_isShared_396_ == 0 {
                    v___x_398_ = v___x_395_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_399_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_399_, 0, v_a_393_);
                    v___x_398_ = v_reuseFailAlloc_399_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_398_;
            }
            8 => {
                v___x_406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_406_, 0, v_a_402_);
                if v_isShared_405_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_404_, 0, v___x_406_);
                    v___x_408_ = v___x_404_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_406_);
                    v___x_408_ = v_reuseFailAlloc_409_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_408_;
            }
            10 => {
                if v_isShared_414_ == 0 {
                    v___x_416_ = v___x_413_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_417_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_417_, 0, v_a_411_);
                    v___x_416_ = v_reuseFailAlloc_417_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_416_;
            }
            12 => {
                if v_isShared_422_ == 0 {
                    v___x_424_ = v___x_421_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_425_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_425_, 0, v_a_419_);
                    v___x_424_ = v_reuseFailAlloc_425_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_424_;
            }
            14 => {
                if v_isShared_430_ == 0 {
                    v___x_432_ = v___x_429_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_433_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_433_, 0, v_a_427_);
                    v___x_432_ = v_reuseFailAlloc_433_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_432_;
            }
            16 => {
                v___x_474_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_474_, 0, v_a_468_);
                crate::leanh::lean_ctor_set(v___x_474_, 1, v_a_470_);
                if v_isShared_473_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_472_, 0, v___x_474_);
                    v___x_476_ = v___x_472_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_474_);
                    v___x_476_ = v_reuseFailAlloc_477_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_476_;
            }
            18 => {
                if v_isShared_482_ == 0 {
                    v___x_484_ = v___x_481_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_485_, 0, v_a_479_);
                    v___x_484_ = v_reuseFailAlloc_485_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_484_;
            }
            20 => {
                v___x_498_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_498_, 0, v_a_492_);
                crate::leanh::lean_ctor_set(v___x_498_, 1, v_a_494_);
                if v_isShared_497_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_496_, 0, v___x_498_);
                    v___x_500_ = v___x_496_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_501_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_501_, 0, v___x_498_);
                    v___x_500_ = v_reuseFailAlloc_501_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_500_;
            }
            22 => {
                if v_isShared_506_ == 0 {
                    v___x_508_ = v___x_505_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_509_, 0, v_a_503_);
                    v___x_508_ = v_reuseFailAlloc_509_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_508_;
            }
            24 => {
                v___x_525_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_525_, 0, v_a_521_);
                crate::leanh::lean_ctor_set(v___x_525_, 1, v_val_518_);
                if v_isShared_524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_523_, 0, v___x_525_);
                    v___x_527_ = v___x_523_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
                    v___x_527_ = v_reuseFailAlloc_528_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_527_;
            }
            26 => {
                if v_isShared_533_ == 0 {
                    v___x_535_ = v___x_532_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_530_);
                    v___x_535_ = v_reuseFailAlloc_536_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_535_;
            }
            28 => {
                v___x_545_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_545_, 0, v_val_538_);
                crate::leanh::lean_ctor_set(v___x_545_, 1, v_a_541_);
                if v_isShared_544_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_543_, 0, v___x_545_);
                    v___x_547_ = v___x_543_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_548_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_548_, 0, v___x_545_);
                    v___x_547_ = v_reuseFailAlloc_548_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_547_;
            }
            30 => {
                if v_isShared_553_ == 0 {
                    v___x_555_ = v___x_552_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
                    v___x_555_ = v_reuseFailAlloc_556_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_555_;
            }
            32 => {
                if v_isShared_561_ == 0 {
                    v___x_563_ = v___x_560_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_564_, 0, v_a_558_);
                    v___x_563_ = v_reuseFailAlloc_564_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_563_;
            }
            34 => {
                if crate::leanh::lean_obj_tag(v_a_567_) == 1 {
                    crate::leanh::lean_dec(v_generation_344_);
                    crate::leanh::lean_dec_ref(v_e_343_);
                    v_val_571_ = crate::leanh::lean_ctor_get(v_a_567_, 0);
                    v_isSharedCheck_581_ = (!crate::leanh::lean_is_exclusive(v_a_567_)) as u8;
                    if v_isSharedCheck_581_ == 0 {
                        v___x_573_ = v_a_567_;
                        v_isShared_574_ = v_isSharedCheck_581_;
                        state = 35;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_571_);
                        crate::leanh::lean_dec(v_a_567_);
                        v___x_573_ = crate::leanh::lean_box(0);
                        v_isShared_574_ = v_isSharedCheck_581_;
                        state = 35;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_569_);
                    crate::leanh::lean_dec(v_a_567_);
                    v_e_357_ = v_e_343_;
                    v___y_358_ = v_a_345_;
                    v___y_359_ = v_a_346_;
                    v___y_360_ = v_a_347_;
                    v___y_361_ = v_a_348_;
                    v___y_362_ = v_a_349_;
                    v___y_363_ = v_a_350_;
                    v___y_364_ = v_a_351_;
                    v___y_365_ = v_a_352_;
                    v___y_366_ = v_a_353_;
                    v___y_367_ = v_a_354_;
                    state = 1;
                    continue;
                }
            }
            35 => {
                if v_isShared_574_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_573_, 0);
                    v___x_576_ = v___x_573_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_580_, 0, v_val_571_);
                    v___x_576_ = v_reuseFailAlloc_580_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_570_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_569_, 0, v___x_576_);
                    v___x_578_ = v___x_569_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_579_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_579_, 0, v___x_576_);
                    v___x_578_ = v_reuseFailAlloc_579_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_578_;
            }
            38 => {
                if v_isShared_586_ == 0 {
                    v___x_588_ = v___x_585_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_589_, 0, v_a_583_);
                    v___x_588_ = v_reuseFailAlloc_589_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_588_;
            }
            40 => {
                v___x_600_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_600_, 0, v_a_596_);
                if v_isShared_599_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_598_, 0, v___x_600_);
                    v___x_602_ = v___x_598_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_603_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_600_);
                    v___x_602_ = v_reuseFailAlloc_603_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_602_;
            }
            42 => {
                if v_isShared_608_ == 0 {
                    v___x_610_ = v___x_607_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_611_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_611_, 0, v_a_605_);
                    v___x_610_ = v_reuseFailAlloc_611_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_610_;
            }
            44 => {
                if v_isShared_616_ == 0 {
                    v___x_618_ = v___x_615_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
                    v___x_618_ = v_reuseFailAlloc_619_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_618_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr___boxed(
    mut v_e_621_: *mut crate::leanh::LeanObject,
    mut v_generation_622_: *mut crate::leanh::LeanObject,
    mut v_a_623_: *mut crate::leanh::LeanObject,
    mut v_a_624_: *mut crate::leanh::LeanObject,
    mut v_a_625_: *mut crate::leanh::LeanObject,
    mut v_a_626_: *mut crate::leanh::LeanObject,
    mut v_a_627_: *mut crate::leanh::LeanObject,
    mut v_a_628_: *mut crate::leanh::LeanObject,
    mut v_a_629_: *mut crate::leanh::LeanObject,
    mut v_a_630_: *mut crate::leanh::LeanObject,
    mut v_a_631_: *mut crate::leanh::LeanObject,
    mut v_a_632_: *mut crate::leanh::LeanObject,
    mut v_a_633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_634_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(
        v_e_621_,
        v_generation_622_,
        v_a_623_,
        v_a_624_,
        v_a_625_,
        v_a_626_,
        v_a_627_,
        v_a_628_,
        v_a_629_,
        v_a_630_,
        v_a_631_,
        v_a_632_,
    );
    crate::leanh::lean_dec(v_a_632_);
    crate::leanh::lean_dec_ref(v_a_631_);
    crate::leanh::lean_dec(v_a_630_);
    crate::leanh::lean_dec_ref(v_a_629_);
    crate::leanh::lean_dec(v_a_628_);
    crate::leanh::lean_dec_ref(v_a_627_);
    crate::leanh::lean_dec(v_a_626_);
    crate::leanh::lean_dec_ref(v_a_625_);
    crate::leanh::lean_dec(v_a_624_);
    crate::leanh::lean_dec(v_a_623_);
    return v_res_634_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_IntInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_IntInstTesters(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
}
