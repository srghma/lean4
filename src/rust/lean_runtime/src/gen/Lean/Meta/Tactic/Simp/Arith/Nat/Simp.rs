// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Simp
// Imports: Lean.Meta.Tactic.Simp.Arith.Util Lean.Meta.Tactic.Simp.Arith.Nat.Basic Lean.Meta.AppBuilder
use crate::r#gen::Init::Data::Nat::Linear::{
    l_Nat_Linear_Expr_toPoly, l_Nat_Linear_ExprCnstr_toPoly, l_Nat_Linear_Poly_norm,
    l_Nat_Linear_Poly_toExpr, l_Nat_Linear_PolyCnstr_isUnsat, l_Nat_Linear_PolyCnstr_isValid,
    l_Nat_Linear_PolyCnstr_norm, l_Nat_Linear_PolyCnstr_toExpr, l_Nat_Linear_instBEqExpr_beq,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_isApp, l_Lean_Expr_isAppOfArity, l_Lean_Expr_isConstOf, l_Lean_eagerReflBoolTrue,
    l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp6, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkNatAdd,
    l_Lean_mkNatEq, l_Lean_mkNatLE, l_Lean_mkNatLit, l_Lean_mkPropEq, l_Lean_mkSort,
};
use crate::r#gen::Lean::Level::l_Lean_Level_succ___override;
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkExpectedPropHint,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_instantiateMVarsIfMVarApp___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Nat::Basic::{
    initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic,
    l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg,
    l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr,
    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg,
    l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr, l_Lean_Meta_Simp_Arith_Nat_toContextExpr,
    l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f, l_Lean_Meta_Simp_Arith_Nat_toLinearExpr,
    runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Util::{
    initialize_Lean_Meta_Tactic_Simp_Arith_Util,
    runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value: LeanStringObject<4> =
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
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value: LeanStringObject<7> =
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
        m_data: [76, 105, 110, 101, 97, 114, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [69, 120, 112, 114, 67, 110, 115, 116, 114, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            101, 113, 95, 111, 102, 95, 116, 111, 78, 111, 114, 109, 80, 111, 108, 121, 95, 101,
            113, 0,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value)
                as *mut LeanObject,
            7629568945124732217 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value)
                as *mut LeanObject,
            6028090968349347099 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6_value: LeanStringObject<5> =
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
        m_data: [84, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__6_value)
                as *mut LeanObject,
            11870096045526947150 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_value: LeanStringObject<19> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 19,
        m_capacity: 19,
        m_length: 18,
        m_data: [
            101, 113, 95, 116, 114, 117, 101, 95, 111, 102, 95, 105, 115, 86, 97, 108, 105, 100, 0,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value)
                as *mut LeanObject,
            7629568945124732217 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__9_value)
                as *mut LeanObject,
            4574354164886414687 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [70, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__12_value)
                as *mut LeanObject,
            907667957179513571 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            101, 113, 95, 102, 97, 108, 115, 101, 95, 111, 102, 95, 105, 115, 85, 110, 115, 97,
            116, 0,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__2_value)
                as *mut LeanObject,
            7629568945124732217 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__15_value)
                as *mut LeanObject,
            10664531703608190244 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 110, 115, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__0_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__1_value)
                as *mut LeanObject,
            17532416664988428445 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7_value: LeanStringObject<4> =
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
        m_data: [78, 111, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__7_value)
                as *mut LeanObject,
            16612019923665488825 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [71, 84, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [103, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__9_value)
                as *mut LeanObject,
            2272833755566510320 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__10_value)
                as *mut LeanObject,
            9426339939459091439 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [76, 84, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [108, 116, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__12_value)
                as *mut LeanObject,
            17878876274162330439 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__13_value)
                as *mut LeanObject,
            11833570877100518198 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [71, 69, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [103, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__15_value)
                as *mut LeanObject,
            1755019837031360842 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__16_value)
                as *mut LeanObject,
            5555145617058846791 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [76, 69, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [108, 101, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__18_value)
                as *mut LeanObject,
            8347582161988589016 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__19_value)
                as *mut LeanObject,
            7316284823769321069 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 111, 116, 95, 108, 101, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__23_value)
                as *mut LeanObject,
            4324381115663783915 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 111, 116, 95, 103, 101, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__26_value)
                as *mut LeanObject,
            16050530035529649249 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 111, 116, 95, 108, 116, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__29_value)
                as *mut LeanObject,
            11906387800666752824 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 111, 116, 95, 103, 116, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__32_value)
                as *mut LeanObject,
            14438326155402529092 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0_value: LeanStringObject<5> =
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
        m_data: [69, 120, 112, 114, 0],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0_value)
        as *mut LeanObject;
static l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__0_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__1_value)
                as *mut LeanObject,
            7207443721092690486 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__0_value)
                as *mut LeanObject,
            5346548721068792964 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__3_value)
                as *mut LeanObject,
            10210312251999725498 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5() -> *mut LeanObject {
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    v___x_547_ = lean_box(0);
    v___x_548_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__4;
    v___x_549_ = l_Lean_mkConst(v___x_548_, v___x_547_);
    return v___x_549_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8() -> *mut LeanObject {
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    v___x_553_ = lean_box(0);
    v___x_554_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__7;
    v___x_555_ = l_Lean_mkConst(v___x_554_, v___x_553_);
    return v___x_555_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11() -> *mut LeanObject {
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v___x_562_ = lean_box(0);
    v___x_563_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__10;
    v___x_564_ = l_Lean_mkConst(v___x_563_, v___x_562_);
    return v___x_564_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14() -> *mut LeanObject {
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    v___x_568_ = lean_box(0);
    v___x_569_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__13;
    v___x_570_ = l_Lean_mkConst(v___x_569_, v___x_568_);
    return v___x_570_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17() -> *mut LeanObject {
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    v___x_577_ = lean_box(0);
    v___x_578_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__16;
    v___x_579_ = l_Lean_mkConst(v___x_578_, v___x_577_);
    return v___x_579_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(
    mut v_e_580_: *mut LeanObject,
    mut v_a_581_: *mut LeanObject,
    mut v_a_582_: *mut LeanObject,
    mut v_a_583_: *mut LeanObject,
    mut v_a_584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_590_: u8 = 0;
    let mut v_val_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v_fst_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_599_: u8 = 0;
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: u8 = 0;
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_611_: u8 = 0;
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_617_: u8 = 0;
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_634_: u8 = 0;
    let mut v_a_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_638_: u8 = 0;
    let mut v___x_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_642_: u8 = 0;
    let mut v___x_643_: u8 = 0;
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_648_: u8 = 0;
    let mut v_a_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_652_: u8 = 0;
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_661_: u8 = 0;
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_678_: u8 = 0;
    let mut v_a_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_682_: u8 = 0;
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_686_: u8 = 0;
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_691_: u8 = 0;
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_708_: u8 = 0;
    let mut v_a_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_716_: u8 = 0;
    let mut v_a_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_720_: u8 = 0;
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_724_: u8 = 0;
    let mut v_isSharedCheck_725_: u8 = 0;
    let mut v_isSharedCheck_726_: u8 = 0;
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_731_: u8 = 0;
    let mut v_a_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_735_: u8 = 0;
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_739_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_586_ = l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(
                    v_e_580_, v_a_581_, v_a_582_, v_a_583_, v_a_584_,
                );
                if lean_obj_tag(v___x_586_) == 0 {
                    v_a_587_ = lean_ctor_get(v___x_586_, 0);
                    v_isSharedCheck_731_ = (!lean_is_exclusive(v___x_586_)) as u8;
                    if v_isSharedCheck_731_ == 0 {
                        v___x_589_ = v___x_586_;
                        v_isShared_590_ = v_isSharedCheck_731_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_587_);
                        lean_dec(v___x_586_);
                        v___x_589_ = lean_box(0);
                        v_isShared_590_ = v_isSharedCheck_731_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_732_ = lean_ctor_get(v___x_586_, 0);
                    v_isSharedCheck_739_ = (!lean_is_exclusive(v___x_586_)) as u8;
                    if v_isSharedCheck_739_ == 0 {
                        v___x_734_ = v___x_586_;
                        v_isShared_735_ = v_isSharedCheck_739_;
                        state = 30;
                        continue;
                    } else {
                        lean_inc(v_a_732_);
                        lean_dec(v___x_586_);
                        v___x_734_ = lean_box(0);
                        v_isShared_735_ = v_isSharedCheck_739_;
                        state = 30;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_587_) == 1 {
                    lean_del_object(v___x_589_);
                    v_val_591_ = lean_ctor_get(v_a_587_, 0);
                    v_isSharedCheck_726_ = (!lean_is_exclusive(v_a_587_)) as u8;
                    if v_isSharedCheck_726_ == 0 {
                        v___x_593_ = v_a_587_;
                        v_isShared_594_ = v_isSharedCheck_726_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_591_);
                        lean_dec(v_a_587_);
                        v___x_593_ = lean_box(0);
                        v_isShared_594_ = v_isSharedCheck_726_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_587_);
                    v___x_727_ = lean_box(0);
                    if v_isShared_590_ == 0 {
                        lean_ctor_set(v___x_589_, 0, v___x_727_);
                        v___x_729_ = v___x_589_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
                        v___x_729_ = v_reuseFailAlloc_730_;
                        state = 29;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_595_ = lean_ctor_get(v_val_591_, 0);
                v_snd_596_ = lean_ctor_get(v_val_591_, 1);
                v_isSharedCheck_725_ = (!lean_is_exclusive(v_val_591_)) as u8;
                if v_isSharedCheck_725_ == 0 {
                    v___x_598_ = v_val_591_;
                    v_isShared_599_ = v_isSharedCheck_725_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_596_);
                    lean_inc(v_fst_595_);
                    lean_dec(v_val_591_);
                    v___x_598_ = lean_box(0);
                    v_isShared_599_ = v_isSharedCheck_725_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc(v_fst_595_);
                v___x_600_ =
                    l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(v_snd_596_, v_fst_595_);
                if lean_obj_tag(v___x_600_) == 0 {
                    v_a_601_ = lean_ctor_get(v___x_600_, 0);
                    lean_inc(v_a_601_);
                    lean_dec_ref_known(v___x_600_, 1);
                    lean_inc(v_fst_595_);
                    v___x_602_ = l_Nat_Linear_ExprCnstr_toPoly(v_fst_595_);
                    v___x_603_ = l_Nat_Linear_PolyCnstr_norm(v___x_602_);
                    v___x_604_ = l_Nat_Linear_PolyCnstr_isUnsat(v___x_603_);
                    if v___x_604_ == 0 {
                        v___x_605_ = l_Nat_Linear_PolyCnstr_isValid(v___x_603_);
                        if v___x_605_ == 0 {
                            v___x_606_ = l_Nat_Linear_PolyCnstr_toExpr(v___x_603_);
                            lean_inc_ref(v___x_606_);
                            v___x_607_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(
                                v_snd_596_, v___x_606_,
                            );
                            if lean_obj_tag(v___x_607_) == 0 {
                                v_a_608_ = lean_ctor_get(v___x_607_, 0);
                                v_isSharedCheck_648_ = (!lean_is_exclusive(v___x_607_)) as u8;
                                if v_isSharedCheck_648_ == 0 {
                                    v___x_610_ = v___x_607_;
                                    v_isShared_611_ = v_isSharedCheck_648_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_608_);
                                    lean_dec(v___x_607_);
                                    v___x_610_ = lean_box(0);
                                    v_isShared_611_ = v_isSharedCheck_648_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_606_);
                                lean_dec(v_a_601_);
                                lean_del_object(v___x_598_);
                                lean_dec(v_snd_596_);
                                lean_dec(v_fst_595_);
                                lean_del_object(v___x_593_);
                                v_a_649_ = lean_ctor_get(v___x_607_, 0);
                                v_isSharedCheck_656_ = (!lean_is_exclusive(v___x_607_)) as u8;
                                if v_isSharedCheck_656_ == 0 {
                                    v___x_651_ = v___x_607_;
                                    v_isShared_652_ = v_isSharedCheck_656_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_a_649_);
                                    lean_dec(v___x_607_);
                                    v___x_651_ = lean_box(0);
                                    v_isShared_652_ = v_isSharedCheck_656_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_603_);
                            v___x_657_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(
                                v_snd_596_, v_a_581_, v_a_582_, v_a_583_, v_a_584_,
                            );
                            if lean_obj_tag(v___x_657_) == 0 {
                                v_a_658_ = lean_ctor_get(v___x_657_, 0);
                                v_isSharedCheck_678_ = (!lean_is_exclusive(v___x_657_)) as u8;
                                if v_isSharedCheck_678_ == 0 {
                                    v___x_660_ = v___x_657_;
                                    v_isShared_661_ = v_isSharedCheck_678_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_658_);
                                    lean_dec(v___x_657_);
                                    v___x_660_ = lean_box(0);
                                    v_isShared_661_ = v_isSharedCheck_678_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_601_);
                                lean_del_object(v___x_598_);
                                lean_dec(v_fst_595_);
                                lean_del_object(v___x_593_);
                                v_a_679_ = lean_ctor_get(v___x_657_, 0);
                                v_isSharedCheck_686_ = (!lean_is_exclusive(v___x_657_)) as u8;
                                if v_isSharedCheck_686_ == 0 {
                                    v___x_681_ = v___x_657_;
                                    v_isShared_682_ = v_isSharedCheck_686_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_679_);
                                    lean_dec(v___x_657_);
                                    v___x_681_ = lean_box(0);
                                    v_isShared_682_ = v_isSharedCheck_686_;
                                    state = 19;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_603_);
                        v___x_687_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(
                            v_snd_596_, v_a_581_, v_a_582_, v_a_583_, v_a_584_,
                        );
                        if lean_obj_tag(v___x_687_) == 0 {
                            v_a_688_ = lean_ctor_get(v___x_687_, 0);
                            v_isSharedCheck_708_ = (!lean_is_exclusive(v___x_687_)) as u8;
                            if v_isSharedCheck_708_ == 0 {
                                v___x_690_ = v___x_687_;
                                v_isShared_691_ = v_isSharedCheck_708_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_688_);
                                lean_dec(v___x_687_);
                                v___x_690_ = lean_box(0);
                                v_isShared_691_ = v_isSharedCheck_708_;
                                state = 21;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_601_);
                            lean_del_object(v___x_598_);
                            lean_dec(v_fst_595_);
                            lean_del_object(v___x_593_);
                            v_a_709_ = lean_ctor_get(v___x_687_, 0);
                            v_isSharedCheck_716_ = (!lean_is_exclusive(v___x_687_)) as u8;
                            if v_isSharedCheck_716_ == 0 {
                                v___x_711_ = v___x_687_;
                                v_isShared_712_ = v_isSharedCheck_716_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_709_);
                                lean_dec(v___x_687_);
                                v___x_711_ = lean_box(0);
                                v_isShared_712_ = v_isSharedCheck_716_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_598_);
                    lean_dec(v_snd_596_);
                    lean_dec(v_fst_595_);
                    lean_del_object(v___x_593_);
                    v_a_717_ = lean_ctor_get(v___x_600_, 0);
                    v_isSharedCheck_724_ = (!lean_is_exclusive(v___x_600_)) as u8;
                    if v_isSharedCheck_724_ == 0 {
                        v___x_719_ = v___x_600_;
                        v_isShared_720_ = v_isSharedCheck_724_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_717_);
                        lean_dec(v___x_600_);
                        v___x_719_ = lean_box(0);
                        v_isShared_720_ = v_isSharedCheck_724_;
                        state = 27;
                        continue;
                    }
                }
            }
            4 => {
                v___x_643_ = lean_expr_eqv(v_a_608_, v_a_601_);
                if v___x_643_ == 0 {
                    lean_del_object(v___x_610_);
                    state = 5;
                    continue;
                } else {
                    if v___x_605_ == 0 {
                        lean_dec(v_a_608_);
                        lean_dec_ref(v___x_606_);
                        lean_dec(v_a_601_);
                        lean_del_object(v___x_598_);
                        lean_dec(v_snd_596_);
                        lean_dec(v_fst_595_);
                        lean_del_object(v___x_593_);
                        v___x_644_ = lean_box(0);
                        if v_isShared_611_ == 0 {
                            lean_ctor_set(v___x_610_, 0, v___x_644_);
                            v___x_646_ = v___x_610_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_647_, 0, v___x_644_);
                            v___x_646_ = v_reuseFailAlloc_647_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_610_);
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_613_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(
                    v_snd_596_, v_a_581_, v_a_582_, v_a_583_, v_a_584_,
                );
                if lean_obj_tag(v___x_613_) == 0 {
                    v_a_614_ = lean_ctor_get(v___x_613_, 0);
                    v_isSharedCheck_634_ = (!lean_is_exclusive(v___x_613_)) as u8;
                    if v_isSharedCheck_634_ == 0 {
                        v___x_616_ = v___x_613_;
                        v_isShared_617_ = v_isSharedCheck_634_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_614_);
                        lean_dec(v___x_613_);
                        v___x_616_ = lean_box(0);
                        v_isShared_617_ = v_isSharedCheck_634_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_a_608_);
                    lean_dec_ref(v___x_606_);
                    lean_dec(v_a_601_);
                    lean_del_object(v___x_598_);
                    lean_dec(v_fst_595_);
                    lean_del_object(v___x_593_);
                    v_a_635_ = lean_ctor_get(v___x_613_, 0);
                    v_isSharedCheck_642_ = (!lean_is_exclusive(v___x_613_)) as u8;
                    if v_isSharedCheck_642_ == 0 {
                        v___x_637_ = v___x_613_;
                        v_isShared_638_ = v_isSharedCheck_642_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_635_);
                        lean_dec(v___x_613_);
                        v___x_637_ = lean_box(0);
                        v_isShared_638_ = v_isSharedCheck_642_;
                        state = 10;
                        continue;
                    }
                }
            }
            6 => {
                v___x_618_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__5,
                );
                v___x_619_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_595_);
                v___x_620_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v___x_606_);
                v___x_621_ = l_Lean_eagerReflBoolTrue;
                v___x_622_ =
                    l_Lean_mkApp4(v___x_618_, v_a_614_, v___x_619_, v___x_620_, v___x_621_);
                lean_inc(v_a_608_);
                v___x_623_ = l_Lean_mkPropEq(v_a_601_, v_a_608_);
                v___x_624_ = l_Lean_Meta_mkExpectedPropHint(v___x_622_, v___x_623_);
                if v_isShared_599_ == 0 {
                    lean_ctor_set(v___x_598_, 1, v___x_624_);
                    lean_ctor_set(v___x_598_, 0, v_a_608_);
                    v___x_626_ = v___x_598_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_633_, 0, v_a_608_);
                    lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_624_);
                    v___x_626_ = v_reuseFailAlloc_633_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_594_ == 0 {
                    lean_ctor_set(v___x_593_, 0, v___x_626_);
                    v___x_628_ = v___x_593_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_632_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_626_);
                    v___x_628_ = v_reuseFailAlloc_632_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_617_ == 0 {
                    lean_ctor_set(v___x_616_, 0, v___x_628_);
                    v___x_630_ = v___x_616_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
                    v___x_630_ = v_reuseFailAlloc_631_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_630_;
            }
            10 => {
                if v_isShared_638_ == 0 {
                    v___x_640_ = v___x_637_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_641_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_641_, 0, v_a_635_);
                    v___x_640_ = v_reuseFailAlloc_641_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_640_;
            }
            12 => {
                return v___x_646_;
            }
            13 => {
                if v_isShared_652_ == 0 {
                    v___x_654_ = v___x_651_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_655_, 0, v_a_649_);
                    v___x_654_ = v_reuseFailAlloc_655_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_654_;
            }
            15 => {
                v___x_662_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__8,
                );
                v___x_663_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__11,
                );
                v___x_664_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_595_);
                v___x_665_ = l_Lean_eagerReflBoolTrue;
                v___x_666_ = l_Lean_mkApp3(v___x_663_, v_a_658_, v___x_664_, v___x_665_);
                v___x_667_ = l_Lean_mkPropEq(v_a_601_, v___x_662_);
                v___x_668_ = l_Lean_Meta_mkExpectedPropHint(v___x_666_, v___x_667_);
                if v_isShared_599_ == 0 {
                    lean_ctor_set(v___x_598_, 1, v___x_668_);
                    lean_ctor_set(v___x_598_, 0, v___x_662_);
                    v___x_670_ = v___x_598_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_662_);
                    lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_668_);
                    v___x_670_ = v_reuseFailAlloc_677_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_594_ == 0 {
                    lean_ctor_set(v___x_593_, 0, v___x_670_);
                    v___x_672_ = v___x_593_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_676_, 0, v___x_670_);
                    v___x_672_ = v_reuseFailAlloc_676_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_661_ == 0 {
                    lean_ctor_set(v___x_660_, 0, v___x_672_);
                    v___x_674_ = v___x_660_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_675_, 0, v___x_672_);
                    v___x_674_ = v_reuseFailAlloc_675_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_674_;
            }
            19 => {
                if v_isShared_682_ == 0 {
                    v___x_684_ = v___x_681_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_685_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_685_, 0, v_a_679_);
                    v___x_684_ = v_reuseFailAlloc_685_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_684_;
            }
            21 => {
                v___x_692_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__14,
                );
                v___x_693_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___closed__17,
                );
                v___x_694_ = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(v_fst_595_);
                v___x_695_ = l_Lean_eagerReflBoolTrue;
                v___x_696_ = l_Lean_mkApp3(v___x_693_, v_a_688_, v___x_694_, v___x_695_);
                v___x_697_ = l_Lean_mkPropEq(v_a_601_, v___x_692_);
                v___x_698_ = l_Lean_Meta_mkExpectedPropHint(v___x_696_, v___x_697_);
                if v_isShared_599_ == 0 {
                    lean_ctor_set(v___x_598_, 1, v___x_698_);
                    lean_ctor_set(v___x_598_, 0, v___x_692_);
                    v___x_700_ = v___x_598_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_692_);
                    lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_698_);
                    v___x_700_ = v_reuseFailAlloc_707_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                if v_isShared_594_ == 0 {
                    lean_ctor_set(v___x_593_, 0, v___x_700_);
                    v___x_702_ = v___x_593_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_706_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_700_);
                    v___x_702_ = v_reuseFailAlloc_706_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_691_ == 0 {
                    lean_ctor_set(v___x_690_, 0, v___x_702_);
                    v___x_704_ = v___x_690_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_702_);
                    v___x_704_ = v_reuseFailAlloc_705_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_704_;
            }
            25 => {
                if v_isShared_712_ == 0 {
                    v___x_714_ = v___x_711_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_715_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_715_, 0, v_a_709_);
                    v___x_714_ = v_reuseFailAlloc_715_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_714_;
            }
            27 => {
                if v_isShared_720_ == 0 {
                    v___x_722_ = v___x_719_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
                    v___x_722_ = v_reuseFailAlloc_723_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_722_;
            }
            29 => {
                return v___x_729_;
            }
            30 => {
                if v_isShared_735_ == 0 {
                    v___x_737_ = v___x_734_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_738_, 0, v_a_732_);
                    v___x_737_ = v_reuseFailAlloc_738_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_737_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f___boxed(
    mut v_e_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
    mut v_a_742_: *mut LeanObject,
    mut v_a_743_: *mut LeanObject,
    mut v_a_744_: *mut LeanObject,
    mut v_a_745_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_746_: *mut LeanObject = core::ptr::null_mut();
    v_res_746_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(
        v_e_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_,
    );
    lean_dec(v_a_744_);
    lean_dec_ref(v_a_743_);
    lean_dec(v_a_742_);
    lean_dec_ref(v_a_741_);
    return v_res_746_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3() -> *mut LeanObject {
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    v___x_752_ = lean_box(0);
    v___x_753_ = l_Lean_Level_succ___override(v___x_752_);
    return v___x_753_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4() -> *mut LeanObject {
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    v___x_754_ = lean_box(0);
    v___x_755_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__3,
    );
    v___x_756_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_756_, 0, v___x_755_);
    lean_ctor_set(v___x_756_, 1, v___x_754_);
    return v___x_756_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5() -> *mut LeanObject {
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    v___x_757_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4_once),
        _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__4,
    );
    v___x_758_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__2;
    v___x_759_ = l_Lean_mkConst(v___x_758_, v___x_757_);
    return v___x_759_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6() -> *mut LeanObject {
    let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    v___x_760_ = lean_box(0);
    v___x_761_ = l_Lean_mkSort(v___x_760_);
    return v___x_761_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22() -> *mut LeanObject {
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_787_ = lean_unsigned_to_nat(1);
    v___x_788_ = l_Lean_mkNatLit(v___x_787_);
    return v___x_788_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25() -> *mut LeanObject {
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    v___x_793_ = lean_box(0);
    v___x_794_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__24;
    v___x_795_ = l_Lean_mkConst(v___x_794_, v___x_793_);
    return v___x_795_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28() -> *mut LeanObject {
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    v___x_800_ = lean_box(0);
    v___x_801_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__27;
    v___x_802_ = l_Lean_mkConst(v___x_801_, v___x_800_);
    return v___x_802_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31() -> *mut LeanObject {
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    v___x_807_ = lean_box(0);
    v___x_808_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__30;
    v___x_809_ = l_Lean_mkConst(v___x_808_, v___x_807_);
    return v___x_809_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34() -> *mut LeanObject {
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    v___x_814_ = lean_box(0);
    v___x_815_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__33;
    v___x_816_ = l_Lean_mkConst(v___x_815_, v___x_814_);
    return v___x_816_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(
    mut v_e_817_: *mut LeanObject,
    mut v_a_818_: *mut LeanObject,
    mut v_a_819_: *mut LeanObject,
    mut v_a_820_: *mut LeanObject,
    mut v_a_821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_h_u2081_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_837_: u8 = 0;
    let mut v_val_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v_fst_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_846_: u8 = 0;
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_859_: u8 = 0;
    let mut v_isSharedCheck_860_: u8 = 0;
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_866_: u8 = 0;
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: u8 = 0;
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: u8 = 0;
    let mut v_arg_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v_arg_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: u8 = 0;
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: u8 = 0;
    let mut v_arg_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: u8 = 0;
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: u8 = 0;
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: u8 = 0;
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u8 = 0;
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_907_: u8 = 0;
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_911_: u8 = 0;
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: u8 = 0;
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_925_: u8 = 0;
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_929_: u8 = 0;
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: u8 = 0;
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_941_: u8 = 0;
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_945_: u8 = 0;
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: u8 = 0;
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_957_: u8 = 0;
    let mut v___x_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_961_: u8 = 0;
    let mut v_a_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_965_: u8 = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_969_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_867_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__8;
                v___x_868_ = lean_unsigned_to_nat(1);
                v___x_869_ = l_Lean_Expr_isAppOfArity(v_e_817_, v___x_867_, v___x_868_);
                if v___x_869_ == 0 {
                    v___x_870_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(
                        v_e_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_,
                    );
                    return v___x_870_;
                } else {
                    v___x_871_ = l_Lean_Expr_appArg_x21(v_e_817_);
                    v___x_872_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v___x_871_, v_a_819_);
                    if lean_obj_tag(v___x_872_) == 0 {
                        v_a_873_ = lean_ctor_get(v___x_872_, 0);
                        lean_inc(v_a_873_);
                        lean_dec_ref_known(v___x_872_, 1);
                        v___x_874_ = l_Lean_Expr_cleanupAnnotations(v_a_873_);
                        v___x_875_ = l_Lean_Expr_isApp(v___x_874_);
                        if v___x_875_ == 0 {
                            lean_dec_ref(v___x_874_);
                            lean_dec_ref(v_e_817_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_876_ = lean_ctor_get(v___x_874_, 1);
                            lean_inc_ref(v_arg_876_);
                            v___x_877_ = l_Lean_Expr_appFnCleanup___redArg(v___x_874_);
                            v___x_878_ = l_Lean_Expr_isApp(v___x_877_);
                            if v___x_878_ == 0 {
                                lean_dec_ref(v___x_877_);
                                lean_dec_ref(v_arg_876_);
                                lean_dec_ref(v_e_817_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_879_ = lean_ctor_get(v___x_877_, 1);
                                lean_inc_ref(v_arg_879_);
                                v___x_880_ = l_Lean_Expr_appFnCleanup___redArg(v___x_877_);
                                v___x_881_ = l_Lean_Expr_isApp(v___x_880_);
                                if v___x_881_ == 0 {
                                    lean_dec_ref(v___x_880_);
                                    lean_dec_ref(v_arg_879_);
                                    lean_dec_ref(v_arg_876_);
                                    lean_dec_ref(v_e_817_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_882_ = l_Lean_Expr_appFnCleanup___redArg(v___x_880_);
                                    v___x_883_ = l_Lean_Expr_isApp(v___x_882_);
                                    if v___x_883_ == 0 {
                                        lean_dec_ref(v___x_882_);
                                        lean_dec_ref(v_arg_879_);
                                        lean_dec_ref(v_arg_876_);
                                        lean_dec_ref(v_e_817_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v_arg_884_ = lean_ctor_get(v___x_882_, 1);
                                        lean_inc_ref(v_arg_884_);
                                        v___x_885_ = l_Lean_Expr_appFnCleanup___redArg(v___x_882_);
                                        v___x_886_ =
                                            l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__11;
                                        v___x_887_ = l_Lean_Expr_isConstOf(v___x_885_, v___x_886_);
                                        if v___x_887_ == 0 {
                                            v___x_888_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__14;
                                            v___x_889_ =
                                                l_Lean_Expr_isConstOf(v___x_885_, v___x_888_);
                                            if v___x_889_ == 0 {
                                                v___x_890_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__17;
                                                v___x_891_ =
                                                    l_Lean_Expr_isConstOf(v___x_885_, v___x_890_);
                                                if v___x_891_ == 0 {
                                                    v___x_892_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__20;
                                                    v___x_893_ = l_Lean_Expr_isConstOf(
                                                        v___x_885_, v___x_892_,
                                                    );
                                                    lean_dec_ref(v___x_885_);
                                                    if v___x_893_ == 0 {
                                                        lean_dec_ref(v_arg_884_);
                                                        lean_dec_ref(v_arg_879_);
                                                        lean_dec_ref(v_arg_876_);
                                                        lean_dec_ref(v_e_817_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_894_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_884_, v_a_819_);
                                                        if lean_obj_tag(v___x_894_) == 0 {
                                                            v_a_895_ = lean_ctor_get(v___x_894_, 0);
                                                            lean_inc(v_a_895_);
                                                            lean_dec_ref_known(v___x_894_, 1);
                                                            v___x_896_ =
                                                                l_Lean_Expr_cleanupAnnotations(
                                                                    v_a_895_,
                                                                );
                                                            v___x_897_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21;
                                                            v___x_898_ = l_Lean_Expr_isConstOf(
                                                                v___x_896_, v___x_897_,
                                                            );
                                                            lean_dec_ref(v___x_896_);
                                                            if v___x_898_ == 0 {
                                                                lean_dec_ref(v_arg_879_);
                                                                lean_dec_ref(v_arg_876_);
                                                                lean_dec_ref(v_e_817_);
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_899_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once), _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
                                                                lean_inc_ref(v_arg_876_);
                                                                v___x_900_ = l_Lean_mkNatAdd(
                                                                    v_arg_876_, v___x_899_,
                                                                );
                                                                lean_inc_ref(v_arg_879_);
                                                                v___x_901_ = l_Lean_mkNatLE(
                                                                    v___x_900_, v_arg_879_,
                                                                );
                                                                v___x_902_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25_once), _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__25);
                                                                v___x_903_ = l_Lean_mkAppB(
                                                                    v___x_902_, v_arg_879_,
                                                                    v_arg_876_,
                                                                );
                                                                v_val_827_ = v___x_901_;
                                                                v_h_u2081_828_ = v___x_903_;
                                                                v___y_829_ = v_a_818_;
                                                                v___y_830_ = v_a_819_;
                                                                v___y_831_ = v_a_820_;
                                                                v___y_832_ = v_a_821_;
                                                                state = 2;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_arg_879_);
                                                            lean_dec_ref(v_arg_876_);
                                                            lean_dec_ref(v_e_817_);
                                                            v_a_904_ = lean_ctor_get(v___x_894_, 0);
                                                            v_isSharedCheck_911_ =
                                                                (!lean_is_exclusive(v___x_894_))
                                                                    as u8;
                                                            if v_isSharedCheck_911_ == 0 {
                                                                v___x_906_ = v___x_894_;
                                                                v_isShared_907_ =
                                                                    v_isSharedCheck_911_;
                                                                state = 10;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_904_);
                                                                lean_dec(v___x_894_);
                                                                v___x_906_ = lean_box(0);
                                                                v_isShared_907_ =
                                                                    v_isSharedCheck_911_;
                                                                state = 10;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_885_);
                                                    v___x_912_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_884_, v_a_819_);
                                                    if lean_obj_tag(v___x_912_) == 0 {
                                                        v_a_913_ = lean_ctor_get(v___x_912_, 0);
                                                        lean_inc(v_a_913_);
                                                        lean_dec_ref_known(v___x_912_, 1);
                                                        v___x_914_ = l_Lean_Expr_cleanupAnnotations(
                                                            v_a_913_,
                                                        );
                                                        v___x_915_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21;
                                                        v___x_916_ = l_Lean_Expr_isConstOf(
                                                            v___x_914_, v___x_915_,
                                                        );
                                                        lean_dec_ref(v___x_914_);
                                                        if v___x_916_ == 0 {
                                                            lean_dec_ref(v_arg_879_);
                                                            lean_dec_ref(v_arg_876_);
                                                            lean_dec_ref(v_e_817_);
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_917_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22_once), _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__22);
                                                            lean_inc_ref(v_arg_879_);
                                                            v___x_918_ = l_Lean_mkNatAdd(
                                                                v_arg_879_, v___x_917_,
                                                            );
                                                            lean_inc_ref(v_arg_876_);
                                                            v___x_919_ = l_Lean_mkNatLE(
                                                                v___x_918_, v_arg_876_,
                                                            );
                                                            v___x_920_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28_once), _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__28);
                                                            v___x_921_ = l_Lean_mkAppB(
                                                                v___x_920_, v_arg_879_, v_arg_876_,
                                                            );
                                                            v_val_827_ = v___x_919_;
                                                            v_h_u2081_828_ = v___x_921_;
                                                            v___y_829_ = v_a_818_;
                                                            v___y_830_ = v_a_819_;
                                                            v___y_831_ = v_a_820_;
                                                            v___y_832_ = v_a_821_;
                                                            state = 2;
                                                            continue;
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_arg_879_);
                                                        lean_dec_ref(v_arg_876_);
                                                        lean_dec_ref(v_e_817_);
                                                        v_a_922_ = lean_ctor_get(v___x_912_, 0);
                                                        v_isSharedCheck_929_ =
                                                            (!lean_is_exclusive(v___x_912_)) as u8;
                                                        if v_isSharedCheck_929_ == 0 {
                                                            v___x_924_ = v___x_912_;
                                                            v_isShared_925_ = v_isSharedCheck_929_;
                                                            state = 12;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_922_);
                                                            lean_dec(v___x_912_);
                                                            v___x_924_ = lean_box(0);
                                                            v_isShared_925_ = v_isSharedCheck_929_;
                                                            state = 12;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_885_);
                                                v___x_930_ =
                                                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                        v_arg_884_, v_a_819_,
                                                    );
                                                if lean_obj_tag(v___x_930_) == 0 {
                                                    v_a_931_ = lean_ctor_get(v___x_930_, 0);
                                                    lean_inc(v_a_931_);
                                                    lean_dec_ref_known(v___x_930_, 1);
                                                    v___x_932_ =
                                                        l_Lean_Expr_cleanupAnnotations(v_a_931_);
                                                    v___x_933_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21;
                                                    v___x_934_ = l_Lean_Expr_isConstOf(
                                                        v___x_932_, v___x_933_,
                                                    );
                                                    lean_dec_ref(v___x_932_);
                                                    if v___x_934_ == 0 {
                                                        lean_dec_ref(v_arg_879_);
                                                        lean_dec_ref(v_arg_876_);
                                                        lean_dec_ref(v_e_817_);
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        lean_inc_ref(v_arg_879_);
                                                        lean_inc_ref(v_arg_876_);
                                                        v___x_935_ =
                                                            l_Lean_mkNatLE(v_arg_876_, v_arg_879_);
                                                        v___x_936_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31_once), _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__31);
                                                        v___x_937_ = l_Lean_mkAppB(
                                                            v___x_936_, v_arg_879_, v_arg_876_,
                                                        );
                                                        v_val_827_ = v___x_935_;
                                                        v_h_u2081_828_ = v___x_937_;
                                                        v___y_829_ = v_a_818_;
                                                        v___y_830_ = v_a_819_;
                                                        v___y_831_ = v_a_820_;
                                                        v___y_832_ = v_a_821_;
                                                        state = 2;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_arg_879_);
                                                    lean_dec_ref(v_arg_876_);
                                                    lean_dec_ref(v_e_817_);
                                                    v_a_938_ = lean_ctor_get(v___x_930_, 0);
                                                    v_isSharedCheck_945_ =
                                                        (!lean_is_exclusive(v___x_930_)) as u8;
                                                    if v_isSharedCheck_945_ == 0 {
                                                        v___x_940_ = v___x_930_;
                                                        v_isShared_941_ = v_isSharedCheck_945_;
                                                        state = 14;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_938_);
                                                        lean_dec(v___x_930_);
                                                        v___x_940_ = lean_box(0);
                                                        v_isShared_941_ = v_isSharedCheck_945_;
                                                        state = 14;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_885_);
                                            v___x_946_ =
                                                l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                                    v_arg_884_, v_a_819_,
                                                );
                                            if lean_obj_tag(v___x_946_) == 0 {
                                                v_a_947_ = lean_ctor_get(v___x_946_, 0);
                                                lean_inc(v_a_947_);
                                                lean_dec_ref_known(v___x_946_, 1);
                                                v___x_948_ =
                                                    l_Lean_Expr_cleanupAnnotations(v_a_947_);
                                                v___x_949_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__21;
                                                v___x_950_ =
                                                    l_Lean_Expr_isConstOf(v___x_948_, v___x_949_);
                                                lean_dec_ref(v___x_948_);
                                                if v___x_950_ == 0 {
                                                    lean_dec_ref(v_arg_879_);
                                                    lean_dec_ref(v_arg_876_);
                                                    lean_dec_ref(v_e_817_);
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_inc_ref(v_arg_876_);
                                                    lean_inc_ref(v_arg_879_);
                                                    v___x_951_ =
                                                        l_Lean_mkNatLE(v_arg_879_, v_arg_876_);
                                                    v___x_952_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34), core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34_once), _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__34);
                                                    v___x_953_ = l_Lean_mkAppB(
                                                        v___x_952_, v_arg_879_, v_arg_876_,
                                                    );
                                                    v_val_827_ = v___x_951_;
                                                    v_h_u2081_828_ = v___x_953_;
                                                    v___y_829_ = v_a_818_;
                                                    v___y_830_ = v_a_819_;
                                                    v___y_831_ = v_a_820_;
                                                    v___y_832_ = v_a_821_;
                                                    state = 2;
                                                    continue;
                                                }
                                            } else {
                                                lean_dec_ref(v_arg_879_);
                                                lean_dec_ref(v_arg_876_);
                                                lean_dec_ref(v_e_817_);
                                                v_a_954_ = lean_ctor_get(v___x_946_, 0);
                                                v_isSharedCheck_961_ =
                                                    (!lean_is_exclusive(v___x_946_)) as u8;
                                                if v_isSharedCheck_961_ == 0 {
                                                    v___x_956_ = v___x_946_;
                                                    v_isShared_957_ = v_isSharedCheck_961_;
                                                    state = 16;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_954_);
                                                    lean_dec(v___x_946_);
                                                    v___x_956_ = lean_box(0);
                                                    v_isShared_957_ = v_isSharedCheck_961_;
                                                    state = 16;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_817_);
                        v_a_962_ = lean_ctor_get(v___x_872_, 0);
                        v_isSharedCheck_969_ = (!lean_is_exclusive(v___x_872_)) as u8;
                        if v_isSharedCheck_969_ == 0 {
                            v___x_964_ = v___x_872_;
                            v_isShared_965_ = v_isSharedCheck_969_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_962_);
                            lean_dec(v___x_872_);
                            v___x_964_ = lean_box(0);
                            v_isShared_965_ = v_isSharedCheck_969_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_824_ = lean_box(0);
                v___x_825_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_825_, 0, v___x_824_);
                return v___x_825_;
            }
            2 => {
                lean_inc_ref(v_val_827_);
                v___x_833_ = l_Lean_Meta_Simp_Arith_Nat_simpCnstrPos_x3f(
                    v_val_827_, v___y_829_, v___y_830_, v___y_831_, v___y_832_,
                );
                if lean_obj_tag(v___x_833_) == 0 {
                    v_a_834_ = lean_ctor_get(v___x_833_, 0);
                    v_isSharedCheck_866_ = (!lean_is_exclusive(v___x_833_)) as u8;
                    if v_isSharedCheck_866_ == 0 {
                        v___x_836_ = v___x_833_;
                        v_isShared_837_ = v_isSharedCheck_866_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_834_);
                        lean_dec(v___x_833_);
                        v___x_836_ = lean_box(0);
                        v_isShared_837_ = v_isSharedCheck_866_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_h_u2081_828_);
                    lean_dec_ref(v_val_827_);
                    lean_dec_ref(v_e_817_);
                    return v___x_833_;
                }
            }
            3 => {
                if lean_obj_tag(v_a_834_) == 1 {
                    v_val_838_ = lean_ctor_get(v_a_834_, 0);
                    v_isSharedCheck_860_ = (!lean_is_exclusive(v_a_834_)) as u8;
                    if v_isSharedCheck_860_ == 0 {
                        v___x_840_ = v_a_834_;
                        v_isShared_841_ = v_isSharedCheck_860_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_838_);
                        lean_dec(v_a_834_);
                        v___x_840_ = lean_box(0);
                        v_isShared_841_ = v_isSharedCheck_860_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_a_834_);
                    lean_dec_ref(v_e_817_);
                    v___x_861_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_861_, 0, v_val_827_);
                    lean_ctor_set(v___x_861_, 1, v_h_u2081_828_);
                    v___x_862_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_862_, 0, v___x_861_);
                    if v_isShared_837_ == 0 {
                        lean_ctor_set(v___x_836_, 0, v___x_862_);
                        v___x_864_ = v___x_836_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
                        v___x_864_ = v_reuseFailAlloc_865_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v_fst_842_ = lean_ctor_get(v_val_838_, 0);
                v_snd_843_ = lean_ctor_get(v_val_838_, 1);
                v_isSharedCheck_859_ = (!lean_is_exclusive(v_val_838_)) as u8;
                if v_isSharedCheck_859_ == 0 {
                    v___x_845_ = v_val_838_;
                    v_isShared_846_ = v_isSharedCheck_859_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_snd_843_);
                    lean_inc(v_fst_842_);
                    lean_dec(v_val_838_);
                    v___x_845_ = lean_box(0);
                    v_isShared_846_ = v_isSharedCheck_859_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_847_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__5,
                );
                v___x_848_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___closed__6,
                );
                lean_inc(v_fst_842_);
                v___x_849_ = l_Lean_mkApp6(
                    v___x_847_,
                    v___x_848_,
                    v_e_817_,
                    v_val_827_,
                    v_fst_842_,
                    v_h_u2081_828_,
                    v_snd_843_,
                );
                if v_isShared_846_ == 0 {
                    lean_ctor_set(v___x_845_, 1, v___x_849_);
                    v___x_851_ = v___x_845_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_858_, 0, v_fst_842_);
                    lean_ctor_set(v_reuseFailAlloc_858_, 1, v___x_849_);
                    v___x_851_ = v_reuseFailAlloc_858_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_841_ == 0 {
                    lean_ctor_set(v___x_840_, 0, v___x_851_);
                    v___x_853_ = v___x_840_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_857_, 0, v___x_851_);
                    v___x_853_ = v_reuseFailAlloc_857_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_837_ == 0 {
                    lean_ctor_set(v___x_836_, 0, v___x_853_);
                    v___x_855_ = v___x_836_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_853_);
                    v___x_855_ = v_reuseFailAlloc_856_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_855_;
            }
            9 => {
                return v___x_864_;
            }
            10 => {
                if v_isShared_907_ == 0 {
                    v___x_909_ = v___x_906_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
                    v___x_909_ = v_reuseFailAlloc_910_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_909_;
            }
            12 => {
                if v_isShared_925_ == 0 {
                    v___x_927_ = v___x_924_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
                    v___x_927_ = v_reuseFailAlloc_928_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_927_;
            }
            14 => {
                if v_isShared_941_ == 0 {
                    v___x_943_ = v___x_940_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
                    v___x_943_ = v_reuseFailAlloc_944_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_943_;
            }
            16 => {
                if v_isShared_957_ == 0 {
                    v___x_959_ = v___x_956_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
                    v___x_959_ = v_reuseFailAlloc_960_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_959_;
            }
            18 => {
                if v_isShared_965_ == 0 {
                    v___x_967_ = v___x_964_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
                    v___x_967_ = v_reuseFailAlloc_968_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f___boxed(
    mut v_e_970_: *mut LeanObject,
    mut v_a_971_: *mut LeanObject,
    mut v_a_972_: *mut LeanObject,
    mut v_a_973_: *mut LeanObject,
    mut v_a_974_: *mut LeanObject,
    mut v_a_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_976_: *mut LeanObject = core::ptr::null_mut();
    v_res_976_ =
        l_Lean_Meta_Simp_Arith_Nat_simpCnstr_x3f(v_e_970_, v_a_971_, v_a_972_, v_a_973_, v_a_974_);
    lean_dec(v_a_974_);
    lean_dec_ref(v_a_973_);
    lean_dec(v_a_972_);
    lean_dec_ref(v_a_971_);
    return v_res_976_;
}
pub unsafe fn _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2() -> *mut LeanObject {
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    v___x_983_ = lean_box(0);
    v___x_984_ = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__1;
    v___x_985_ = l_Lean_mkConst(v___x_984_, v___x_983_);
    return v___x_985_;
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(
    mut v_input_986_: *mut LeanObject,
    mut v_a_987_: *mut LeanObject,
    mut v_a_988_: *mut LeanObject,
    mut v_a_989_: *mut LeanObject,
    mut v_a_990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_996_: u8 = 0;
    let mut v_fst_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1001_: u8 = 0;
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: u8 = 0;
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1016_: u8 = 0;
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1029_: u8 = 0;
    let mut v_a_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1033_: u8 = 0;
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1037_: u8 = 0;
    let mut v_a_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1041_: u8 = 0;
    let mut v___x_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1045_: u8 = 0;
    let mut v_a_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1049_: u8 = 0;
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1053_: u8 = 0;
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1058_: u8 = 0;
    let mut v_isSharedCheck_1059_: u8 = 0;
    let mut v_a_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1063_: u8 = 0;
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1067_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_992_ = l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(
                    v_input_986_,
                    v_a_987_,
                    v_a_988_,
                    v_a_989_,
                    v_a_990_,
                );
                if lean_obj_tag(v___x_992_) == 0 {
                    v_a_993_ = lean_ctor_get(v___x_992_, 0);
                    v_isSharedCheck_1059_ = (!lean_is_exclusive(v___x_992_)) as u8;
                    if v_isSharedCheck_1059_ == 0 {
                        v___x_995_ = v___x_992_;
                        v_isShared_996_ = v_isSharedCheck_1059_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_993_);
                        lean_dec(v___x_992_);
                        v___x_995_ = lean_box(0);
                        v_isShared_996_ = v_isSharedCheck_1059_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1060_ = lean_ctor_get(v___x_992_, 0);
                    v_isSharedCheck_1067_ = (!lean_is_exclusive(v___x_992_)) as u8;
                    if v_isSharedCheck_1067_ == 0 {
                        v___x_1062_ = v___x_992_;
                        v_isShared_1063_ = v_isSharedCheck_1067_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_1060_);
                        lean_dec(v___x_992_);
                        v___x_1062_ = lean_box(0);
                        v_isShared_1063_ = v_isSharedCheck_1067_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_997_ = lean_ctor_get(v_a_993_, 0);
                v_snd_998_ = lean_ctor_get(v_a_993_, 1);
                v_isSharedCheck_1058_ = (!lean_is_exclusive(v_a_993_)) as u8;
                if v_isSharedCheck_1058_ == 0 {
                    v___x_1000_ = v_a_993_;
                    v_isShared_1001_ = v_isSharedCheck_1058_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_998_);
                    lean_inc(v_fst_997_);
                    lean_dec(v_a_993_);
                    v___x_1000_ = lean_box(0);
                    v_isShared_1001_ = v_isSharedCheck_1058_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1002_ = l_Nat_Linear_Expr_toPoly(v_fst_997_);
                v___x_1003_ = l_Nat_Linear_Poly_norm(v___x_1002_);
                v___x_1004_ = l_Nat_Linear_Poly_toExpr(v___x_1003_);
                v___x_1005_ = l_Nat_Linear_instBEqExpr_beq(v___x_1004_, v_fst_997_);
                if v___x_1005_ == 0 {
                    lean_del_object(v___x_995_);
                    lean_inc(v_snd_998_);
                    v___x_1006_ = l_Lean_Meta_Simp_Arith_Nat_toContextExpr(
                        v_snd_998_, v_a_987_, v_a_988_, v_a_989_, v_a_990_,
                    );
                    if lean_obj_tag(v___x_1006_) == 0 {
                        v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
                        lean_inc(v_a_1007_);
                        lean_dec_ref_known(v___x_1006_, 1);
                        lean_inc(v_fst_997_);
                        v___x_1008_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v_fst_997_);
                        v___x_1009_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                            v_snd_998_, v_fst_997_,
                        );
                        if lean_obj_tag(v___x_1009_) == 0 {
                            v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
                            lean_inc(v_a_1010_);
                            lean_dec_ref_known(v___x_1009_, 1);
                            lean_inc_ref(v___x_1004_);
                            v___x_1011_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(v___x_1004_);
                            v___x_1012_ = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(
                                v_snd_998_,
                                v___x_1004_,
                            );
                            lean_dec(v_snd_998_);
                            if lean_obj_tag(v___x_1012_) == 0 {
                                v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
                                v_isSharedCheck_1029_ = (!lean_is_exclusive(v___x_1012_)) as u8;
                                if v_isSharedCheck_1029_ == 0 {
                                    v___x_1015_ = v___x_1012_;
                                    v_isShared_1016_ = v_isSharedCheck_1029_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_1013_);
                                    lean_dec(v___x_1012_);
                                    v___x_1015_ = lean_box(0);
                                    v_isShared_1016_ = v_isSharedCheck_1029_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v___x_1011_);
                                lean_dec(v_a_1010_);
                                lean_dec_ref(v___x_1008_);
                                lean_dec(v_a_1007_);
                                lean_del_object(v___x_1000_);
                                v_a_1030_ = lean_ctor_get(v___x_1012_, 0);
                                v_isSharedCheck_1037_ = (!lean_is_exclusive(v___x_1012_)) as u8;
                                if v_isSharedCheck_1037_ == 0 {
                                    v___x_1032_ = v___x_1012_;
                                    v_isShared_1033_ = v_isSharedCheck_1037_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_1030_);
                                    lean_dec(v___x_1012_);
                                    v___x_1032_ = lean_box(0);
                                    v_isShared_1033_ = v_isSharedCheck_1037_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_1008_);
                            lean_dec(v_a_1007_);
                            lean_dec_ref(v___x_1004_);
                            lean_del_object(v___x_1000_);
                            lean_dec(v_snd_998_);
                            v_a_1038_ = lean_ctor_get(v___x_1009_, 0);
                            v_isSharedCheck_1045_ = (!lean_is_exclusive(v___x_1009_)) as u8;
                            if v_isSharedCheck_1045_ == 0 {
                                v___x_1040_ = v___x_1009_;
                                v_isShared_1041_ = v_isSharedCheck_1045_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_1038_);
                                lean_dec(v___x_1009_);
                                v___x_1040_ = lean_box(0);
                                v_isShared_1041_ = v_isSharedCheck_1045_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_1004_);
                        lean_del_object(v___x_1000_);
                        lean_dec(v_snd_998_);
                        lean_dec(v_fst_997_);
                        v_a_1046_ = lean_ctor_get(v___x_1006_, 0);
                        v_isSharedCheck_1053_ = (!lean_is_exclusive(v___x_1006_)) as u8;
                        if v_isSharedCheck_1053_ == 0 {
                            v___x_1048_ = v___x_1006_;
                            v_isShared_1049_ = v_isSharedCheck_1053_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1046_);
                            lean_dec(v___x_1006_);
                            v___x_1048_ = lean_box(0);
                            v_isShared_1049_ = v_isSharedCheck_1053_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1004_);
                    lean_del_object(v___x_1000_);
                    lean_dec(v_snd_998_);
                    lean_dec(v_fst_997_);
                    v___x_1054_ = lean_box(0);
                    if v_isShared_996_ == 0 {
                        lean_ctor_set(v___x_995_, 0, v___x_1054_);
                        v___x_1056_ = v___x_995_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
                        v___x_1056_ = v_reuseFailAlloc_1057_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1017_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2_once
                    ),
                    _init_l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___closed__2,
                );
                v___x_1018_ = l_Lean_eagerReflBoolTrue;
                v___x_1019_ = l_Lean_mkApp4(
                    v___x_1017_,
                    v_a_1007_,
                    v___x_1008_,
                    v___x_1011_,
                    v___x_1018_,
                );
                lean_inc(v_a_1013_);
                v___x_1020_ = l_Lean_mkNatEq(v_a_1010_, v_a_1013_);
                v___x_1021_ = l_Lean_Meta_mkExpectedPropHint(v___x_1019_, v___x_1020_);
                if v_isShared_1001_ == 0 {
                    lean_ctor_set(v___x_1000_, 1, v___x_1021_);
                    lean_ctor_set(v___x_1000_, 0, v_a_1013_);
                    v___x_1023_ = v___x_1000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1013_);
                    lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_1021_);
                    v___x_1023_ = v_reuseFailAlloc_1028_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1024_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1024_, 0, v___x_1023_);
                if v_isShared_1016_ == 0 {
                    lean_ctor_set(v___x_1015_, 0, v___x_1024_);
                    v___x_1026_ = v___x_1015_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
                    v___x_1026_ = v_reuseFailAlloc_1027_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1026_;
            }
            6 => {
                if v_isShared_1033_ == 0 {
                    v___x_1035_ = v___x_1032_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
                    v___x_1035_ = v_reuseFailAlloc_1036_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1035_;
            }
            8 => {
                if v_isShared_1041_ == 0 {
                    v___x_1043_ = v___x_1040_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
                    v___x_1043_ = v_reuseFailAlloc_1044_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1043_;
            }
            10 => {
                if v_isShared_1049_ == 0 {
                    v___x_1051_ = v___x_1048_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
                    v___x_1051_ = v_reuseFailAlloc_1052_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1051_;
            }
            12 => {
                return v___x_1056_;
            }
            13 => {
                if v_isShared_1063_ == 0 {
                    v___x_1065_ = v___x_1062_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
                    v___x_1065_ = v_reuseFailAlloc_1066_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f___boxed(
    mut v_input_1068_: *mut LeanObject,
    mut v_a_1069_: *mut LeanObject,
    mut v_a_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1074_: *mut LeanObject = core::ptr::null_mut();
    v_res_1074_ = l_Lean_Meta_Simp_Arith_Nat_simpExpr_x3f(
        v_input_1068_,
        v_a_1069_,
        v_a_1070_,
        v_a_1071_,
        v_a_1072_,
    );
    lean_dec(v_a_1072_);
    lean_dec_ref(v_a_1071_);
    lean_dec(v_a_1070_);
    lean_dec_ref(v_a_1069_);
    return v_res_1074_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Simp(builtin);
}
