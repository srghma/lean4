/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Full Rust implementation of library/expr_lt.cpp extern "C" functions:
  lean_expr_quick_lt  — is_lt(a, b, use_hash=true,  lctx=nullptr)
  lean_expr_lt        — is_lt(a, b, use_hash=false, lctx=nullptr)

Algorithm mirrors C++ is_lt(expr, expr, bool use_hash):
  - Pointer equality → false (not lt)
  - Kind (tag) mismatch → tag_a < tag_b
  - If use_hash: compare hashes (bits[31:0] of Expr.Data); return early on mismatch
  - Structural equality (lean_expr_eqv) → false
  - Per-kind: field-by-field comparison using total orders on sub-types

IMPORTANT: All sub-field inequality checks mirror C++ operator!= on expr/level/name, which
are STRUCTURAL (not pointer) equality checks. In C++, expr::operator!= calls is_equal (=
expr_eq_fn<false>), level::operator!= calls the level structural equality, and name::operator!=
calls name::eq which is structural. We mirror this using lean_expr_eqv, lean_level_eqv, and
lean_name_eq respectively.

Name ordering: C++ uses name::operator< which calls cmp_core (lexicographic, root-to-leaf),
NOT hash-based. Lean's l_Lean_Name_lt is equivalent to this lexicographic ordering.
Do NOT use l_Lean_Name_quickLt (hash-based) as it produces a different ordering.

Level.Data layout (from kernel_level.rs lean_level_mk_data):
  bits[31:0]  = hash
  bit[32]     = hasMVar
  bit[33]     = hasParam
  bits[63:40] = depth

Level kind tags:
  Zero   = scalar (lean_box(0), treated as tag 0 when scalar)
  Succ   = 1, field[0] = inner level
  Max    = 2, fields[0,1] = lhs, rhs
  IMax   = 3, fields[0,1] = lhs, rhs
  Param  = 4, field[0] = Name
  MVar   = 5, field[0] = LevelMVarId (Name)

Expr kind tags (same as kernel_expr_eq_fn):
  BVar=0  FVar=1  MVar=2  Sort=3  Const=4  App=5
  Lambda=6  Pi=7  Let=8  Lit=9  MData=10  Proj=11

DataValue kind tags (data_value_kind enum):
  String=0  Bool=1  Name=2  Nat=3

KVMap = list_ref<pair_ref<name, data_value>>, field layout same as kvmap_eq in expr_eq_fn.rs:
  list nil  = lean_is_scalar(ptr)
  list cons = ctor(tag=1), field[0]=pair, field[1]=tail
  pair      = ctor, field[0]=name, field[1]=data_value

DataValue Bool (tag=1): 0 ptr fields, 1 uint8 scalar (the bool value at byte offset 0).
*/

#[cfg(feature = "export-runtime-ffi")]
mod library_expr_lt_impl {
    use super::runtime_object_name_impl::lean_name_eq;
    use super::*;

    extern "C" {
        fn lean_level_eqv(l1: *mut LeanObject, l2: *mut LeanObject) -> u8;
        fn lean_expr_eqv(a: *mut LeanObject, b: *mut LeanObject) -> u8;
        fn lean_nat_big_lt(a: *mut LeanObject, b: *mut LeanObject) -> bool;
        fn lean_nat_big_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool;
        fn lean_string_lt(s1: *mut LeanObject, s2: *mut LeanObject) -> bool;
        fn lean_string_eq_cold(s1: *mut LeanObject, s2: *mut LeanObject) -> bool;
        // Borrowed — does not consume arguments.
        // Mirrors C++ name::operator< which uses cmp_core (lexicographic, root-to-leaf, NOT hash-based).
        fn l_Lean_Name_lt(n1: *mut LeanObject, n2: *mut LeanObject) -> u8;
    }

    // ── Expr field layout helpers ─────────────────────────────────────────────

    const EXPR_BVAR: u8 = 0;
    const EXPR_FVAR: u8 = 1;
    const EXPR_MVAR: u8 = 2;
    const EXPR_SORT: u8 = 3;
    const EXPR_CONST: u8 = 4;
    const EXPR_APP: u8 = 5;
    const EXPR_LAMBDA: u8 = 6;
    const EXPR_PI: u8 = 7;
    const EXPR_LET: u8 = 8;
    const EXPR_LIT: u8 = 9;
    const EXPR_MDATA: u8 = 10;
    const EXPR_PROJ: u8 = 11;

    #[inline(always)]
    unsafe fn expr_hash(e: *mut LeanObject) -> u32 {
        let num_objs = (*e).other as usize;
        lean_ctor_get_uint64(e, num_objs * core::mem::size_of::<*mut LeanObject>()) as u32
    }

    #[inline(always)]
    unsafe fn expr_let_nondep(e: *mut LeanObject) -> u8 {
        lean_ctor_get_uint8(e, 4 * core::mem::size_of::<*mut LeanObject>() + 8)
    }

    // ── Level helpers ─────────────────────────────────────────────────────────

    const LEVEL_SUCC: u8 = 1;
    const LEVEL_MAX: u8 = 2;
    const LEVEL_IMAX: u8 = 3;
    const LEVEL_PARAM: u8 = 4;
    const LEVEL_MVAR: u8 = 5;

    #[inline(always)]
    unsafe fn level_data(l: *mut LeanObject) -> u64 {
        debug_assert!(!lean_is_scalar(l));
        let num_objs = (*l).other as usize;
        lean_ctor_get_uint64(l, num_objs * core::mem::size_of::<*mut LeanObject>())
    }

    #[inline(always)]
    unsafe fn level_hash(l: *mut LeanObject) -> u32 {
        if lean_is_scalar(l) {
            return 0;
        }
        level_data(l) as u32
    }

    // Depth occupies bits[63:40] of the Level.Data u64.
    const LEVEL_DATA_DEPTH_SHIFT: u32 = 40;

    #[inline(always)]
    unsafe fn level_depth(l: *mut LeanObject) -> u32 {
        if lean_is_scalar(l) {
            return 0;
        }
        (level_data(l) >> LEVEL_DATA_DEPTH_SHIFT) as u32
    }

    // Total order on Level objects. Mirrors C++ is_lt(level, level, use_hash).
    // Sub-field inequality checks use lean_level_eqv (structural), matching C++ level::operator!=.
    unsafe fn level_lt(a: *mut LeanObject, b: *mut LeanObject, use_hash: bool) -> bool {
        if a == b {
            return false;
        }
        let da = level_depth(a);
        let db = level_depth(b);
        if da < db {
            return true;
        }
        if da > db {
            return false;
        }
        let tag_a = lean_obj_tag(a);
        let tag_b = lean_obj_tag(b);
        if tag_a != tag_b {
            return tag_a < tag_b;
        }
        if use_hash {
            let ha = level_hash(a);
            let hb = level_hash(b);
            if ha < hb {
                return true;
            }
            if ha > hb {
                return false;
            }
        }
        if lean_level_eqv(a, b) != 0 {
            return false;
        }
        match tag_a {
            LEVEL_PARAM | LEVEL_MVAR => {
                l_Lean_Name_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
            }
            LEVEL_MAX | LEVEL_IMAX => {
                let lhs_a = lean_ctor_get(a, 0);
                let lhs_b = lean_ctor_get(b, 0);
                // C++ uses level_lhs(a) != level_lhs(b) which is level::operator!= (structural).
                if lean_level_eqv(lhs_a, lhs_b) == 0 {
                    return level_lt(lhs_a, lhs_b, use_hash);
                }
                level_lt(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_hash)
            }
            LEVEL_SUCC => level_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0), use_hash),
            _ => false,
        }
    }

    // Mirrors C++ is_lt(levels, levels, use_hash).
    // C++ uses car(as) == car(bs) which is level::operator== (structural).
    unsafe fn levels_lt(
        mut as_: *mut LeanObject,
        mut bs_: *mut LeanObject,
        use_hash: bool,
    ) -> bool {
        loop {
            let sa = lean_is_scalar(as_);
            let sb = lean_is_scalar(bs_);
            if sa {
                return !sb;
            } // nil < cons
            if sb {
                return false;
            }
            let head_a = lean_ctor_get(as_, 0);
            let head_b = lean_ctor_get(bs_, 0);
            // Use structural equality to match C++ car(as) == car(bs) (level::operator==).
            if lean_level_eqv(head_a, head_b) == 0 {
                return level_lt(head_a, head_b, use_hash);
            }
            as_ = lean_ctor_get(as_, 1);
            bs_ = lean_ctor_get(bs_, 1);
        }
    }

    // ── Nat helpers ───────────────────────────────────────────────────────────

    // Borrowed Nat comparison; mirrors lean_nat_lt from lean.h.
    #[inline(always)]
    unsafe fn nat_lt(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if lean_is_scalar(a) && lean_is_scalar(b) {
            return (a as usize) < (b as usize);
        }
        lean_nat_big_lt(a, b)
    }

    // Borrowed Nat equality check.
    #[inline(always)]
    unsafe fn nat_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if a == b {
            return true;
        }
        if lean_is_scalar(a) || lean_is_scalar(b) {
            return false;
        }
        lean_nat_big_eq(a, b)
    }

    // ── DataValue helpers ─────────────────────────────────────────────────────

    const DV_STRING: u8 = 0;
    const DV_BOOL: u8 = 1;
    const DV_NAME: u8 = 2;
    const DV_NAT: u8 = 3;

    // String equality (borrowed).
    #[inline(always)]
    unsafe fn string_size(s: *mut LeanObject) -> usize {
        *((s as *const u8).add(8) as *const usize)
    }

    #[inline(always)]
    unsafe fn str_eq(s1: *mut LeanObject, s2: *mut LeanObject) -> bool {
        s1 == s2 || (string_size(s1) == string_size(s2) && lean_string_eq_cold(s1, s2))
    }

    // Borrowed DataValue equality — avoids the consuming lean_data_value_beq.
    unsafe fn data_value_eq(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if a == b {
            return true;
        }
        let tag_a = lean_obj_tag(a);
        if tag_a != lean_obj_tag(b) {
            return false;
        }
        match tag_a {
            DV_STRING => str_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            DV_BOOL => lean_ctor_get_uint8(a, 0) == lean_ctor_get_uint8(b, 0),
            DV_NAME => lean_name_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0,
            DV_NAT => nat_eq(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            _ => false,
        }
    }

    // DataValue ordering. Mirrors C++ data_value::operator< from kvmap.h.
    // C++ uses name::operator< (lexicographic) for DV_NAME, so we use l_Lean_Name_lt.
    unsafe fn data_value_lt(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if a == b {
            return false;
        }
        let tag_a = lean_obj_tag(a);
        let tag_b = lean_obj_tag(b);
        if tag_a != tag_b {
            return tag_a < tag_b;
        }
        match tag_a {
            DV_STRING => lean_string_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            DV_BOOL => {
                // false < true: a.bool == 0 && b.bool != 0
                lean_ctor_get_uint8(a, 0) == 0 && lean_ctor_get_uint8(b, 0) != 0
            }
            DV_NAME => l_Lean_Name_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0,
            DV_NAT => nat_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            _ => false,
        }
    }

    // ── KVMap ordering ────────────────────────────────────────────────────────

    // Mirrors C++ list_ref<pair_ref<name,data_value>>::operator<  (lexicographic).
    // Borrowed: does not consume m1 or m2.
    unsafe fn kvmap_lt(mut m1: *mut LeanObject, mut m2: *mut LeanObject) -> bool {
        loop {
            if m1 == m2 {
                return false;
            }
            let s1 = lean_is_scalar(m1);
            let s2 = lean_is_scalar(m2);
            if s1 {
                return !s2;
            } // nil < cons
            if s2 {
                return false;
            }

            // cons cell: field[0]=pair, field[1]=tail
            let pair1 = lean_ctor_get(m1, 0);
            let pair2 = lean_ctor_get(m2, 0);
            if pair1 != pair2 {
                // pair: field[0]=name, field[1]=data_value
                let name1 = lean_ctor_get(pair1, 0);
                let name2 = lean_ctor_get(pair2, 0);
                if lean_name_eq(name1, name2) == 0 {
                    return l_Lean_Name_lt(name1, name2) != 0;
                }
                // Names equal: compare data_values.
                let dv1 = lean_ctor_get(pair1, 1);
                let dv2 = lean_ctor_get(pair2, 1);
                if !data_value_eq(dv1, dv2) {
                    return data_value_lt(dv1, dv2);
                }
                // Pair elements equal: continue to next list node.
            }

            m1 = lean_ctor_get(m1, 1);
            m2 = lean_ctor_get(m2, 1);
        }
    }

    // ── Literal ordering ─────────────────────────────────────────────────────

    // Literal.natVal = tag 0, field[0] = Nat
    // Literal.strVal = tag 1, field[0] = String
    unsafe fn lit_lt(a: *mut LeanObject, b: *mut LeanObject) -> bool {
        if a == b {
            return false;
        }
        let tag_a = lean_obj_tag(a);
        let tag_b = lean_obj_tag(b);
        if tag_a != tag_b {
            return tag_a < tag_b;
        }
        match tag_a {
            0 => nat_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            1 => lean_string_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),
            _ => false,
        }
    }

    // ── Main expression ordering ──────────────────────────────────────────────

    // Mirrors C++ is_lt(expr, expr, use_hash, lctx=nullptr).
    // Borrowed: does not consume a or b.
    //
    // Sub-field inequality checks mirror C++, which uses expr::operator!= (= is_equal =
    // expr_eq_fn<false> = lean_expr_eqv) for sub-exprs, level::operator!= (= lean_level_eqv)
    // for sub-levels, and name::operator!= (= lean_name_eq) for sub-names.
    unsafe fn expr_lt(a: *mut LeanObject, b: *mut LeanObject, use_hash: bool) -> bool {
        if a == b {
            return false;
        }

        let tag_a = lean_obj_tag(a);
        let tag_b = lean_obj_tag(b);
        if tag_a != tag_b {
            return tag_a < tag_b;
        }

        if use_hash {
            let ha = expr_hash(a);
            let hb = expr_hash(b);
            if ha < hb {
                return true;
            }
            if ha > hb {
                return false;
            }
        }

        // Structural equality fast-exit: mirrors C++ "if (a == b) return false;" which calls
        // expr_eq_fn<false>. Needed because sub-field comparisons below use structural equality.
        if lean_expr_eqv(a, b) != 0 {
            return false;
        }

        match tag_a {
            EXPR_LIT => lit_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),

            EXPR_BVAR => nat_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0)),

            EXPR_MDATA => {
                // field[0]=KVMap, field[1]=expr
                // C++: if (mdata_expr(a) != mdata_expr(b)) — structural expr inequality
                let inner_a = lean_ctor_get(a, 1);
                let inner_b = lean_ctor_get(b, 1);
                if lean_expr_eqv(inner_a, inner_b) == 0 {
                    return expr_lt(inner_a, inner_b, use_hash);
                }
                kvmap_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0))
            }

            EXPR_PROJ => {
                // field[0]=sname(Name), field[1]=idx(Nat), field[2]=expr
                // C++: if (proj_expr(a) != proj_expr(b)) — structural expr inequality
                let expr_a = lean_ctor_get(a, 2);
                let expr_b = lean_ctor_get(b, 2);
                if lean_expr_eqv(expr_a, expr_b) == 0 {
                    return expr_lt(expr_a, expr_b, use_hash);
                }
                let sname_a = lean_ctor_get(a, 0);
                let sname_b = lean_ctor_get(b, 0);
                if lean_name_eq(sname_a, sname_b) == 0 {
                    return l_Lean_Name_lt(sname_a, sname_b) != 0;
                }
                nat_lt(lean_ctor_get(a, 1), lean_ctor_get(b, 1))
            }

            EXPR_CONST => {
                // field[0]=name, field[1]=List Level
                // C++: if (const_name(a) != const_name(b)) — structural name inequality
                let name_a = lean_ctor_get(a, 0);
                let name_b = lean_ctor_get(b, 0);
                if lean_name_eq(name_a, name_b) == 0 {
                    return l_Lean_Name_lt(name_a, name_b) != 0;
                }
                levels_lt(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_hash)
            }

            EXPR_APP => {
                // field[0]=fn, field[1]=arg
                // C++: if (app_fn(a) != app_fn(b)) — structural expr inequality
                let fn_a = lean_ctor_get(a, 0);
                let fn_b = lean_ctor_get(b, 0);
                if lean_expr_eqv(fn_a, fn_b) == 0 {
                    return expr_lt(fn_a, fn_b, use_hash);
                }
                expr_lt(lean_ctor_get(a, 1), lean_ctor_get(b, 1), use_hash)
            }

            EXPR_LAMBDA | EXPR_PI => {
                // field[0]=name, field[1]=domain, field[2]=body
                // C++: if (binding_domain(a) != binding_domain(b)) — structural expr inequality
                let dom_a = lean_ctor_get(a, 1);
                let dom_b = lean_ctor_get(b, 1);
                if lean_expr_eqv(dom_a, dom_b) == 0 {
                    return expr_lt(dom_a, dom_b, use_hash);
                }
                expr_lt(lean_ctor_get(a, 2), lean_ctor_get(b, 2), use_hash)
            }

            EXPR_LET => {
                // field[0]=name, field[1]=type, field[2]=value, field[3]=body; scalar: nondep
                // C++: if (let_nondep(a) != let_nondep(b)) — scalar comparison
                let nd_a = expr_let_nondep(a);
                let nd_b = expr_let_nondep(b);
                if nd_a != nd_b {
                    return nd_a < nd_b;
                }
                // C++: else if (let_type(a) != let_type(b)) — structural expr inequality
                let type_a = lean_ctor_get(a, 1);
                let type_b = lean_ctor_get(b, 1);
                if lean_expr_eqv(type_a, type_b) == 0 {
                    return expr_lt(type_a, type_b, use_hash);
                }
                // C++: else if (let_value(a) != let_value(b)) — structural expr inequality
                let val_a = lean_ctor_get(a, 2);
                let val_b = lean_ctor_get(b, 2);
                if lean_expr_eqv(val_a, val_b) == 0 {
                    return expr_lt(val_a, val_b, use_hash);
                }
                expr_lt(lean_ctor_get(a, 3), lean_ctor_get(b, 3), use_hash)
            }

            EXPR_SORT => {
                // field[0] = Level
                level_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0), use_hash)
            }

            EXPR_FVAR | EXPR_MVAR => {
                // field[0] = Name (FVar name or MVar name); no lctx, so use name ordering.
                // C++ uses fvar_name(a) < fvar_name(b) which is name::operator< (lexicographic).
                l_Lean_Name_lt(lean_ctor_get(a, 0), lean_ctor_get(b, 0)) != 0
            }

            _ => false,
        }
    }

    #[no_mangle]
    pub unsafe fn lean_expr_quick_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
        expr_lt(a, b, true) as u8
    }

    #[no_mangle]
    pub unsafe fn lean_expr_lt(a: *mut LeanObject, b: *mut LeanObject) -> u8 {
        expr_lt(a, b, false) as u8
    }
}
