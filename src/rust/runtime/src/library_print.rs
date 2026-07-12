/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Rust port of library/print.cpp.

Provides lean_expr_dbg_to_string, which is the ToString Expr instance in Lean
(registered via @[extern "lean_expr_dbg_to_string"] on Expr.dbgToString).

initialize_print / finalize_print are now no-ops exported with their original
C++ mangled names so that any code compiled against the old ABI still links.
init_default_print_fn is also a no-op: the C++ formatter.h print function
pointer is no longer needed because lean_expr_dbg_to_string is implemented
entirely in Rust.
*/
pub fn initialize_print() {}
pub fn finalize_print() {}

mod library_print_impl {
    use crate::runtime_expr_shared::{
        DV_BOOL, DV_NAME, DV_NAT, DV_STRING, LeanBinderInfo, LeanDataValueKind, LeanExprKind,
        LeanLevelKind, LeanLiteralTag, LeanNameTag, expr_binder_info_raw, expr_bvar_range,
        expr_kind, expr_let_nondep, lean_data_value_kind, lean_literal_tag, lean_name_tag,
        level_kind,
    };
    use crate::*;
    use core::ffi::{CStr, c_char, c_int, c_long, c_uchar, c_uint, c_void};

    unsafe extern "C" {
        // Lean-compiled (Lean.Expr): mkFVar — takes owned FVarId (= Name at ABI), returns owned Expr.
        fn lean_expr_mk_fvar(n: *mut LeanObject) -> *mut LeanObject;
        // lean_expr_instantiate1 is provided by kernel_instantiate.rs.
        fn lean_expr_instantiate1(a: *mut LeanObject, e: *mut LeanObject) -> *mut LeanObject;
        // Lean-compiled (Init.Data.Repr): takes owned Nat, returns owned String.
        fn l_Nat_reprFast(n: *mut LeanObject) -> *mut LeanObject;
    }

    // Pi with Default binder whose body has no loose BVars = arrow type (A → B).
    #[inline(always)]
    unsafe fn is_arrow(e: *const LeanObject) -> bool {
        matches!(expr_kind(e), LeanExprKind::Pi)
            && expr_binder_info_raw(e) == LeanBinderInfo::Default
            && expr_bvar_range(lean_ctor_get(e, 2)) == 0
    }

    // True iff the root component of name n is a numeral (mirrors is_numerical_name).
    unsafe fn is_numerical_name(mut n: *const LeanObject) -> bool {
        loop {
            if lean_is_scalar(n) {
                return false; // Name.anonymous
            }
            let tag = lean_name_tag(n);
            let prefix = lean_ctor_get(n, 0);
            if lean_is_scalar(prefix) {
                // Atomic: numeral iff Name.num (tag 2).
                return matches!(tag, LeanNameTag::Numeral);
            }
            n = prefix;
        }
    }

    // Print a Lean Nat (small scalar or GMP big integer).
    unsafe fn fmt_nat(nat: *const LeanObject, out: &mut String) {
        if lean_is_scalar(nat) {
            out.push_str(&lean_unbox(nat).to_string());
        } else {
            lean_inc(nat); // l_Nat_reprFast takes owned Nat
            let s = l_Nat_reprFast(nat as *mut LeanObject);
            out.push_str(&CStr::from_ptr(lean_string_cstr(s)).to_string_lossy());
            lean_dec(s);
        }
    }

    // Print a Name (anonymous → nothing printed).
    unsafe fn fmt_name(n: *const LeanObject, out: &mut String) {
        if lean_is_scalar(n) {
            return; // Name.anonymous
        }
        let tag = lean_name_tag(n);
        let prefix = lean_ctor_get(n, 0);
        if !lean_is_scalar(prefix) {
            fmt_name(prefix, out);
            out.push('.');
        }
        match tag {
            LeanNameTag::String => {
                // Name.str: field[1] = String
                let s = lean_ctor_get(n, 1);
                out.push_str(&CStr::from_ptr(lean_string_cstr(s)).to_string_lossy());
            }
            LeanNameTag::Numeral => {
                // Name.num: field[1] = Nat
                fmt_nat(lean_ctor_get(n, 1), out);
            }
            LeanNameTag::Anonymous => out.push_str("?name?"),
        }
    }

    // Print a Name with fix_name transform: lone numeric root → "M".
    unsafe fn fmt_fix_name(n: *const LeanObject, out: &mut String) {
        if lean_is_scalar(n) {
            return; // Name.anonymous
        }
        let tag = lean_name_tag(n);
        let prefix = lean_ctor_get(n, 0);
        if lean_is_scalar(prefix) {
            // Atomic component.
            if matches!(tag, LeanNameTag::Numeral) {
                out.push('M'); // lone numeral → "M"
                return;
            }
            // Atomic string: print normally below.
        } else {
            fmt_fix_name(prefix, out);
            out.push('.');
        }
        match tag {
            LeanNameTag::String => {
                let s = lean_ctor_get(n, 1);
                out.push_str(&CStr::from_ptr(lean_string_cstr(s)).to_string_lossy());
            }
            LeanNameTag::Numeral => {
                fmt_nat(lean_ctor_get(n, 1), out);
            }
            LeanNameTag::Anonymous => out.push_str("?name?"),
        }
    }

    // If l is succ^k(zero) for some k≥0, return Some(k); otherwise None.
    // Mirrors is_explicit + get_depth in the C++ level printer.
    unsafe fn level_explicit_depth(mut l: *const LeanObject) -> Option<usize> {
        let mut depth = 0usize;
        loop {
        if lean_is_scalar(l) {
            return Some(depth); // Level.zero
        }
        if !matches!(level_kind(l), LeanLevelKind::Succ) {
            return None;
        }
            depth += 1;
            l = lean_ctor_get(l, 0);
        }
    }

    // print_child wraps l in parens unless it is explicit, param, or mvar.
    unsafe fn fmt_level_child(l: *const LeanObject, out: &mut String) {
        let needs_parens = if lean_is_scalar(l) {
            false // Level.zero = explicit
        } else {
            match level_kind(l) {
                LeanLevelKind::Param => false, // Level.param
                LeanLevelKind::MVar => false,
                _ => level_explicit_depth(l).is_none(),
            }
        };
        if needs_parens {
            out.push('(');
            fmt_level(l, out);
            out.push(')');
        } else {
            fmt_level(l, out);
        }
    }

    // Print a Level, mirroring print() + print_child() in level.cpp.
    unsafe fn fmt_level(l: *const LeanObject, out: &mut String) {
        // Explicit level (succ^k zero) → print as decimal number.
        if let Some(depth) = level_explicit_depth(l) {
            out.push_str(&depth.to_string());
            return;
        }
        match level_kind(l) {
            LeanLevelKind::Succ => {
                out.push_str("succ ");
                fmt_level_child(lean_ctor_get(l, 0), out);
            }
            LeanLevelKind::Max | LeanLevelKind::IMax => {
                let tag = level_kind(l);
                out.push_str(if matches!(tag, LeanLevelKind::Max) {
                    "max "
                } else {
                    "imax "
                });
                // max/imax are right-associative; unroll consecutive same-kind nodes.
                fmt_level_child(lean_ctor_get(l, 0), out);
                let mut rhs = lean_ctor_get(l, 1);
                while matches!(level_kind(rhs), LeanLevelKind::Max)
                    == matches!(tag, LeanLevelKind::Max)
                    && !lean_is_scalar(rhs)
                {
                    out.push(' ');
                    fmt_level_child(lean_ctor_get(rhs, 0), out);
                    rhs = lean_ctor_get(rhs, 1);
                }
                out.push(' ');
                fmt_level_child(rhs, out);
            }
            LeanLevelKind::Param => {
                fmt_name(lean_ctor_get(l, 0), out);
            }
            _ => {
                // Level.mvar (tag 5)
                out.push('?');
                fmt_name(lean_ctor_get(l, 0), out);
            }
        }
    }

    #[inline(always)]
    unsafe fn level_is_zero(l: *const LeanObject) -> bool {
        lean_is_scalar(l) // Level.zero = lean_box(0)
    }

    #[inline(always)]
    unsafe fn level_is_succ(l: *const LeanObject) -> bool {
        matches!(level_kind(l), LeanLevelKind::Succ)
    }

    // Print a Sort expression (Prop / Type / Type.{n} / Sort.{u}).
    unsafe fn fmt_sort(e: *const LeanObject, out: &mut String) {
        let l = lean_ctor_get(e, 0);
        if level_is_zero(l) {
            out.push_str("Prop");
        } else if level_is_succ(l) && level_is_zero(lean_ctor_get(l, 0)) {
            out.push_str("Type");
        } else if level_is_succ(l) {
            // Type.{inner_level}; operator<< prints succ_of(l) = inner level.
            out.push_str("Type.{");
            fmt_level(lean_ctor_get(l, 0), out);
            out.push('}');
        } else {
            out.push_str("Sort.{");
            fmt_level(l, out);
            out.push('}');
        }
    }

    // Print a List Level (nil = lean_box(0); cons: field[0]=head, field[1]=tail).
    unsafe fn fmt_levels_list(mut ls: *const LeanObject, out: &mut String) {
        let mut first = true;
        while !lean_is_scalar(ls) {
            if !first {
                out.push_str(", ");
            }
            first = false;
            fmt_level(lean_ctor_get(ls, 0), out);
            ls = lean_ctor_get(ls, 1);
        }
    }

    // BVar/FVar/MVar/Sort/Const/Lit are atomic; Proj is atomic iff its inner expr is.
    unsafe fn is_atomic_expr(e: *const LeanObject) -> bool {
        match expr_kind(e) {
            LeanExprKind::BVar
            | LeanExprKind::FVar
            | LeanExprKind::MVar
            | LeanExprKind::Sort
            | LeanExprKind::Const
            | LeanExprKind::Lit => true,
            LeanExprKind::Proj => is_atomic_expr(lean_ctor_get(e, 2)),
            _ => false,
        }
    }

    unsafe fn fmt_expr_child(e: *mut LeanObject, out: &mut String) {
        if is_atomic_expr(e) {
            fmt_expr(e, out);
        } else {
            out.push('(');
            fmt_expr(e, out);
            out.push(')');
        }
    }

    // cleanup_name: replace name with "x" if root component is numeral. Returns owned Name.
    unsafe fn cleanup_name_owned(n: *mut LeanObject) -> *mut LeanObject {
        if is_numerical_name(n) {
            let x_str = lean_mk_string(b"x\0".as_ptr() as *const c_char); // owned String
            lean_name_mk_string(lean_box(0), x_str) // lean_box(0)=anonymous (scalar, no RC)
        } else {
            lean_inc(n);
            n
        }
    }

    #[inline(always)]
    unsafe fn fmt_binder_open(bi: LeanBinderInfo, out: &mut String) {
        match bi {
            LeanBinderInfo::Implicit => out.push('{'),
            LeanBinderInfo::StrictImplicit => out.push_str("{{"),
            LeanBinderInfo::InstImplicit => out.push('['),
            _ => out.push('('), // LeanBinderInfo::Default
        }
    }

    #[inline(always)]
    unsafe fn fmt_binder_close(bi: LeanBinderInfo, out: &mut String) {
        match bi {
            LeanBinderInfo::Implicit => out.push('}'),
            LeanBinderInfo::StrictImplicit => out.push_str("}}"),
            LeanBinderInfo::InstImplicit => out.push(']'),
            _ => out.push(')'),
        }
    }

    // Print a fun/forall binder chain, instantiating each body with a fresh FVar.
    // Mirrors print_binding in print.cpp (without pick_unused_name uniquification).
    unsafe fn fmt_binding(bname: &str, e_orig: *mut LeanObject, is_lambda: bool, out: &mut String) {
        let kind = expr_kind(e_orig);
        out.push_str(bname);

        // Track owned instantiated bodies so they can be released after printing.
        let mut owned_exprs: Vec<*mut LeanObject> = Vec::new();
        let mut current = e_orig; // initially borrowed

        loop {
            if expr_kind(current) != kind || is_arrow(current) {
                break;
            }
            out.push(' ');
            let name_field = lean_ctor_get(current, 0);
            let domain = lean_ctor_get(current, 1);
            let body = lean_ctor_get(current, 2);
            let bi = expr_binder_info_raw(current);

            let fresh_name = cleanup_name_owned(name_field); // owned Name

            fmt_binder_open(bi, out);
            fmt_name(fresh_name, out); // borrows fresh_name
            out.push_str(" : ");
            fmt_expr(domain, out);
            fmt_binder_close(bi, out);

            // Substitute BVar(0) in body with a fresh FVar carrying the binder name.
            let fresh_fvar = lean_expr_mk_fvar(fresh_name); // consumes fresh_name, owned Expr
            let inst_body = lean_expr_instantiate1(body, fresh_fvar); // both borrowed, owned result
            lean_dec(fresh_fvar);

            owned_exprs.push(inst_body);
            current = inst_body; // borrow from owned_exprs.last()
        }

        if is_lambda {
            out.push_str(" => ");
        } else {
            out.push_str(", ");
        }
        fmt_expr(current, out);

        for obj in owned_exprs {
            lean_dec(obj);
        }
    }

    // Print a let/have binding with instantiated body.
    unsafe fn fmt_let(e: *mut LeanObject, out: &mut String) {
        let nondep = expr_let_nondep(e);
        let name_field = lean_ctor_get(e, 0);
        let ty = lean_ctor_get(e, 1);
        let val = lean_ctor_get(e, 2);
        let body = lean_ctor_get(e, 3);

        out.push_str(if nondep { "have " } else { "let " });

        let fresh_name = cleanup_name_owned(name_field); // owned
        fmt_name(fresh_name, out);
        out.push_str(" : ");
        fmt_expr(ty, out);
        out.push_str(" := ");
        fmt_expr(val, out);
        out.push_str("; ");

        let fresh_fvar = lean_expr_mk_fvar(fresh_name); // consumes fresh_name
        let inst_body = lean_expr_instantiate1(body, fresh_fvar);
        lean_dec(fresh_fvar);
        fmt_expr(inst_body, out);
        lean_dec(inst_body);
    }

    // Print escaped string content (without surrounding quotes), mirroring escaped() in C++.
    unsafe fn fmt_escaped(s: *mut LeanObject, out: &mut String) {
        for &b in CStr::from_ptr(lean_string_cstr(s)).to_bytes() {
            match b {
                b'"' => out.push_str("\\\""),
                b'\\' => out.push_str("\\\\"),
                b'\n' => out.push_str("\\n"),
                b'\r' => out.push_str("\\r"),
                b'\t' => out.push_str("\\t"),
                0..=31 | 127 => {
                    out.push_str(&format!("\\x{:02x}", b));
                }
                _ => out.push(b as char),
            }
        }
    }

    // Print KVMap entries: "key:value " for each entry (mirroring print_mdata in print.cpp).
    // In C++ the kvmap type is list_ref<kvmap_entry>, i.e. the list itself (not a wrapper object).
    // MData field[0] stores the List (Name × DataValue) directly.
    // List.nil = lean_box(0); List.cons: field[0]=Prod.mk Name DataValue, field[1]=tail.
    unsafe fn fmt_mdata_kvmap(kvmap: *mut LeanObject, out: &mut String) {
        let mut list = kvmap; // kvmap IS the List — no extra field access needed
        while !lean_is_scalar(list) {
            // List.cons: field[0] = Prod.mk Name DataValue, field[1] = tail
            let pair = lean_ctor_get(list, 0);
            let key = lean_ctor_get(pair, 0); // Name
            let dv = lean_ctor_get(pair, 1); // DataValue
            // Print "key:"
            fmt_name(key, out);
            out.push(':');
            // Print value
            match lean_data_value_kind(dv) {
                LeanDataValueKind::String => {
                    // DataValue.ofString: field[0] = String
                    fmt_escaped(lean_ctor_get(dv, 0), out);
                }
                LeanDataValueKind::Bool => {
                    // DataValue.ofBool: lean_alloc_ctor(1, 0, 1) + lean_ctor_set_uint8(v, 0, b)
                    // Bool is stored as a uint8 scalar (NOT a boxed pointer).
                    let b = lean_ctor_get_uint8(dv, 0);
                    if b != 0 {
                        out.push('1');
                    } else {
                        out.push('0');
                    }
                }
                LeanDataValueKind::Name => {
                    // DataValue.ofName: field[0] = Name
                    fmt_name(lean_ctor_get(dv, 0), out);
                }
                LeanDataValueKind::Nat => {
                    // DataValue.ofNat: field[0] = Nat
                    fmt_nat(lean_ctor_get(dv, 0), out);
                }
                _ => {
                    // ofInt, ofSyntax, or unknown — skip value
                    out.push('?');
                }
            }
            out.push(' ');
            list = lean_ctor_get(list, 1); // tail
        }
    }

    // Print an Expr, mirroring print_expr_fn::print in print.cpp.
    unsafe fn fmt_expr(e: *mut LeanObject, out: &mut String) {
        match expr_kind(e) {
            LeanExprKind::BVar => {
                // #idx
                out.push('#');
                fmt_nat(lean_ctor_get(e, 0), out);
            }
            LeanExprKind::FVar => {
                // FVarId is a single-field struct; at the ABI level it IS the Name.
                fmt_name(lean_ctor_get(e, 0), out);
            }
            LeanExprKind::MVar => {
                out.push('?');
                fmt_fix_name(lean_ctor_get(e, 0), out);
            }
            LeanExprKind::Sort => {
                fmt_sort(e, out);
            }
            LeanExprKind::Const => {
                let name = lean_ctor_get(e, 0);
                let levels = lean_ctor_get(e, 1); // List Level; nil = lean_box(0)
                fmt_name(name, out);
                if !lean_is_scalar(levels) {
                    out.push_str(".{");
                    fmt_levels_list(levels, out);
                    out.push('}');
                }
            }
            LeanExprKind::App => {
                let f = lean_ctor_get(e, 0);
                let a = lean_ctor_get(e, 1);
                // Left-spine: don't wrap nested App in parens.
                if matches!(expr_kind(f), LeanExprKind::App) {
                    fmt_expr(f, out);
                } else {
                    fmt_expr_child(f, out);
                }
                out.push(' ');
                fmt_expr_child(a, out);
            }
            LeanExprKind::Lambda => {
                fmt_binding("fun", e, true, out);
            }
            LeanExprKind::Pi => {
                if is_arrow(e) {
                    // Arrow body has bvarRange=0, so lower_loose_bvars is a no-op.
                    let domain = lean_ctor_get(e, 1);
                    let body = lean_ctor_get(e, 2);
                    fmt_expr_child(domain, out);
                    out.push_str(" -> ");
                    if is_atomic_expr(body) || is_arrow(body) {
                        fmt_expr(body, out);
                    } else {
                        fmt_expr_child(body, out);
                    }
                } else {
                    fmt_binding("forall", e, false, out);
                }
            }
            LeanExprKind::Let => {
                fmt_let(e, out);
            }
            LeanExprKind::Lit => {
                let lit = lean_ctor_get(e, 0); // Literal
                if matches!(lean_literal_tag(lit), LeanLiteralTag::Nat) {
                    // Literal.natVal: field[0] = Nat
                    fmt_nat(lean_ctor_get(lit, 0), out);
                } else {
                    // Literal.strVal: field[0] = String (escaped output)
                    let s = lean_ctor_get(lit, 0);
                    out.push('"');
                    fmt_escaped(s, out);
                    out.push('"');
                }
            }
            LeanExprKind::MData => {
                out.push_str("[mdata ");
                fmt_mdata_kvmap(lean_ctor_get(e, 0), out); // field[0] = KVMap
                fmt_expr(lean_ctor_get(e, 1), out); // field[1] = Expr
                out.push(']');
            }
            LeanExprKind::Proj => {
                // Proj: field[0]=typeName, field[1]=idx(Nat, 0-based), field[2]=struct.
                // Display as 1-indexed (matching C++: proj_idx.to_mpz() + 1).
                let idx = lean_ctor_get(e, 1);
                let inner = lean_ctor_get(e, 2);
                fmt_expr_child(inner, out);
                out.push('.');
                if lean_is_scalar(idx) {
                    out.push_str(&(lean_unbox(idx) + 1).to_string());
                } else {
                    lean_inc(idx);
                    let s = l_Nat_reprFast(idx);
                    out.push_str(&CStr::from_ptr(lean_string_cstr(s)).to_string_lossy());
                    lean_dec(s);
                }
            }
            _ => {
                out.push_str("?expr?");
            }
        }
    }

    // lean_expr_dbg_to_string: ToString Expr instance (@[extern "lean_expr_dbg_to_string"]).
    // Argument is borrowed (@&); return is owned.
    #[no_mangle]
    pub unsafe fn lean_expr_dbg_to_string(e: *mut LeanObject) -> *mut LeanObject {
        let mut out = String::new();
        fmt_expr(e, &mut out);
        let cstr = std::ffi::CString::new(out)
            .unwrap_or_else(|_| std::ffi::CString::new("?nul_in_expr?").unwrap());
        lean_mk_string(cstr.as_ptr())
    }
}
