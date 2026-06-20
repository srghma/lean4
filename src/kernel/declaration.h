/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"

namespace lean {
extern "C" object * lean_mk_reducibility_hints_regular(uint32 h);
extern "C" uint32 lean_reducibility_hints_get_height(object * o);
extern "C" object * lean_mk_axiom_val(object * n, object * lparams, object * type, uint8 is_unsafe);
extern "C" uint8 lean_axiom_val_is_unsafe(object * v);
extern "C" object * lean_mk_definition_val(object * n, object * lparams, object * type, object * value, object * hints, uint8 safety, object * all);
extern "C" uint8 lean_definition_val_get_safety(object * v);
extern "C" object * lean_mk_theorem_val(object * n, object * lparams, object * type, object * value, object * all);
extern "C" object * lean_mk_opaque_val(object * n, object * lparams, object * type, object * value, uint8 is_unsafe, object * all);
extern "C" uint8 lean_opaque_val_is_unsafe(object * v);
extern "C" object * lean_mk_quot_val(object * n, object * lparams, object * type, uint8 k);
extern "C" uint8 lean_quot_val_kind(object * v);
extern "C" object * lean_mk_inductive_val(object * n, object * lparams, object * type, object * nparams, object * nindices,
                                          object * all, object * cnstrs, object * nnested, uint8 rec, uint8 unsafe, uint8 is_refl);
extern "C" uint8 lean_inductive_val_is_rec(object * v);
extern "C" uint8 lean_inductive_val_is_unsafe(object * v);
extern "C" uint8 lean_inductive_val_is_reflexive(object * v);
extern "C" object * lean_mk_constructor_val(object * n, object * lparams, object * type, object * induct,
                                            object * cidx, object * nparams, object * nfields, uint8 unsafe);
extern "C" uint8 lean_constructor_val_is_unsafe(object * v);
extern "C" object * lean_mk_recursor_val(object * n, object * lparams, object * type, object * all,
                                         object * nparams, object * nindices, object * nmotives, object * nminors,
                                         object * rules, uint8 k, uint8 unsafe);
extern "C" uint8 lean_recursor_k(object * v);
extern "C" uint8 lean_recursor_is_unsafe(object * v);
extern "C" object * lean_mk_inductive_decl(object * lparams, object * nparams, object * types, uint8 unsafe);
extern "C" uint8 lean_is_unsafe_inductive_decl(object * d);

/**
inductive ReducibilityHints where
  | opaque  : ReducibilityHints
  | abbrev  : ReducibilityHints
  | regular : UInt32 → ReducibilityHints

Reducibility hints are used in the convertibility checker (aka is_def_eq predicate),
whenever checking a constraint such as

           (f ...) =?= (g ...)

where f and g are definitions, and the checker has to decide which one will be unfolded.
If f (g) is Opaque,             then g (f) is unfolded if it is also not marked as Opaque.
Else if f (g) is Abbreviation,  then f (g) is unfolded if g (f) is also not marked as Abbreviation.
Else if f and g are Regular,    then we unfold the one with the biggest definitional height.
Otherwise unfold both.

The definitional height is by default computed by the kernel. It only takes into account
other Regular definitions used in a definition.

Remark: the hint only affects performance. */
enum class reducibility_hints_kind { Opaque, Abbreviation, Regular };
class reducibility_hints : public object_ref {
    reducibility_hints(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit reducibility_hints(object * r):object_ref(r) {}
public:
    static reducibility_hints mk_opaque() { return reducibility_hints(box(static_cast<unsigned>(reducibility_hints_kind::Opaque))); }
    static reducibility_hints mk_abbreviation() { return reducibility_hints(box(static_cast<unsigned>(reducibility_hints_kind::Abbreviation))); }
    static reducibility_hints mk_regular(unsigned h) {
        return reducibility_hints(lean_mk_reducibility_hints_regular(h));
    }
    reducibility_hints_kind kind() const { return static_cast<reducibility_hints_kind>(obj_tag(raw())); }
    bool is_regular() const { return kind() == reducibility_hints_kind::Regular; }
    bool is_abbrev() const { return kind() == reducibility_hints_kind::Abbreviation; }
    unsigned get_height() const {
        return lean_reducibility_hints_get_height(to_obj_arg());
    }
};

/** Given h1 and h2 the hints for definitions f1 and f2, then
    result is
    <  0 If f1 should be unfolded
    == 0 If f1 and f2 should be unfolded
    >  0 If f2 should be unfolded */
inline int compare(reducibility_hints const & h1, reducibility_hints const & h2) {
    if (h1.kind() == h2.kind()) {
        if (h1.kind() == reducibility_hints_kind::Regular) {
            if (h1.get_height() == h2.get_height())
                return 0;
            else if (h1.get_height() > h2.get_height())
                return -1;
            else
                return 1;
        } else {
            return 0;
        }
    } else {
        if (h1.kind() == reducibility_hints_kind::Opaque) {
            return 1;
        } else if (h2.kind() == reducibility_hints_kind::Opaque) {
            return -1;
        } else if (h1.kind() == reducibility_hints_kind::Abbreviation) {
            return -1;
        } else if (h2.kind() == reducibility_hints_kind::Abbreviation) {
            return 1;
        } else {
            lean_unreachable();
        }
    }
}

/*
structure ConstantVal where
  name : Name
  levelParams : List Name
  type : Expr
*/
class constant_val : public object_ref {
public:
    constant_val(name const & n, names const & lparams, expr const & type):
        object_ref(mk_cnstr(0, n, lparams, type)) {
    }
    constant_val(constant_val const & other):object_ref(other) {}
    constant_val(constant_val && other) noexcept:object_ref(std::move(other)) {}
    constant_val & operator=(constant_val const & other) { object_ref::operator=(other); return *this; }
    constant_val & operator=(constant_val && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    name const & get_name() const { return static_cast<name const &>(cnstr_get_ref(*this, 0)); }
    names const & get_lparams() const { return static_cast<names const &>(cnstr_get_ref(*this, 1)); }
    expr const & get_type() const { return static_cast<expr const &>(cnstr_get_ref(*this, 2)); }
};

/*
structure AxiomVal extends ConstantVal where
  isUnsafe : Bool
*/
class axiom_val : public object_ref {
public:
    axiom_val(name const & n, names const & lparams, expr const & type, bool is_unsafe):
        object_ref(lean_mk_axiom_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), is_unsafe)) {
    }
    axiom_val(axiom_val const & other):object_ref(other) {}
    axiom_val(axiom_val && other) noexcept:object_ref(std::move(other)) {}
    axiom_val & operator=(axiom_val const & other) { object_ref::operator=(other); return *this; }
    axiom_val & operator=(axiom_val && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    bool is_unsafe() const { return lean_axiom_val_is_unsafe(to_obj_arg()); }
};

/*
inductive DefinitionSafety where
  | «unsafe» | safe | «partial»
*/
enum class definition_safety { unsafe, safe, partial };

/*
structure DefinitionVal extends ConstantVal where
  value  : Expr
  hints  : ReducibilityHints
  safety : DefinitionSafety
*/
class definition_val : public object_ref {
public:
    definition_val(name const & n, names const & lparams, expr const & type, expr const & val, reducibility_hints const & hints, definition_safety safety, names const & all):
        object_ref(lean_mk_definition_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), val.to_obj_arg(),
                                          hints.to_obj_arg(), static_cast<uint8>(safety), all.to_obj_arg())) {
    }
    definition_val(definition_val const & other):object_ref(other) {}
    definition_val(definition_val && other) noexcept:object_ref(std::move(other)) {}
    definition_val & operator=(definition_val const & other) { object_ref::operator=(other); return *this; }
    definition_val & operator=(definition_val && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    expr const & get_value() const { return static_cast<expr const &>(cnstr_get_ref(*this, 1)); }
    reducibility_hints const & get_hints() const { return static_cast<reducibility_hints const &>(cnstr_get_ref(*this, 2)); }
    definition_safety get_safety() const { return static_cast<definition_safety>(lean_definition_val_get_safety(to_obj_arg())); }
    bool is_unsafe() const { return get_safety() == definition_safety::unsafe; }
};
typedef list_ref<definition_val> definition_vals;

/*
structure TheoremVal extends ConstantVal where
  value : Expr
  all : List Name := [name]
*/
class theorem_val : public object_ref {
public:
    theorem_val(name const & n, names const & lparams, expr const & type, expr const & val, names const & all):
        object_ref(lean_mk_theorem_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), val.to_obj_arg(), all.to_obj_arg())) {
    }
    theorem_val(theorem_val const & other):object_ref(other) {}
    theorem_val(theorem_val && other) noexcept:object_ref(std::move(other)) {}
    theorem_val & operator=(theorem_val const & other) { object_ref::operator=(other); return *this; }
    theorem_val & operator=(theorem_val && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    expr const & get_value() const { return static_cast<expr const &>(cnstr_get_ref(*this, 1)); }
};

/*
structure OpaqueVal extends ConstantVal where
  value : Expr
  isUnsafe : Bool
  all : List Name := [name]
*/
class opaque_val : public object_ref {
public:
    opaque_val(name const & n, names const & lparams, expr const & type, expr const & val, bool is_unsafe, names const & all):
        object_ref(lean_mk_opaque_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), val.to_obj_arg(), is_unsafe, all.to_obj_arg())) {
    }
    opaque_val(opaque_val const & other):object_ref(other) {}
    opaque_val(opaque_val && other) noexcept:object_ref(std::move(other)) {}
    opaque_val & operator=(opaque_val const & other) { object_ref::operator=(other); return *this; }
    opaque_val & operator=(opaque_val && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    expr const & get_value() const { return static_cast<expr const &>(cnstr_get_ref(*this, 1)); }
    bool is_unsafe() const { return lean_opaque_val_is_unsafe(to_obj_arg()); }
};

/*
structure Constructor where
  name : Name
  type : Expr
*/
typedef pair_ref<name, expr> constructor;
inline name const & constructor_name(constructor const & c) { return c.fst(); }
inline expr const & constructor_type(constructor const & c) { return c.snd(); }
typedef list_ref<constructor> constructors;

/**
structure InductiveType where
  name : Name
  type : Expr
  ctors : List Constructor
*/
class inductive_type : public object_ref {
public:
    inductive_type(name const & id, expr const & type, constructors const & cnstrs):
        object_ref(mk_cnstr(0, id, type, cnstrs)) {
    }
    inductive_type(inductive_type const & other):object_ref(other) {}
    inductive_type(inductive_type && other) noexcept:object_ref(std::move(other)) {}
    inductive_type & operator=(inductive_type const & other) { object_ref::operator=(other); return *this; }
    inductive_type & operator=(inductive_type && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    name const & get_name() const { return static_cast<name const &>(cnstr_get_ref(*this, 0)); }
    expr const & get_type() const { return static_cast<expr const &>(cnstr_get_ref(*this, 1)); }
    constructors const & get_cnstrs() const { return static_cast<constructors const &>(cnstr_get_ref(*this, 2)); }
};
typedef list_ref<inductive_type> inductive_types;

/*
inductive Declaration where
  | axiomDecl       (val : AxiomVal)
  | defnDecl        (val : DefinitionVal)
  | thmDecl         (val : TheoremVal)
  | opaqueDecl      (val : OpaqueVal)
  | quotDecl
  | mutualDefnDecl  (defns : List DefinitionVal) -- All definitions must be marked as `unsafe` or `partial`
  | inductDecl      (lparams : List Name) (nparams : Nat) (types : List InductiveType) (isUnsafe : Bool)
*/
enum class declaration_kind { Axiom, Definition, Theorem, Opaque, Quot, MutualDefinition, Inductive };
class declaration : public object_ref {
    object * get_val_obj() const { return cnstr_get(raw(), 0); }
    object_ref const & to_val() const { return cnstr_get_ref(*this, 0); }
public:
    declaration();
    declaration(declaration const & other):object_ref(other) {}
    declaration(declaration && other) noexcept:object_ref(std::move(other)) {}
    /* low-level constructors */
    explicit declaration(object * o):object_ref(o) {}
    explicit declaration(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit declaration(object_ref const & o):object_ref(o) {}
    declaration_kind kind() const { return static_cast<declaration_kind>(obj_tag(raw())); }

    declaration & operator=(declaration const & other) { object_ref::operator=(other); return *this; }
    declaration & operator=(declaration && other) noexcept { object_ref::operator=(std::move(other)); return *this; }

    friend bool is_eqp(declaration const & d1, declaration const & d2) { return d1.raw() == d2.raw(); }

    bool is_definition() const { return kind() == declaration_kind::Definition; }
    bool is_axiom() const { return kind() == declaration_kind::Axiom; }
    bool is_theorem() const { return kind() == declaration_kind::Theorem; }
    bool is_opaque() const { return kind() == declaration_kind::Opaque; }
    bool is_mutual() const { return kind() == declaration_kind::MutualDefinition; }
    bool is_inductive() const { return kind() == declaration_kind::Inductive; }
    bool is_unsafe() const;
    /** \brief Only definitions have values for the purpose of reduction and
        type checking. Theorems used to be like that; now they are treated like
        opaque declarations. */
    bool has_value() const { return is_definition(); }

    axiom_val const & to_axiom_val() const { lean_assert(is_axiom()); return static_cast<axiom_val const &>(cnstr_get_ref(raw(), 0)); }
    definition_val const & to_definition_val() const { lean_assert(is_definition()); return static_cast<definition_val const &>(cnstr_get_ref(raw(), 0)); }
    theorem_val const & to_theorem_val() const { lean_assert(is_theorem()); return static_cast<theorem_val const &>(cnstr_get_ref(raw(), 0)); }
    opaque_val const & to_opaque_val() const { lean_assert(is_opaque()); return static_cast<opaque_val const &>(cnstr_get_ref(raw(), 0)); }
    definition_vals const & to_definition_vals() const { lean_assert(is_mutual()); return static_cast<definition_vals const &>(cnstr_get_ref(raw(), 0)); }
};

inline declaration mk_axiom(name const & n, names const & lparams, expr const & t, bool is_unsafe = false) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Axiom), axiom_val(n, lparams, t, is_unsafe)));
}

inline declaration mk_inductive_decl(names const & lparams, nat const & nparams, inductive_types const & types, bool is_unsafe) {
    return declaration(lean_mk_inductive_decl(lparams.to_obj_arg(), nparams.to_obj_arg(), types.to_obj_arg(), is_unsafe));
}

/** \brief View for manipulating declaration.induct_decl constructor.
    | induct_decl      (lparams : list name) (nparams : nat) (types : list inductive_type) (is_unsafe : bool) */
class inductive_decl : public object_ref {
public:
    inductive_decl(inductive_decl const & other):object_ref(other) {}
    inductive_decl(inductive_decl && other) noexcept:object_ref(std::move(other)) {}
    inductive_decl(declaration const & d):object_ref(d) { lean_assert(d.is_inductive()); }
    inductive_decl & operator=(inductive_decl const & other) { object_ref::operator=(other); return *this; }
    inductive_decl & operator=(inductive_decl && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    names const & get_lparams() const { return static_cast<names const &>(cnstr_get_ref(raw(), 0)); }
    nat const & get_nparams() const { return static_cast<nat const &>(cnstr_get_ref(raw(), 1)); }
    inductive_types const & get_types() const { return static_cast<inductive_types const &>(cnstr_get_ref(raw(), 2)); }
    bool is_unsafe() const { return lean_is_unsafe_inductive_decl(to_obj_arg()); }
};

inline bool declaration::is_unsafe() const {
    switch (kind()) {
    case declaration_kind::Definition:       return to_definition_val().get_safety() == definition_safety::unsafe;
    case declaration_kind::Axiom:            return to_axiom_val().is_unsafe();
    case declaration_kind::Theorem:          return false;
    case declaration_kind::Opaque:           return to_opaque_val().is_unsafe();
    case declaration_kind::Inductive:        return inductive_decl(*this).is_unsafe();
    case declaration_kind::Quot:             return false;
    case declaration_kind::MutualDefinition: return true;
    }
    lean_unreachable();
}

/*
structure InductiveVal extends ConstantVal where
  numParams : Nat
  numIndices : Nat
  all : List Name    -- List of all (including this one) inductive datatypes in the mutual
                        declaration containing this one
  ctors : List Name  -- List of the names of the constructors for this inductive datatype
  numNested : Nat
  isRec : Bool
  isUnsafe : Bool
  isReflexive : Bool
*/
class inductive_val : public object_ref {
public:
    inductive_val(name const & n, names const & lparams, expr const & type, unsigned nparams,
                  unsigned nindices, names const & all, names const & cnstrs, unsigned nnested, bool is_rec, bool is_unsafe, bool is_reflexive):
        object_ref(lean_mk_inductive_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), nat(nparams).to_obj_arg(),
                                         nat(nindices).to_obj_arg(), all.to_obj_arg(), cnstrs.to_obj_arg(),
                                         nat(nnested).to_obj_arg(), is_rec, is_unsafe, is_reflexive)) {
    }
    inductive_val(inductive_val const & other):object_ref(other) {}
    inductive_val(inductive_val && other) noexcept:object_ref(std::move(other)) {}
    inductive_val & operator=(inductive_val const & other) { object_ref::operator=(other); return *this; }
    inductive_val & operator=(inductive_val && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    unsigned get_nparams() const { return static_cast<nat const &>(cnstr_get_ref(*this, 1)).get_small_value(); }
    unsigned get_nindices() const { return static_cast<nat const &>(cnstr_get_ref(*this, 2)).get_small_value(); }
    names const & get_all() const { return static_cast<names const &>(cnstr_get_ref(*this, 3)); }
    names const & get_cnstrs() const { return static_cast<names const &>(cnstr_get_ref(*this, 4)); }
    unsigned get_ncnstrs() const { return length(get_cnstrs()); }
    unsigned get_nnested() const { return static_cast<nat const &>(cnstr_get_ref(*this, 5)).get_small_value(); }
    bool is_rec() const { return lean_inductive_val_is_rec(to_obj_arg()); }
    bool is_unsafe() const { return lean_inductive_val_is_unsafe(to_obj_arg()); }
    bool is_reflexive() const { return lean_inductive_val_is_reflexive(to_obj_arg()); }
};

/*
structure ConstructorVal extends ConstantVal where
  induct  : Name  -- Inductive type this constructor is a member of
  cidx    : Nat   -- Constructor index (i.e., Position in the inductive declaration)
  numParams : Nat -- Number of parameters in inductive datatype
  numFields : Nat -- Number of fields (i.e., arity - nparams)
  isUnsafe : Bool
*/
class constructor_val : public object_ref {
public:
    constructor_val(name const & n, names const & lparams, expr const & type, name const & induct, unsigned cidx, unsigned nparams, unsigned nfields, bool is_unsafe):
        object_ref(lean_mk_constructor_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), induct.to_obj_arg(),
                                           nat(cidx).to_obj_arg(), nat(nparams).to_obj_arg(), nat(nfields).to_obj_arg(), is_unsafe)) {
    }
    constructor_val(constructor_val const & other):object_ref(other) {}
    constructor_val(constructor_val && other) noexcept:object_ref(std::move(other)) {}
    constructor_val & operator=(constructor_val const & other) { object_ref::operator=(other); return *this; }
    constructor_val & operator=(constructor_val && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_induct() const { return static_cast<name const &>(cnstr_get_ref(*this, 1)); }
    unsigned get_cidx() const { return static_cast<nat const &>(cnstr_get_ref(*this, 2)).get_small_value(); }
    unsigned get_nparams() const { return static_cast<nat const &>(cnstr_get_ref(*this, 3)).get_small_value(); }
    unsigned get_nfields() const { return static_cast<nat const &>(cnstr_get_ref(*this, 4)).get_small_value(); }
    bool is_unsafe() const { return lean_constructor_val_is_unsafe(to_obj_arg()); }
};

/*
structure RecursorRule where
  ctor : Name   -- Reduction rule for this Constructor
  nfields : Nat -- Number of fields (i.e., without counting inductive datatype parameters)
  rhs : Expr    -- Right hand side of the reduction rule
*/
class recursor_rule : public object_ref {
public:
    recursor_rule(name const & cnstr, unsigned nfields, expr const & rhs):
        object_ref(mk_cnstr(0, cnstr, nat(nfields), rhs)) {
    }
    recursor_rule(recursor_rule const & other):object_ref(other) {}
    recursor_rule(recursor_rule && other) noexcept:object_ref(std::move(other)) {}
    recursor_rule & operator=(recursor_rule const & other) { object_ref::operator=(other); return *this; }
    recursor_rule & operator=(recursor_rule && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    name const & get_cnstr() const { return static_cast<name const &>(cnstr_get_ref(*this, 0)); }
    unsigned get_nfields() const { return static_cast<nat const &>(cnstr_get_ref(*this, 1)).get_small_value(); }
    expr const & get_rhs() const { return static_cast<expr const &>(cnstr_get_ref(*this, 2)); }
};

typedef list_ref<recursor_rule> recursor_rules;

/*
structure RecursorVal extends ConstantVal where
  all : List Name  -- List of all inductive datatypes in the mutual declaration that generated this recursor
  numParams : Nat
  numIndices : Nat
  numMotives : Nat
  numMinors : Nat
  rules : List RecursorRule
  k : Bool         -- It supports K-like reduction.
  isUnsafe : Bool
*/
class recursor_val : public object_ref {
public:
    recursor_val(name const & n, names const & lparams, expr const & type,
                 names const & all, unsigned nparams, unsigned nindices, unsigned nmotives,
                 unsigned nminors, recursor_rules const & rules, bool k, bool is_unsafe):
        object_ref(lean_mk_recursor_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), all.to_obj_arg(),
                                        nat(nparams).to_obj_arg(), nat(nindices).to_obj_arg(), nat(nmotives).to_obj_arg(),
                                        nat(nminors).to_obj_arg(), rules.to_obj_arg(), k, is_unsafe)) {
    }
    recursor_val(recursor_val const & other):object_ref(other) {}
    recursor_val(recursor_val && other) noexcept:object_ref(std::move(other)) {}
    recursor_val & operator=(recursor_val const & other) { object_ref::operator=(other); return *this; }
    recursor_val & operator=(recursor_val && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    name const & get_major_induct() const {
        unsigned int n = get_major_idx();
        expr const * t = &(to_constant_val().get_type());
        for (unsigned int i = 0; i < n; i++) {
            t = &(binding_body(*t));
        }
        t = &(binding_domain(*t));
        t = &(get_app_fn(*t));
        return const_name(*t);
    }
    names const & get_all() const { return static_cast<names const &>(cnstr_get_ref(*this, 1)); }
    unsigned get_nparams() const { return static_cast<nat const &>(cnstr_get_ref(*this, 2)).get_small_value(); }
    unsigned get_nindices() const { return static_cast<nat const &>(cnstr_get_ref(*this, 3)).get_small_value(); }
    unsigned get_nmotives() const { return static_cast<nat const &>(cnstr_get_ref(*this, 4)).get_small_value(); }
    unsigned get_nminors() const { return static_cast<nat const &>(cnstr_get_ref(*this, 5)).get_small_value(); }
    unsigned get_major_idx() const { return get_nparams() + get_nmotives() + get_nminors() + get_nindices(); }
    recursor_rules const & get_rules() const { return static_cast<recursor_rules const &>(cnstr_get_ref(*this, 6)); }
    bool is_k() const { return lean_recursor_k(to_obj_arg()); }
    bool is_unsafe() const { return lean_recursor_is_unsafe(to_obj_arg()); }
};

enum class quot_kind { Type, Mk, Lift, Ind };

/*
inductive QuotKind where
  | type  -- `Quot`
  | ctor  -- `Quot.mk`
  | lift  -- `Quot.lift`
  | ind   -- `Quot.ind`

structure QuotVal extends ConstantVal where
  kind : QuotKind
*/
class quot_val : public object_ref {
public:
    quot_val(name const & n, names const & lparams, expr const & type, quot_kind k):
        object_ref(lean_mk_quot_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), static_cast<uint8>(k))) {
    }
    quot_val(quot_val const & other):object_ref(other) {}
    quot_val(quot_val && other) noexcept:object_ref(std::move(other)) {}
    quot_val & operator=(quot_val const & other) { object_ref::operator=(other); return *this; }
    quot_val & operator=(quot_val && other) noexcept { object_ref::operator=(std::move(other)); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    quot_kind get_quot_kind() const { return static_cast<quot_kind>(lean_quot_val_kind(to_obj_arg())); }
};

/*
/-- Information associated with constant declarations. -/
inductive ConstantInfo where
  | axiomInfo    (val : AxiomVal)
  | defnInfo     (val : DefinitionVal)
  | thmInfo      (val : TheoremVal)
  | opaqueInfo   (val : OpaqueVal)
  | quotInfo     (val : QuotVal)
  | inductInfo   (val : InductiveVal)
  | ctorInfo     (val : ConstructorVal)
  | recInfo      (val : RecursorVal)l)
*/
enum class constant_info_kind { Axiom, Definition, Theorem, Opaque, Quot, Inductive, Constructor, Recursor };
class constant_info : public object_ref {
    object * get_val_obj() const { return cnstr_get(raw(), 0); }
    object_ref const & to_val() const { return cnstr_get_ref(*this, 0); }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(to_val(), 0)); }
public:
    constant_info();
    constant_info(declaration const & d):object_ref(d.raw()) {
        lean_assert(d.is_definition() || d.is_theorem() || d.is_axiom() || d.is_opaque());
        inc_ref(d.raw());
    }
    constant_info(definition_val const & v):
        object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Definition), v)) {
    }
    constant_info(quot_val const & v):
        object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Quot), v)) {
    }
    constant_info(inductive_val const & v):
        object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Inductive), v)) {
    }
    constant_info(constructor_val const & v):
        object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Constructor), v)) {
    }
    constant_info(recursor_val const & v):
        object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Recursor), v)) {
    }
    constant_info(constant_info const & other):object_ref(other) {}
    constant_info(constant_info && other) noexcept:object_ref(std::move(other)) {}
    explicit constant_info(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit constant_info(obj_arg o):object_ref(o) {}

    constant_info_kind kind() const { return static_cast<constant_info_kind>(cnstr_tag(raw())); }

    constant_info & operator=(constant_info const & other) { object_ref::operator=(other); return *this; }
    constant_info & operator=(constant_info && other) noexcept { object_ref::operator=(std::move(other)); return *this; }

    friend bool is_eqp(constant_info const & d1, constant_info const & d2) { return d1.raw() == d2.raw(); }

    bool is_unsafe() const {
        switch (kind()) {
        case constant_info_kind::Axiom:       return to_axiom_val().is_unsafe();
        case constant_info_kind::Definition:  return to_definition_val().get_safety() == definition_safety::unsafe;
        case constant_info_kind::Theorem:     return false;
        case constant_info_kind::Opaque:      return to_opaque_val().is_unsafe();
        case constant_info_kind::Quot:        return false;
        case constant_info_kind::Inductive:   return to_inductive_val().is_unsafe();
        case constant_info_kind::Constructor: return to_constructor_val().is_unsafe();
        case constant_info_kind::Recursor:    return to_recursor_val().is_unsafe();
        }
        lean_unreachable();
    }

    bool is_definition() const { return kind() == constant_info_kind::Definition; }
    bool is_axiom() const { return kind() == constant_info_kind::Axiom; }
    bool is_theorem() const { return kind() == constant_info_kind::Theorem; }
    bool is_opaque() const { return kind() == constant_info_kind::Opaque; }
    bool is_inductive() const { return kind() == constant_info_kind::Inductive; }
    bool is_constructor() const { return kind() == constant_info_kind::Constructor; }
    bool is_recursor() const { return kind() == constant_info_kind::Recursor; }
    bool is_quot() const { return kind() == constant_info_kind::Quot; }

    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    unsigned get_num_lparams() const { return length(get_lparams()); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    bool has_value(bool allow_opaque = false) const {
        return is_theorem() || is_definition() || (allow_opaque && is_opaque());
    }
    reducibility_hints const & get_hints() const;

    axiom_val const & to_axiom_val() const { lean_assert(is_axiom()); return static_cast<axiom_val const &>(to_val()); }
    definition_val const & to_definition_val() const { lean_assert(is_definition()); return static_cast<definition_val const &>(to_val()); }
    theorem_val const & to_theorem_val() const { lean_assert(is_theorem()); return static_cast<theorem_val const &>(to_val()); }
    opaque_val const & to_opaque_val() const { lean_assert(is_opaque()); return static_cast<opaque_val const &>(to_val()); }
    inductive_val const & to_inductive_val() const { lean_assert(is_inductive()); return static_cast<inductive_val const &>(to_val()); }
    constructor_val const & to_constructor_val() const { lean_assert(is_constructor()); return static_cast<constructor_val const &>(to_val()); }
    recursor_val const & to_recursor_val() const { lean_assert(is_recursor()); return static_cast<recursor_val const &>(to_val()); }
    quot_val const & to_quot_val() const { lean_assert(is_quot()); return static_cast<quot_val const &>(to_val()); }

    expr get_value(bool DEBUG_CODE(allow_opaque)) const {
        lean_assert(has_value(allow_opaque));
        if (is_theorem())
            return to_theorem_val().get_value();
        else
            return static_cast<expr const &>(cnstr_get_ref(to_val(), 1));
    }
    expr get_value() const { return get_value(false); }
};

inline optional<constant_info> none_constant_info() { return optional<constant_info>(); }

static_assert(static_cast<unsigned>(declaration_kind::Axiom) == static_cast<unsigned>(constant_info_kind::Axiom), "declaration vs constant_info tag mismatch");
static_assert(static_cast<unsigned>(declaration_kind::Definition) == static_cast<unsigned>(constant_info_kind::Definition), "declaration vs constant_info tag mismatch");
static_assert(static_cast<unsigned>(declaration_kind::Theorem) == static_cast<unsigned>(constant_info_kind::Theorem), "declaration vs constant_info tag mismatch");

void initialize_declaration();
void finalize_declaration();

namespace declaration_detail {
inline reducibility_hints const & opaque_hints() {
    static reducibility_hints * r = []() {
        auto * h = new reducibility_hints(reducibility_hints::mk_opaque());
        mark_persistent(h->raw());
        return h;
    }();
    return *r;
}

inline object * dummy_declaration() {
    static object * r = []() {
        object * d = mk_axiom(name(), names(), expr()).raw();
        inc(d);
        mark_persistent(d);
        return d;
    }();
    return r;
}
}

inline declaration::declaration():object_ref(declaration_detail::dummy_declaration(), true) {}

inline constant_info::constant_info():object_ref(declaration_detail::dummy_declaration(), true) {}

inline reducibility_hints const & constant_info::get_hints() const {
    if (is_definition())
        return static_cast<reducibility_hints const &>(cnstr_get_ref(to_val(), 2));
    else
        return declaration_detail::opaque_hints();
}
}
