```lean
inductive Eval : ClosEnv n → Term n → Clos → Prop where
| var : γ i = .clos m δ → Eval δ m v → Eval γ (‵ i) v
| lam : Eval γ (ƛ m) (.clos (ƛ m) γ)
| ap : Eval γ l (.clos (ƛ n) δ) → Eval (δ ‚' .clos m γ) n v → Eval γ (l ⬝ m) v

mutual
  /-- Preserves your exact inductive declaration! -/
  inductive Eval : ClosEnv n → Term n → Clos → Prop where
  | var : EvalClos (γ i) v → Eval γ (‵ i) v
  | lam : Eval γ (ƛ m) (.clos (ƛ m) γ)
  | ap  : Eval γ l (.clos (ƛ n) δ) → Eval (δ ‚' .clos m γ) n v → Eval γ (l ⬝ m) v

  inductive EvalClos : Clos → Clos → Prop where
  | clos : Eval γ m v → EvalClos (.clos m γ) v
end
```

same as

```lean
inductive Box where
  | pack : Nat → Box

-- ====================================================================
-- BEFORE: Without mutual definitions & using list index lookup equality
-- ====================================================================
inductive EvalNumBefore : List Box → Nat → Nat → Prop where
  | num {env : List Box} {n : Nat} :
      EvalNumBefore env n n

  -- Requires TWO equality hypotheses: `h1` (lookup) and `h2` (unpacking)
  | var {env : List Box} {i : Nat} {b : Box} {n v : Nat}
      (h1 : env[i]? = some b := by rfl)
      (h2 : b = Box.pack n := by rfl) :
      EvalNumBefore [] n v → EvalNumBefore env i v


-- ====================================================================
-- AFTER: With mutual definitions & de Bruijn structural rules
-- ZERO equality hypotheses needed!
-- ====================================================================
mutual
  inductive EvalNumAfter : List Box → Nat → Nat → Prop where
  | num {env : List Box} {n : Nat} :
      EvalNumAfter env n n

  -- Variable 0: Evaluates head `b` of environment `(b :: env)`
  | var0 {env : List Box} {b : Box} {v : Nat} :
      EvalBoxAfter b v → EvalNumAfter (b :: env) 0 v

  -- Variable i + 1: Steps past `b'` into tail `env`
  | varSucc {env : List Box} {b' : Box} {i v : Nat} :
      EvalNumAfter env i v → EvalNumAfter (b' :: env) (i + 1) v

  inductive EvalBoxAfter : Box → Nat → Prop where
  | openBox {n v : Nat} :
      EvalNumAfter [] n v → EvalBoxAfter (Box.pack n) v
end


-- ====================================================================
-- SIDE-BY-SIDE EXAMPLE 1: Evaluating Index 0 in [Box.pack 42]
-- ====================================================================

-- BEFORE (Must manually pass `b := ...`, `n := ...`, and two `rfl` proofs):
example : EvalNumBefore [Box.pack 42] 0 42 := by
  apply EvalNumBefore.var (b := Box.pack 42) (n := 42) rfl rfl
  apply EvalNumBefore.num

-- AFTER (Zero arguments, zero `rfl` proofs needed!):
example : EvalNumAfter [Box.pack 42] 0 42 := by
  apply EvalNumAfter.var0
  apply EvalBoxAfter.openBox
  apply EvalNumAfter.num


-- ====================================================================
-- SIDE-BY-SIDE EXAMPLE 2: Evaluating Index 1 in [Box.pack 10, Box.pack 42]
-- ====================================================================

-- BEFORE:
example : EvalNumBefore [Box.pack 10, Box.pack 42] 1 42 := by
  apply EvalNumBefore.var /- (b := Box.pack 42) (n := 42) -/ rfl rfl
  apply EvalNumBefore.num

-- AFTER:
example : EvalNumAfter [Box.pack 10, Box.pack 42] 1 42 := by
  apply EvalNumAfter.varSucc
  apply EvalNumAfter.var0
  apply EvalBoxAfter.openBox
  apply EvalNumAfter.num
```
