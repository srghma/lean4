```lean
inductive Dom : Type where
| nat : Dom 

abbrev reify : Dom → Type
| .nat => Nat

notation:65 " ⟦ " x " ⟧ " => reify x

inductive Expr : Dom → Type where
| quote {T} : ⟦ T ⟧ → Expr T
| add : Expr .nat → Expr .nat → Expr .nat

prefix:max " `` " => Expr.quote
infixl:65 " ⊕ " => Expr.add
prefix:30 " ⊢ " => Expr

-- 1. Disable `quotPrecheck` to prevent Lean from checking if `EvalsTo` already exists.
-- 2. Disable `hygiene` so that the notation dynamically resolves to the 
--    inductive type we are defining directly below.
set_option quotPrecheck false in
set_option hygiene false in
infixl:70 " ⇓ " => EvalsTo

inductive EvalsTo : {T : Dom} → ⊢ T → ⟦ T ⟧ → Type where
| VAL : ∀ {v}
      -------------------
      , (`` v) ⇓ v

| ADD : ∀ {e₁ e₂} {v₁ v₂}
      , e₁ ⇓ v₁ 
      → e₂ ⇓ v₂
      ----------------------------
      → (e₁ ⊕ e₂) ⇓ (v₁ + v₂)

#check EvalsTo.ADD
-- EvalsTo.ADD {e₁ e₂ : ⊢ Dom.nat} {v₁ v₂ : Nat} 
--   (a : e₁ ⇓ v₁) (a_1 : e₂ ⇓ v₂) : (e₁ ⊕ e₂) ⇓ v₁ + v₂
```
