<details>
  <summary>play.lean</summary>

```lean
-- import Mathlib.SetTheory.Ordinal.Basic
-- import Mathlib.SetTheory.Ordinal.Arithmetic
-- import Mathlib.SetTheory.Cardinal.Basic
-- import Mathlib.SetTheory.Cardinal.Aleph
-- import Mathlib.Tactic
import Mathlib
import Aesop


#check Ordinal
#check Ordinal.type
#check Ordinal.enum
#check Order.succ        -- Successor in Lean 4 order theory
-- #check Ordinal.succ
#check Ordinal.limitRecOn

-- #eval Cardinal.mk Bool   -- 2
#reduce Cardinal.mk Bool   -- 2
#check Cardinal.mk Bool   -- 2
-- #print Cardinal.mk Bool   -- 2

#check (· + · : Cardinal → Cardinal → Cardinal)
#check (· * · : Cardinal → Cardinal → Cardinal)
#check (· ^ · : Cardinal → Cardinal → Cardinal)

#check Cardinal.aleph
#check Cardinal.aleph0

example : Cardinal := Cardinal.aleph0

noncomputable example : Cardinal := Cardinal.aleph 3

example : Cardinal.aleph0 ≤ Cardinal.aleph 1 := by
  simp

#check Ordinal
#check Ordinal.type
#check Ordinal.enum
-- #check Ordinal.succ
#check Ordinal.limitRecOn

def o : Ordinal := 5
-- #eval o
#reduce o
#print o

example : Ordinal := Order.succ 5

#check Ordinal.omega

noncomputable example : Ordinal := Ordinal.omega 0

#check (· + · : Ordinal → Ordinal → Ordinal)
#check (· * · : Ordinal → Ordinal → Ordinal)
#check (· ^ · : Ordinal → Ordinal → Ordinal)

-- #eval (5 : Ordinal) + 7
#reduce (5 : Ordinal) + 7
-- #print (5 : Ordinal) + 7

-- #guard (5 : Ordinal) + (7 : Ordinal) = (13 : Ordinal)

noncomputable example : Ordinal := Ordinal.omega 0 + (3 : Ordinal)

noncomputable example : Ordinal := (3 : Ordinal) + Ordinal.omega 0

example : (3 : Ordinal) + Ordinal.omega 0 = Ordinal.omega 0 := by
  rw [Ordinal.omega_zero]
  exact Ordinal.natCast_add_omega0 3


example : Ordinal.omega 0 + (3 : Ordinal) ≠ Ordinal.omega 0 := by
  simp only [Ordinal.omega_zero, ne_eq, add_eq_left, OfNat.ofNat_ne_zero, not_false_eq_true]

#check Ordinal.card

noncomputable def κ : Cardinal :=
  Ordinal.card (Ordinal.omega 0)

noncomputable def α : Ordinal :=
  Cardinal.ord Cardinal.aleph0

#check Ordinal.omega          -- ω
-- #check Ordinal.succ α         -- α + 1
#check Cardinal.aleph0        -- ℵ₀
#check fun n => Cardinal.aleph (n : Nat)       -- ℵₙ
#check Cardinal.mk Bool          -- |α|
#check Cardinal.mk Nat          -- |α|

----------------

-- 1 + ω = ω
example : (1 : Ordinal) + Ordinal.omega0 = Ordinal.omega0 := by
  exact Ordinal.one_add_omega0

-- ω + 1 ≠ ω
example : Ordinal.omega0 + 1 ≠ Ordinal.omega0 := by
  simp only [ne_eq, add_eq_left, one_ne_zero, not_false_eq_true]

-- 2 * ω = ω (Stacking 2 elements ω times gives ω)
example : (2 : Ordinal) * Ordinal.omega0 = Ordinal.omega0 := by
  exact Ordinal.natCast_mul_omega0 Nat.zero_lt_two

-- ω * 2 = ω + ω ≠ ω (Stacking ω elements twice gives ω + ω)
example : Ordinal.omega0 * 2 = Ordinal.omega0 + Ordinal.omega0 := by
  exact Ordinal.mul_two Ordinal.omega0

example : Ordinal.omega0 * (2 : Ordinal) ≠ Ordinal.omega0 := by
  intro h
  have : Ordinal.omega0 + Ordinal.omega0 = Ordinal.omega0 := by
    rwa [← Ordinal.mul_two]
  simp_all only [ne_eq, Ordinal.omega0_ne_zero, not_false_eq_true, mul_eq_left₀, OfNat.ofNat_ne_one]

-------------

-- ℵ₀ + ℵ₀ = ℵ₀
example : Cardinal.aleph0 + Cardinal.aleph0 = Cardinal.aleph0 := by
  simp_all only [Cardinal.aleph0_add_aleph0]

-- ℵ₀ * ℵ₀ = ℵ₀
example : Cardinal.aleph0 * Cardinal.aleph0 = Cardinal.aleph0 := by
  simp_all only [Std.le_refl, Cardinal.mul_aleph0_eq]

-- Cantor's Theorem: c < 2^c for any cardinal
example (c : Cardinal) : c < 2 ^ c := by
  exact Cardinal.cantor c

-- ℵ₀ < ℵ₁
example : Cardinal.aleph0 < Cardinal.aleph 1 := by
  exact Cardinal.aleph0_lt_aleph_one

------------

-- The size of ω is ℵ₀
example : Ordinal.card Ordinal.omega0 = Cardinal.aleph0 := by
  exact Ordinal.card_omega0

-- The size of ω + 1 is STILL ℵ₀
example : Ordinal.card (Ordinal.omega0 + 1) = Cardinal.aleph0 := by
  simp

-- The initial ordinal of ℵ₀ is ω
example : Cardinal.ord Cardinal.aleph0 = Ordinal.omega0 := by
  exact Cardinal.ord_aleph0

-- The initial ordinal of ℵ₁ is greater than ω
example : Ordinal.omega0 < Cardinal.ord (Cardinal.aleph 1) := by
  rw [← Cardinal.ord_aleph0]
  exact Cardinal.ord_lt_ord.mpr Cardinal.aleph0_lt_aleph_one

-------------

-- ω^2 = ω * ω
example : Ordinal.omega0 ^ (2 : Ordinal) = Ordinal.omega0 * Ordinal.omega0 := by
  have h2 : (2 : Ordinal) = 1 + 1 := by norm_num
  rw [h2, Ordinal.opow_add, Ordinal.opow_one]

-- ω^ω is strictly larger than any ω^n for finite n
example (n : ℕ) : Ordinal.omega0 ^ (n : Ordinal) < Ordinal.omega0 ^ Ordinal.omega0 := by
  rw [Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0]
  exact Ordinal.natCast_lt_omega0 n

-- But the cardinality of ω^ω is STILL ℵ₀!
example : Ordinal.card (Ordinal.omega0 ^ Ordinal.omega0) = Cardinal.aleph0 := by
  rw [Ordinal.card_opow_eq_of_omega0_le_right Ordinal.one_lt_omega0 (le_refl _)]
  simp
```

</details>
