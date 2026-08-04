open Std

variable {α : Type u} (r : α → α → Prop)

--------------------------------------------------------------------------------
-- 1. FORWARD DIRECTION: Total r (with Antisymm r) → Trichotomous r
--------------------------------------------------------------------------------

/-- `Total r` alone is sufficient to construct `Trichotomous r`. -/
instance trichotomous_of_total [hT : Total r] : Trichotomous r where
  trichotomous a b hab hba := by
    cases hT.total a b with
    | inl h => exact (hab h).elim
    | inr h => exact (hba h).elim

/-- `Total r` and `Antisymm r` together give `Trichotomous r`. -/
theorem trichotomous_of_total_and_antisymm [Total r] [Antisymm r] : Trichotomous r :=
  inferInstance

--------------------------------------------------------------------------------
-- 2. REVERSE DIRECTION: Trichotomous r + Refl r → Total r
--------------------------------------------------------------------------------

/-- For a reflexive relation (like `≤`), `Trichotomous r` implies `Total r`. -/
theorem total_of_trichotomous_and_refl [hTr : Trichotomous r] [hR : Refl r] : Total r where
  total a b := by
    by_cases hab : r a b
    · exact Or.inl hab
    · by_cases hba : r b a
      · exact Or.inr hba
      · have heq : a = b := hTr.trichotomous a b hab hba
        subst heq
        exact Or.inl (hR.refl a)

--------------------------------------------------------------------------------
-- 3. FULL IFF EQUIVALENCE (For Reflexive Relations)
--------------------------------------------------------------------------------

/-- For reflexive relations, `Total r` is logically equivalent to `Trichotomous r`. -/
theorem total_iff_trichotomous [Refl r] : Total r ↔ Trichotomous r :=
  ⟨fun _ => inferInstance, fun _ => total_of_trichotomous_and_refl r⟩
