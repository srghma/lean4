-- 1. Define the abbreviation
abbrev hidden {α : Sort u} {a : α} := a

-- 2. A theorem with a long, cluttered equation
theorem complex_goal (x : Nat) : (x + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = x + 10 := by
  -- Look at the Infoview (tactic state) on the right.
  -- ⊢ x + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = x + 10

  -- 3. Use `change`, but specify the implicit argument `a` by name:
  change (hidden (α := Nat) (a := x + 1 + 1 + 1 + 1 + 1)) + 1 + 1 + 1 + 1 + 1 = x + 10

  -- Look at the Infoview now. It should display:
  -- ⊢ hidden + 1 + 1 + 1 + 1 + 1 = x + 10

  sorry
