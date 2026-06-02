-- -- need aux bc lean flatly rejects this with `well-founded recursion cannot be used, `loop` does not take any (non-fixed) arguments`
-- def loop (α : Type): α :=
--   loop α
-- termination_by sorry

-- 1. Define a helper function with a dummy argument that changes
def loopAux (α : Sort u) (n : Nat) : α :=
  loopAux α (n - 1)
termination_by n
decreasing_by sorry -- bc 0−1=0

-- 2. Define the exact function you wanted
def loop (α : Sort u) : α :=
  loopAux α 0

-- 3. Prove False using your loop function
theorem proof_of_false : False :=
  loop False

#print loop
