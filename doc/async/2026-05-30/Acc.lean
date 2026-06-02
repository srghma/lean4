namespace Test1

-- Define our relation: R y x means "y is the immediate predecessor of x"
abbrev R (y x : Nat) : Prop :=
  y + 1 = x

-- 1. Show that 0 is a base case (it is accessible because nothing precedes it)
theorem acc_zero : Acc R 0 := by
  apply Acc.intro
  -- grind only
  intro y h -- they give me h, but this h is impossible to construct
  -- h is the hypothesis: R y 0, which means y + 1 = 0.
  -- Since a successor (y + 1) can never equal 0 in Nat, this is a contradiction.
  -- apply Acc.intro
  -- intro y_1 h_1
  -- contradiction
  -- cases h
  -- nomatch h
  -- omega
  -- exact Nat.noConfusion h
  exact False.elim (Nat.succ_ne_zero y h)

def Test1.acc_zero : Acc R 0 := Acc.intro 0 fun y h => False.elim (Nat.succ_ne_zero y h)
#print Quot.sound
#print Eq.rec
#print acc_zero
-- #print acc_zero.match_1_1
-- #print acc_zero._proof_1_1
#print Nat.noConfusion
#print Nat.noConfusionType
#print noConfusion_of_Nat
#print Nat.ctorIdx_succ
#print Nat.ctorIdx

-- 2. Show that 1 is accessible
theorem acc_one : Acc R 1 := by
  apply Acc.intro
  intro y h
  -- h is the hypothesis: R y 1, which means y + 1 = 1 (or Nat.succ y = Nat.succ 0).
  -- This implies y = 0.
  have h_eq : y = 0 := by
    injection h
  -- Since y = 0, we can rewrite the goal "Acc R y" to "Acc R 0"
  rw [h_eq]
  exact acc_zero

-- 3. Show that 2 is accessible
theorem acc_two : Acc R 2 := by
  apply Acc.intro
  intro y h
  -- h is the hypothesis: R y 2, which means y + 1 = 2 (or Nat.succ y = Nat.succ 1).
  -- This implies y = 1.
  have h_eq : y = 1 := by
    injection h
  -- Rewrite the goal "Acc R y" to "Acc R 1"
  rw [h_eq]
  exact acc_one
end Test1

namespace Test2

-- We use the standard `<` relation (written as `(· < ·)` in binder notation)

theorem acc_zero : Acc (· < ·) 0 := by
  apply Acc.intro
  intro y h
  -- h : y < 0
  -- There is no natural number less than 0, so omega solves this by contradiction.
  contradiction

theorem acc_one : Acc (· < ·) 1 := by
  apply Acc.intro
  intro y h
  -- h : y < 1
  -- The only natural number less than 1 is 0.
  have h_eq : y = 0 := by omega
  rw [h_eq]
  exact acc_zero

theorem acc_two : Acc (· < ·) 2 := by
  apply Acc.intro
  intro y h
  -- h : y < 2
  -- Therefore, y must be either 0 or 1.
  have h_cases : y = 0 ∨ y = 1 := by omega
  cases h_cases with
  | inl h0 =>
    -- Case 1: y = 0
    rw [h0]
    exact acc_zero
  | inr h1 =>
    -- Case 2: y = 1
    rw [h1]
    exact acc_one
end Test2

namespace Test3

/--
This is a very important and interesting case. If we change the relation to "less than or equal to" (`≤`), **no natural number is accessible.**

### Why is this?

Recall that `Acc r x` means there are no infinite descending chains starting from `x`.

Because the relation is `≤` (which is reflexive, meaning `x ≤ x` is always true), we can easily build an infinite chain by just repeating the same number forever:
$$\dots \le 0 \le 0 \le 0 \le 0$$

Because we can loop on `0` indefinitely, `0` is no longer a base case. Since `0` is not accessible, `1` cannot be accessible either (since `0 ≤ 1`), and so on.

In Lean 4, we can actually prove that for any natural number $x$, having `Acc (· ≤ ·) x` leads to a contradiction.

### Explanation of the Proof
1. We assume `Acc (· ≤ ·) x` holds and aim to prove `False`.
2. We use induction on the `Acc` hypothesis. The induction step gives us:
   * A guarantee that any step we take "downwards" from `x` (any `y ≤ x`) is accessible (`h_acc`).
   * An induction hypothesis (`ih`) stating that for any such `y`, being accessible leads to `False`.
3. Since `x ≤ x` is true, we can choose `y = x`. This means:
   * `x` is accessible (from `h_acc`).
   * `x` being accessible leads to `False` (from `ih`).
4. Putting these two together yields `False`, completing the proof.

-/
theorem not_acc_le (x : Nat) : Acc (· ≤ ·) x → False := by
  intro h
  -- We perform induction on the accessibility hypothesis `h`
  induction h with
  | intro x h_acc ih =>
    -- x : Nat
    -- h_acc : ∀ y, y ≤ x → Acc (· ≤ ·) y
    -- ih    : ∀ y, y ≤ x → Acc (· ≤ ·) y → False (our induction hypothesis)

    -- Since x ≤ x is always true:
    have h_le : x ≤ x := Nat.le_refl x

    -- Applying `ih` directly to `h_le` gives us `False`
    exact ih x h_le

end Test3


namespace Test4

/--
An excellent way to see this is to define a relation on natural numbers where we can always go "downwards" infinitely.

A relation $R$ has no accessible elements if **every element has at least one predecessor**.

On `Nat`, we can define a relation `R y x` to mean `y = x + 1` (meaning `y` is the successor of `x`). Under this relation, the "predecessor" of any number $x$ is $x + 1$. Because every natural number has a successor, we can chain this infinitely:
$$\dots \to 3 \to 2 \to 1 \to 0$$

Since we can always find a larger number to continue the chain, no base case exists, and no element is accessible.

### Lean 4 Proof

Here is the definition of this relation and the proof that no element can have `Acc`:

### Why this works:
1. We set the predecessor of `x` to be `x + 1`. Since `(x + 1) = x + 1` is always true by definition (`rfl`), every `x` is guaranteed to have a predecessor.
2. The induction hypothesis `ih` says: "If you can prove any predecessor of `x` is accessible, it leads to a contradiction."
3. Since we can always construct the accessible predecessor `x + 1`, we trigger the contradiction, proving that `Acc R x` can never hold for any `x`.
-/
-- Define the relation: y is related to x if y is x + 1
def R (y x : Nat) : Prop :=
  y = x + 1

theorem not_acc_successor (x : Nat) : Acc R x → False := by
  intro h
  -- We perform induction on the accessibility of x
  induction h with
  | intro x h_acc ih =>
    -- x : Nat
    -- h_acc : ∀ y, R y x → Acc R y
    -- ih    : ∀ y, R y x → Acc R y → False

    -- For any x, its "predecessor" under R is x + 1.
    -- We show that R (x + 1) x holds (i.e., x + 1 = x + 1)
    have h_rel : R (x + 1) x := rfl

    -- Applying `ih` directly to `(x + 1)` and `h_rel` gives us `False`
    exact ih (x + 1) h_rel

end Test4
