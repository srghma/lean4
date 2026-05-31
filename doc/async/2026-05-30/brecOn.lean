-- =========================================================================
-- COMPREHENSIVE GUIDE TO LEAN 4 RECURSORS AND ELIMINATORS
-- =========================================================================

-- We define three inductive types to demonstrate different behaviors:
-- 1. A standard recursive type (MyNat)
-- 2. A non-recursive type (MyPair) to show constraints
-- 3. A nested inductive type (NestedTree) to show binductionOn

-- -------------------------------------------------------------------------
-- Type Definitions
-- -------------------------------------------------------------------------

-- A standard recursive type: Unary Natural Numbers
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

-- A non-recursive product type
structure MyPair (α β : Type) where
  fst : α
  snd : β

-- A nested inductive type (using the standard List)
inductive NestedTree where
  | leaf : NestedTree
  | node : List NestedTree → NestedTree


-- =========================================================================
-- PART 1: Types of rec and recOn Operators in Lean
-- =========================================================================

open MyNat

-- -------------------------------------------------------------------------
-- 1.1 T.rec (The Standard Recursor)
-- -------------------------------------------------------------------------
-- The primitive recursor in Lean's core type theory. It enforces structural
-- induction. It expects:
--   - motive: The property or return type to compute.
--   - Base case: What to return for `zero`.
--   - Step case: A function taking the predecessor and the accumulated result.
--   - Major premise: The inductive value itself.
-- -------------------------------------------------------------------------

#check @MyNat.rec
-- Type: ∀ {motive : MyNat → Sort u},
--         motive zero →
--         (∀ (n : MyNat), motive n → motive (succ n)) →
--         ∀ (n : MyNat), motive n

def double (n : MyNat) : MyNat :=
  MyNat.rec (motive := fun _ => MyNat)
    zero                                         -- Base Case
    (fun _prev accum => succ (succ accum))       -- Step Case (accum is the IH)
    n                                            -- Major Premise

#eval double (succ (succ zero)) -- Returns: 4 (represented as 4 succs)


-- -------------------------------------------------------------------------
-- 1.2 T.recOn (Recursor with Swapped Arguments)
-- -------------------------------------------------------------------------
-- Computationally identical to `T.rec`, but the major premise is placed first.
-- This is designed for dot notation (`x.recOn`).
-- -------------------------------------------------------------------------

#check @MyNat.recOn

def doubleOn (n : MyNat) : MyNat :=
  n.recOn (motive := fun _ => MyNat)
    zero                                         -- Base Case
    (fun _prev accum => succ (succ accum))       -- Step Case

#eval doubleOn (succ zero) -- Returns: 2


-- -------------------------------------------------------------------------
-- 1.3 T.casesOn (Non-recursive Case Analysis)
-- -------------------------------------------------------------------------
-- An eliminator for single-step pattern matching without induction.
-- Notice that the step case does NOT receive an accumulated induction hypothesis.
-- -------------------------------------------------------------------------

#check @MyNat.casesOn

def isZero (n : MyNat) : Bool :=
  MyNat.casesOn (motive := fun _ => Bool) n
    true                                         -- Case: zero
    (fun _prev => false)                         -- Case: succ (no induction hypothesis here)


-- -------------------------------------------------------------------------
-- 1.4 T.brecOn (Course-of-Values Recursor)
-- -------------------------------------------------------------------------
-- Unlike `T.rec`, which only provides the inductive result for the immediate
-- sub-term, `T.brecOn` provides a table containing the recursive results for
-- all strictly smaller sub-terms (nested at any depth).
-- -------------------------------------------------------------------------

#check @MyNat.brecOn


-- -------------------------------------------------------------------------
-- 1.5 T.binductionOn (Simultaneous Induction for Nested/Mutual Types)
-- -------------------------------------------------------------------------
-- Generated for nested or mutual inductive types. It facilitates simultaneous
-- induction over the main type and the nested/mutual container (like `List`).
-- -------------------------------------------------------------------------

#check @NestedTree.binductionOn
-- This recursor allows proving a property for NestedTree and, at the same
-- time, proving a corresponding property for List NestedTree.


-- =========================================================================
-- PART 2: The brecOn Family (Course-of-Values Recursion)
-- =========================================================================

-- -------------------------------------------------------------------------
-- 2.1 T.below (The History/Memoization Table)
-- -------------------------------------------------------------------------
-- For a value `t : T`, `t.below` is an iterated dependent product (PProd).
-- It stores the evaluations of the motive for every strict sub-term of `t`.
-- -------------------------------------------------------------------------

#check @MyNat.below
-- Motive-dependent type that packages the results of smaller terms.

-- Let's inspect the type of `.below` for zero and succ:
-- - zero.below is empty (represented by PUnit)
-- - (succ m).below is PProd (motive m) (m.below)


-- -------------------------------------------------------------------------
-- 2.2 T.brecOn (Usage Example)
-- -------------------------------------------------------------------------
-- Here we implement integer division by 2 (`half`).
-- This requires accessing the result of `m` when we are at `succ (succ m)`.
-- This is structural recursion but NOT primitive recursion (it jumps two steps).
-- -------------------------------------------------------------------------

noncomputable def half (n : MyNat) : MyNat :=
  n.brecOn (motive := fun _ => MyNat) (fun k table =>
    match k, table with
    | zero, _ => zero
    | succ zero, _ => zero
    -- table for succ (succ m) has type:
    --   PProd (motive (succ m)) (PProd (motive m) (m.below))
    -- We extract `half_m` which is the pre-computed value for `m`.
    | succ (succ m), PProd.mk _ (PProd.mk half_m _) => succ half_m
  )

#eval half (succ (succ (succ (succ zero)))) -- 4 / 2 = 2


-- -------------------------------------------------------------------------
-- 2.3 T.brecOnTable (Internal Primitive Helper)
-- -------------------------------------------------------------------------
-- Under the hood, Lean uses a helper to construct the `below` table.
-- It computes the final value along with the history table for sub-components.
-- Lean defines this internally. We can check its presence in the environment:
-- -------------------------------------------------------------------------

#check @MyNat.brecOnTable


-- =========================================================================
-- PART 3: Key Constraints and Rules for brecOn
-- =========================================================================

-- -------------------------------------------------------------------------
-- 3.1 Constraint: Recursive Types Only
-- -------------------------------------------------------------------------
-- Non-recursive types like `MyPair` (or the standard `Prod`) do not have
-- a `.brecOn` recursor or `.below` type because they do not contain
-- recursive sub-terms to store in a table.
-- -------------------------------------------------------------------------

-- The following lines will compile and show that rec/recOn/casesOn exist:
#check @MyPair.rec
#check @MyPair.recOn
#check @MyPair.casesOn

-- However, uncommenting either of the following lines will cause a compile
-- error because no `.below` or `.brecOn` is generated for non-recursive types:

-- #check @MyPair.below
-- #check @MyPair.brecOn


-- -------------------------------------------------------------------------
-- 3.2 Constraint: Noncomputability of Manual brecOn
-- -------------------------------------------------------------------------
-- Functions defined manually using `T.brecOn` in proofs/definitions are
-- generally marked `noncomputable`.
--
-- This is because the Lean compiler generates VM/C code from the original
-- pattern-matching equations directly, rather than executing the complex
-- proof terms produced by `brecOn`.
--
-- (Note that we marked our `half` function as `noncomputable` above.)
-- -------------------------------------------------------------------------
