To force Mem to match only the first (leftmost) occurrence of an element—exactly like your type-checking Lookup rule—you need how to be an inequality proof: a ≠ b.
1. How to use standard Mem
With standard Mem, tail allows skipping any element, even if it matches a.
-- Proving '2' is in [1, 2, 3]:
def ex1 : Mem 2 [1, 2, 3] :=
  Mem.tail 1 (Mem.head [3])

-- With duplicates [2, 2], there are TWO valid proofs for '2':
def proof1 : Mem 2 [2, 2] := Mem.head [2]              -- finds 1st '2'
def proof2 : Mem 2 [2, 2] := Mem.tail 2 (Mem.head [])  -- finds 2nd '2'

2. Fixing how to force finding the first occurrence
To make Mem deterministic (so proof2 above becomes impossible), how must be a ≠ b (or b ≠ a).
inductive FirstMem (a : α) : List α → Prop where
  | head (as : List α) : FirstMem a (a :: as)
  | tail {b : α} {as : List α} (h : a ≠ b) : FirstMem a as → FirstMem a (b :: as)

Why this works
 * head: Matches if a is at the front of the list.
 * tail: Only steps deeper into b :: as if you can prove a ≠ b.
If the head of the list equals a, you cannot use tail because you would need to prove a ≠ a, which is a contradiction.
3. Comparison with your Lookup judgment
| Concept | Lookup (Context variable lookup) | FirstMem (First list occurrence) |
|---|---|---|
| Found target | z : Lookup (Γ , x : t) x t | head : FirstMem a (a :: as) |
| Step past non-target | s : x ≠ y → Lookup Γ x t → ... | tail : a ≠ b → FirstMem a as → ... |
4. Usage Example
-- Valid: 2 ≠ 1 allows stepping past 1 to find 2
def ex_first : FirstMem 2 [1, 2, 2] :=
  FirstMem.tail (by decide) (FirstMem.head [2])

-- IMPOSSIBLE: Trying to skip the first '2' in [2, 2] fails:
-- FirstMem.tail (h : 2 ≠ 2) (FirstMem.head [])
--              ^^^^^^^^^^ No proof exists for 2 ≠ 2!

By adding a ≠ b, FirstMem a l has at most one unique proof for any given list l.


To create a LastMem relation that only matches the rightmost (last) occurrence of an element in a list, you have two primary approaches:
Approach 1: Reversing the list (Simplest)
The cleanest definition reuses our previous FirstMem logic by reversing the list. The last occurrence in a list l is simply the first occurrence in l.reverse:
def LastMem (a : α) (l : List α) : Prop :=
  FirstMem a l.reverse

Approach 2: Direct Inductive Definition (Structural)
If you want an inductive judgment defined directly on lists from left to right without using reverse, the logic requires two cases:
 * head: a is at the head, AND a does not appear anywhere in the rest of the list (as).
 * tail: Step into the tail if a is somewhere in as (regardless of whether a = b).
inductive LastMem (a : α) : List α → Prop where
  /-- a is at the head, and it NEVER appears again in as -/
  | head (as : List α) (h_not : a ∉ as) : LastMem a (a :: as)

  /-- a is in the tail (we skip b, even if b == a) -/
  | tail (b : α) {as : List α} (h_tail : LastMem a as) : LastMem a (b :: as)

Why this works
 * In [2, 2], can we pick the first 2 using head?
   No, because head demands 2 ∉ [2], which is false! You are forced to use tail.
 * On the second 2, 2 ∉ [] holds, so head succeeds.
Comparison of standard Mem, FirstMem, and LastMem
For l = [2, 2]:
| Relation | Rules for [2, 2] | Valid Proofs |
|---|---|---|
| Mem 2 [2, 2] | head or tail unconditionally | 2 proofs (index 0 and 1) |
| FirstMem 2 [2, 2] | tail requires 2 ≠ 2 (Impossible) | 1 proof (index 0 only) |
| LastMem 2 [2, 2] | head requires 2 ∉ [2] (Impossible) | 1 proof (index 1 only) |
Usage Example
-- Proving '2' is the last member of [2, 1, 2]:

def ex_last : LastMem 2 [2, 1, 2] :=
  -- Step past first 2:
  LastMem.tail 2 (
    -- Step past 1:
    LastMem.tail 1 (
      -- Found last 2, and 2 ∉ []:
      LastMem.head [] (by decide)
    )
  )

