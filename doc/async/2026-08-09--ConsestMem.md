<details>
<summary>how to use List.Mem?</summary>


To force Mem to match only the first (leftmost) occurrence of an element—exactly like your type-checking Lookup rule—you need how to be an inequality proof: a ≠ b. 🎯

---

### 1. How to use standard Mem 🔍

With standard Mem, tail allows skipping any element, even if it matches a.

<details>
<summary><b>View Examples</b> 💻</summary>

```lean
-- Proving '2' is in [1, 2, 3]:
def ex1 : Mem 2 [1, 2, 3] :=
  Mem.tail 1 (Mem.head [3])

-- With duplicates [2, 2], there are TWO valid proofs for '2':
def proof1 : Mem 2 [2, 2] := Mem.head [2]              -- finds 1st '2'
def proof2 : Mem 2 [2, 2] := Mem.tail 2 (Mem.head [])  -- finds 2nd '2'
```

</details>

---

### 2. Fixing how to force finding the first occurrence 🛠️

To make Mem deterministic (so proof2 above becomes impossible), how must be a ≠ b (or b ≠ a).

```lean
inductive FirstMem (a : α) : List α → Prop where
  | head (as : List α) : FirstMem a (a :: as)
  | tail {b : α} {as : List α} (h : a ≠ b) : FirstMem a as → FirstMem a (b :: as)
```

#### Why this works 💡

 * **head**: Matches if a is at the front of the list.
 * **tail**: Only steps deeper into b :: as if you can prove a ≠ b.

If the head of the list equals a, you cannot use tail because you would need to prove a ≠ a, which is a contradiction.

---

### 3. Comparison with your Lookup judgment 📊

| Concept | Lookup (Context variable lookup) | FirstMem (First list occurrence) |
|---|---|---|
| Found target | z : Lookup (Γ , x : t) x t | head : FirstMem a (a :: as) |
| Step past non-target | s : x ≠ y → Lookup Γ x t → ... | tail : a ≠ b → FirstMem a as → ... |

---

### 4. Usage Example 🧪

<details>
<summary><b>View Usage Example</b> 📜</summary>

```lean
-- Valid: 2 ≠ 1 allows stepping past 1 to find 2
def ex_first : FirstMem 2 [1, 2, 2] :=
  FirstMem.tail (by decide) (FirstMem.head [2])

-- IMPOSSIBLE: Trying to skip the first '2' in [2, 2] fails:
-- FirstMem.tail (h : 2 ≠ 2) (FirstMem.head [])
--              ^^^^^^^^^^ No proof exists for 2 ≠ 2!
```

By adding a ≠ b, FirstMem a l has at most one unique proof for any given list l.

</details>

---

# LastMem Relation 📍

To create a LastMem relation that only matches the rightmost (last) occurrence of an element in a list, you have two primary approaches:

### Approach 1: Reversing the list (Simplest) 🔄

The cleanest definition reuses our previous FirstMem logic by reversing the list. The last occurrence in a list l is simply the first occurrence in l.reverse:

```lean
def LastMem (a : α) (l : List α) : Prop :=
  FirstMem a l.reverse
```

---

### Approach 2: Direct Inductive Definition (Structural) 🏗️

If you want an inductive judgment defined directly on lists from left to right without using reverse, the logic requires two cases:

 * **head**: a is at the head, AND a does not appear anywhere in the rest of the list (as).
 * **tail**: Step into the tail if a is somewhere in as (regardless of whether a = b).

```lean
inductive LastMem (a : α) : List α → Prop where
  /-- a is at the head, and it NEVER appears again in as -/
  | head (as : List α) (h_not : a ∉ as) : LastMem a (a :: as)

  /-- a is in the tail (we skip b, even if b == a) -/
  | tail (b : α) {as : List α} (h_tail : LastMem a as) : LastMem a (b :: as)
```

<details>
<summary><b>Why this works</b> 💡</summary>

 * In [2, 2], can we pick the first 2 using head?
   No, because head demands 2 ∉ [2], which is false! You are forced to use tail.
 * On the second 2, 2 ∉ [] holds, so head succeeds.

</details>

---

### Comparison of standard Mem, FirstMem, and LastMem ⚖️

For l = [2, 2]:

| Relation | Rules for [2, 2] | Valid Proofs |
|---|---|---|
| Mem 2 [2, 2] | head or tail unconditionally | 2 proofs (index 0 and 1) |
| FirstMem 2 [2, 2] | tail requires 2 ≠ 2 (Impossible) | 1 proof (index 0 only) |
| LastMem 2 [2, 2] | head requires 2 ∉ [2] (Impossible) | 1 proof (index 1 only) |

---

### Usage Example 🚀

<details>
<summary><b>View LastMem Proof Example</b> 📜</summary>

```lean
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
```

</details>
</details>


<details>
<summary>littleOmega bigOmega in lean (big is impossible)</summary>

```lean
-- 1. Define T in Prop (impredicative type)
def T : Prop := ∀ (A : Prop), A → A

-- 2. Define ω₁ : T → T
theorem littleOmega : T → T := fun (x : T) => (x T) x

-- The polymorphic identity function (which has type T)
theorem idT : T := fun (A : Prop) (a : A) => a

-- Apply omega₁ to idT
#reduce littleOmega idT

-- Trying to make **Big Omega** (omega₁ applied to omega₁):
-- def bigOmega := littleOmega littleOmega   -- ❌ Type Error!

-- `Prop` is impredicative (you can quantify over all of `Prop` and land back in `Prop`,
-- which is what makes your `T` even expressible), but `Prop` itself lives in `Type`,
-- and `Type u` lives in `Type (u+1)` — the hierarchy never folds back on itself.
-- That asymmetry between "`Prop` quantifies over `Prop`" and "`Prop` is `Prop`" is exactly
-- what blocks **Big Omega**.

-- this works, but only `partial def` (not `theorem` or `partial theorem`)
partial def bigOmega : T := littleOmega bigOmega

-- ### Summary
-- * **Little $\omega$** ($\lambda x.\ x\ x$): Expressible as `omega₁ : T → T` in Lean because `Prop` is impredicative.
-- * **Big $\Omega$** ($\omega \, \omega$): **Impossible** to write in Lean because `omega₁` has type `T → T`, not `T`, preventing the infinite loop!
```

</details>

<details>
<summary>IsTallest</summary>

```lean
-- 1. Declare the Person structure
structure Person where
  name   : String
  height : Nat  -- height in centimeters, for example

-- 2. Define the IsTallest predicate
def IsTallest (x : Person) : Prop := ∀ (p : Person), x.height ≥ p.height

-- Create two instance persons
def Alice : Person := { name := "Alice", height := 180 }
def Bob   : Person := { name := "Bob",   height := 170 }

-- 'IsTallest Alice' is now a proposition (Prop)
#check IsTallest Alice
-- Output: IsTallest Alice : Prop

-- If we assume the universe of people consists only of Alice and Bob:
theorem alice_is_tallest (h : ∀ p : Person, p = Alice ∨ p = Bob) : IsTallest Alice := by
  intro p
  rcases h p with rfl | rfl
  · -- Case p = Alice
    exact Nat.le_refl 180
  · -- Case p = Bob
    exact Nat.le_of_lt (by decide)

```

</details>

<details>
<summary>Church Numbers and Booleans in Prop</summary>

```lean
-- ## 1. Impredicative Booleans (Bool)

def CBool : Prop := ∀ (A : Prop), A → A → A

theorem cTrue : CBool := fun (A : Prop) (t : A) (f : A) => t

theorem cFalse : CBool := fun (A : Prop) (t : A) (f : A) => f

theorem cNot (b : CBool) : CBool := b CBool cFalse cTrue

-- ## 2. Impredicative Natural Numbers (Nat)

def CNat : Prop := ∀ (A : Prop), (A → A) → A → A

theorem cZero : CNat := fun (A : Prop) (f : A → A) (x : A) => x

theorem cOne : CNat := fun (A : Prop) (f : A → A) (x : A) => f x

theorem cSucc (n : CNat) : CNat :=
  fun (A : Prop) (f : A → A) (x : A) => f (n A f x)

-- With impredicativity in Prop, the system folds in on itself

```

</details>

