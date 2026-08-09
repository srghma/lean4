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


```lean
inductive NotBad : Prop
  | wrap : (∀ (P : Prop), P → P) → NotBad

-- 2. Trying to pattern-match on Bad to return a Type FAILS:
def extractType (b : NotBad) : Type :=
  match b with
  | NotBad.wrap f => Nat

-- The field `(Type → Prop)` lives in Type 1, NOT Prop
inductive Bad2 : Prop
  | wrap : (Type 0 → Prop) → Bad2

-- ❌ THIS FAILS WITH `induction` failed: recursor `Bad2.casesOn` can only eliminate into `Prop`
-- def extractType2 (b : Bad2) : Type :=
--   match b with
--   | Bad2.wrap f => Nat

-- def extractType2 (b : Bad2) : Prop :=
--   Bad2.casesOn b (fun _ => True)

-- def extractType2 (b : Bad2) : Prop := by
--   cases b
--   exact True

-- def extractType2 (b : Bad2) : Prop :=
--   Bad2.casesOn (motive := fun _ => True) b (fun _ => True)

-- def extractType21 (b : Bad2) : Prop :=
--   match (motive := Bad2 → Prop) b with
--   | Bad2.wrap f => True

-- ✅ WORKS PERFECTLY!
theorem extractProof2 (b : Bad2) : True :=
  match b with
  | Bad2.wrap _f => True.intro
```

```lean
def T : Prop := ∀ (A : Prop), A → A
def idT : T := fun A a => a

inductive Bad : Prop where
  | wrap : T → Bad

def bad : Bad := Bad.wrap idT


def unwrap : Bad → T
  | Bad.wrap x => x

partial def noBad : Bad → False
  | Bad.wrap x => noBad (x Bad bad)     -- ⚠️
```
</details>

<details>
<summary>why bigOmega impossible? it would allow `fix (x -> x) = x`, which if `x` is `False` would construct `False` (Curry's paradox is a paradox in which an arbitrary claim F is proved from the mere existence of a sentence C that says of itself "If C, then F".)</summary>

Your diagnosis is exactly right, and it's worth seeing *why* it's right — it's not an accident of how you happened to write `T`, it's a theorem.

**The type mismatch is forced by consistency, not by bad luck.**

Lean's core calculus (the Calculus of Inductive Constructions) is strongly normalizing: every closed, well-typed term built in the trusted kernel — no `sorry`, no unsound axioms — reduces to a normal form in finitely many steps. This has been proven for the underlying calculus (Coquand–Werner and later refinements). So it's not that *this particular* `T` fails to give you a loop — nothing in safe Lean can loop. If Big Omega were constructible, strong normalization would be false, and the whole system would be broken.

**Why it would actually be catastrophic if it worked.**

Suppose you *could* get something of type `T → T` applied to itself to type-check — equivalently, suppose you had a genuine fixed-point operator `fix : (P → P) → P` for arbitrary `P : Prop`. Instantiate `P := False`:

```
fix (fun h => h) : False
```

`False → False` is trivially provable (`id`), so you'd derive `False` directly, with zero other assumptions. That's Curry's paradox. So the reason `omega₁ : T → T` can never be fed to itself isn't a syntactic accident — allowing it would let you prove anything at all. The type discipline you noticed *is* the thing standing between Lean and inconsistency.

**This is literally Girard's paradox, tamed.**

Martin-Löf's original 1971 type theory had `Type : Type`, and Girard showed it's inconsistent via essentially this self-application trick. Hurkens later compressed the argument to about 60 lines. The one ingredient those paradoxes need is a universe of propositions that contains *itself* as a member — `Prop : Prop`, or `Type : Type`. Lean/Coq deliberately avoid this: `Prop` is impredicative (you can quantify over all of `Prop` and land back in `Prop`, which is what makes your `T` even expressible), but `Prop` itself lives in `Type`, and `Type u` lives in `Type (u+1)` — the hierarchy never folds back on itself. That asymmetry between "`Prop` quantifies over `Prop`" and "`Prop` *is* `Prop`" is exactly what blocks Big Omega.

**So: is there another way, inside real Lean? No — provably not**, as long as you stay in the trusted, consistent core. This isn't "no one's found the trick yet"; the trick's existence is equivalent to Lean being unsound.

**What if you step outside the trusted core?** There are escape hatches, but none of them actually build Big Omega — they just opt out of the guarantee:

- `partial def bigOmega : T := littleOmega bigOmega` will elaborate (`T` is inhabited, e.g. by `idT`), but the kernel treats `partial` definitions as opaque constants — it never unfolds or reduces them; the only requirement for soundness is that the declared type is inhabited. So you get a black-box constant, not an actual self-reducing loop inside Lean's logic. `#reduce` on it won't show you an infinite regress; it'll just refuse to unfold.
- `sorry` invokes the explicit "admit" axiom and Lean will flag every downstream result as depending on an unproven assumption.
- An axiom that collapses the universe hierarchy (recreating `Type : Type`) reopens Girard/Hurkens' paradox and gets you straight to `False` — at which point "Big Omega" is moot, since `False` already proves everything, including a term of any type you like, trivially and uninterestingly.

So the honest summary: your `littleOmega : T → T` not being self-applicable is one of the load-bearing walls of the type theory. If you ever find a way around it in unmodified, axiom-clean Lean, you haven't found a clever encoding — you've found an inconsistency bug worth reporting.

</details>

<details>
<summary>how about other type theories? is it possible to implement bigOmega in hott? e.g. arend language. or redtt ? or cooltt? or some other type-system</summary>

# Does the extra cubical machinery in redtt/cooltt allow bigOmega?

No — this was an actual open problem, and it's now closed: normalization for univalent, Cartesian cubical type theory was proven, closing the last major open problem in the syntactic metatheory of cubical type theory, giving a reduction-free bijection between terms and normal forms, decidability of judgmental equality, and injectivity of type constructors. redtt and cooltt are both direct implementations of that theory. So even with the interval object, Kan composition, univalence-as-computation, and higher inductive types, the "every closed term reaches a normal form, nothing loops" guarantee still holds. More geometric structure doesn't buy you an escape hatch.

**Where a real, honest Big Omega *does* exist — by leaving the logic behind.**

- **Type-in-type used deliberately as a programming language, not a logic** — e.g. Lennart Augustsson's Cayenne, which has `Type : Type` on purpose. It's a known, accepted inconsistency: "a term of type A exists" stops meaning "A is true." That's the price, and Cayenne's designers pay it knowingly.
- **General recursion in `Type`/`Set`-land, not `Prop`** — every one of these systems (Lean, Arend, Agda, Idris) lets you write actually-looping *programs*, just not actually-looping *proofs*. Turn off the termination checker, or mark it `partial`/`unsafe`, and you get a function that spins forever at runtime — but it lives in a data universe with no claim to truth, so nothing breaks logically.
- **Untyped (or dynamically typed) lambda calculus** — `(λx. x x) (λx. x x)` loops immediately, precisely because there's no static discipline there to stand in the way. That's the one setting where Big Omega isn't just possible, it's the canonical example.

So: the type mismatch you found isn't a Lean-specific speed bump — it's one instance of a firewall every serious proof-relevant type theory needs, and different systems build that firewall at different points (predicativity, restricted elimination, or both), but none of the real ones leave a gap.
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

