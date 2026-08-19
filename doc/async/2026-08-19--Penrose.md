How to express "no algorithm can decide the word problem of semigroups" in lean?

```
-- A rigorous statement requires filtering for computable functions:
theorem semigroup_word_problem_undecidable : 
  ¬ ∃ (dec : FreeSemigroup α → FreeSemigroup α → Bool), 
    Computable dec ∧ -- This is the crucial restriction!
    ∀ u v, dec u v = true ↔ (u, v) ∈ CongruenceClosure 
R :=
```

Is this correct?

or this
```
-- Sketch / template (fill in imports depending on your computability library)
-- variables / instances:
-- A : Type, [Fintype A], [DecidableEq A], [Encodable A]

/- R : finite list (or finset) of pairs of words (the relators).
   congruence_closure R u v  -- u and v are lists of A (words)
-/

theorem exists_finite_presentation_with_undecidable_word_problem :
  ∃ (A : Type) [Fintype A] [DecidableEq A] [Encodable A]
    (R : Finset (List A × List A)),
    ¬ ∃ (dec : (List A × List A) → Bool),
      Computable dec ∧
      ∀ (u v : List A), dec (u, v) = tt ↔ congruence_closure R u v
```

I think no? Did anyone formalize it already?

------


Short answer: no, not quite — and I couldn't find evidence this has been formalized in Lean/Mathlib (it exists in Coq).

## What's wrong with the draft

**1. `R` is silently universally quantified, which makes the statement false.**

Since you never bind `R`, Lean auto-binds it as an implicit `∀`. So the theorem as written claims: *for every relation `R`, the word problem for `⟨α | R⟩` is undecidable.* That's false — take `R = ∅` and you get the free semigroup, whose word problem is literal list equality, which is trivially decidable. Post/Markov's theorem is an **existence** claim: there is *some* finite alphabet and *some finite* `R` for which the word problem is undecidable. Finiteness of `R` is essential — if `R` is allowed to be an arbitrary (non-r.e.) relation you can cheat by encoding any undecidable set directly into `R`, which proves nothing interesting.

**2. `Bool` + `Computable` + `↔` is reinventing a wheel Mathlib already has.**

Mathlib's `Mathlib.Computability.Halting` defines exactly the notion you want:

```
def ComputablePred {α} [Primcodable α] (p : α → Prop) :=
  ∃ _ : DecidablePred p, Computable fun a => decide (p a)
```

and this is literally how the halting problem's undecidability is stated in Mathlib:

```
theorem ComputablePred.halting_problem (n : ℕ) :
    ¬ ComputablePred fun c : Nat.Partrec.Code => (c.eval n).Dom
```

That's your template. Using `ComputablePred` also gets you `Mathlib.Computability.Reduce` for free (many-one reducibility `≤₀`, `ComputablePred.computable_of_manyOneReducible`), which is how you'd actually *prove* the theorem — by reducing the halting problem to the word problem.

**3. `CongruenceClosure R` isn't a real Mathlib name.** The relevant thing is `Con.conGen` (smallest congruence containing a relation, needs `[Mul α]`, which `FreeSemigroup α` has), with underlying relation `ConGen.Rel`.

**4. `FreeSemigroup α` has no `Primcodable` instance off the shelf.** It's a structure `{ head : α, tail : List α }` (Mathlib's docs describe it as essentially nonempty lists over `α`), with `DecidableEq`, but you'll need to derive `Primcodable (FreeSemigroup α)` yourself via the equivalence to `α × List α` (`Primcodable.ofEquiv`), for a suitable `α` like `Fin n`.

## A corrected shape

```lean
theorem semigroup_word_problem_undecidable :
    ∃ (n : ℕ) (R : Finset (FreeSemigroup (Fin n) × FreeSemigroup (Fin n))),
      ¬ ComputablePred
          (fun p : FreeSemigroup (Fin n) × FreeSemigroup (Fin n) =>
            ConGen.Rel (fun x y => (x, y) ∈ R) p.1 p.2) := by
  sorry
```

The finite generating alphabet (`Fin n`) and finite `R` are inside the existential — that's the correct reading of "there's a finitely presented semigroup with undecidable word problem." (If you instead want to state the *contrapositive framing* you tried — "no algorithm decides the word problem, full stop" — you have to fix a specific `R` first, since as shown above the claim is only ever true for particular `R`, never for all `R`.)

## Has anyone formalized it?

I searched and didn't find a Lean or Mathlib formalization of the Post–Markov (semigroup) or Novikov–Boone (group) word-problem undecidability theorem — no matching file in Mathlib's computability/group-theory folders, no Zulip thread turning it up, no paper announcing it. It does exist in Coq: the Saarbrücken "Coq Library of Undecidability Proofs" (Forster, Larchey-Wendling, et al.) formalizes undecidability of the Post correspondence problem and string-rewriting/semi-Thue systems, from which the semigroup word problem follows.

This is a real caveat on my end: I'm working from search results plus general familiarity with Mathlib's computability library, not an exhaustive index, and a negative existence claim ("nobody has done X") is inherently hard to verify completely — it's worth double-checking the [Mathlib4 repo](https://github.com/leanprover-community/mathlib4) and the [Lean Zulip](https://leanprover.zulipchat.com) yourself before concluding it's genuinely unformalized.

Worth knowing going in: this would be a substantial project, not a quick lemma. The real content is constructing an explicit finite presentation and a many-one reduction from the halting problem (à la Post's construction via Turing machines, or Markov's), which is genuinely hard combinatorics to formalize — comparable in scope to the PCP-undecidability development in Coq, which was a multi-chapter thesis.

------


Based on the Penrose book , here are the definitions and explanations for the requested terms:
Recursively Enumerable Set
 * Definition: A set whose elements can be generated one after the other by some algorithm (possibly with repetitions).
 * Key characteristic: For an element in the set, you can algorithmically determine or find that it is in the set by allowing the algorithm to run until it encounters that element.
Recursive Set
 * Definition: A set that has the property that both the set itself and its complementary set (the set of natural numbers not in the set) are recursively enumerable.
 * Key characteristic: You can algorithmically decide for any given natural number whether or not it belongs to the set, because you have algorithms to test both the set and its complement.
Non-Recursively Enumerable Set
 * Definition: A set whose elements cannot be generated or enumerated by any algorithm.
 * Key characteristic: Examples include the set of all true propositions (T) or the set of false S(n) propositions, which are vastly more complex and cannot be generated algorithmically.
Non-Recursive Set
 * Definition: A set that lacks the property of being recursive. This category can include sets that are recursively enumerable but whose complements are not recursively enumerable (meaning you can algorithmically verify elements in the set, but cannot guarantee a decision for elements not in the set), as well as sets that are not recursively enumerable at all.
 * Key characteristic: Non-recursive sets are essentially complicated in a way that defies all attempts at systematization, meaning there is no general algorithmic way to decide whether or not an element belongs to the set.


What is lean definitions then for RE set, non RE, R set, non R set (with and without mathlib)

He says also

> Let us now return to our earlier discussion of the Mandelbrot set. I am going to assume, for the purposes of an illustration, that the Mandelbrot set is, in some appropriate sense, non-recursive. Since its complement is recursively enumerable, this would mean that the set itself would not be recursively enumerable. I think that it is likely that the form of the Mandelbrot set has some lessons to teach us as to the nature of non-recursive sets and non-recursive mathematics.

But currently, was it proved for Mandelbrot set that

1. MS is RE or not RE?
2. Complement of MS is RE or not RE?
3. MS is R?


Proved in lean? Proved in COQ? Proved informally? Proved by Blum?

------


## Lean definitions

### With mathlib

Mathlib's `Mathlib.Computability.Halting` already has almost exactly Penrose's four notions, for predicates `p : α → Prop` on a `Primcodable` type (in particular `α = ℕ`):

```lean
-- RE set
def RePred {α} [Primcodable α] (p : α → Prop) : Prop :=
  Partrec fun a => Part.assert (p a) fun _ => Part.some ()
-- "p is the domain of some partial computable function"

-- Recursive set (R)
def ComputablePred {α} [Primcodable α] (p : α → Prop) : Prop :=
  ∃ _ : DecidablePred p, Computable fun a => decide (p a)
-- "p has a total computable characteristic function"
```

Non‑RE and non‑R are just the negations, there's no separate primitive:

```lean
def NonRePred (p : α → Prop) : Prop := ¬ RePred p
def NonRecursivePred (p : α → Prop) : Prop := ¬ ComputablePred p
```

Post's theorem — exactly the fact Penrose is using — is already proved:

```lean
theorem ComputablePred.computable_iff_re_compl_re {p : α → Prop} :
    ComputablePred p ↔ RePred p ∧ RePred fun a => ¬ p a
```

i.e. **R ⟺ RE(p) ∧ RE(pᶜ)**, and mathlib even has the halting problem as the canonical witness of non‑R/non‑REᶜ:

```lean
theorem ComputablePred.halting_problem_re (n) :
    RePred fun c => (c.eval n).Dom
theorem ComputablePred.halting_problem (n) :
    ¬ ComputablePred fun c => (c.eval n).Dom
theorem ComputablePred.halting_problem_not_re (n) :
    ¬ RePred fun c => ¬ (c.eval n).Dom
```

The last one is literally "the complement of the halting set is not RE" — the discrete analogue of what Penrose speculates about M.

### Without mathlib

This is the more interesting question, because Lean's *core* type theory has no built‑in notion of "undecidable." Every function you can write as a total Lean term is, by construction, computable in the type‑theoretic sense — there's no way to internally express "no algorithm computes this" without first fixing an explicit, closed model of computation and quantifying over *codes* for programs in that model, then defining semantics via an interpreter (usually `Part`-valued, to allow non‑termination).

So "Lean without mathlib" really means: reimplement the computability library. The minimal ingredients:

1. An inductive type of program codes, e.g. Carneiro's `Nat.Partrec.Code` (built from zero/succ/pairing + composition/prec/rfind), or a Turing‑machine/register‑machine encoding.
2. A `Part ℕ`-valued interpreter `eval : Code → ℕ →. ℕ`.
3. Then:

```lean
def RE (p : ℕ → Prop) : Prop := ∃ c : Code, ∀ n, p n ↔ (eval c n).Dom
def R  (p : ℕ → Prop) : Prop := RE p ∧ RE (fun n => ¬ p n)
def NonRE  (p : ℕ → Prop) : Prop := ¬ RE p
def NonR   (p : ℕ → Prop) : Prop := ¬ R p
```

That's essentially what mathlib's `RePred`/`ComputablePred` unfold to once you strip the `Primcodable` typeclass machinery — mathlib isn't doing anything conceptually different, it's just packaging the μ‑recursive‑function model (Mario Carneiro's formalization, arXiv:1810.08380) behind those definitions and adding hundreds of closure lemmas.

**Coq/Rocq** has the same core issue and no library‑standard equivalent, but there is a well‑known external development: the **Coq Library of Undecidability Proofs** (Forster–Kunze et al., `coq-library-undecidability`), which defines essentially the same pair:

```coq
Definition enumerable {X} (p : X -> Prop) :=
  exists f : nat -> option X, forall x, p x <-> exists n, f n = Some x.
Definition decidable {X} (p : X -> Prop) :=
  exists f : X -> bool, forall x, p x <-> f x = true.
```

with `decidable p ↔ enumerable p ∧ enumerable (compl p)` proved as their Post's‑theorem analogue, and the halting problem for a chosen model (Turing machines, μ-recursive functions, or the call-by-value λ-calculus L) as the canonical non‑decidable/non‑co‑enumerable witness. Conceptually identical to the Lean picture.

## The Mandelbrot set: what's actually proved

Here Penrose is more careful than he's usually given credit for — he explicitly says "I am going to *assume*, for the purposes of an illustration," and that hedge turns out to be load‑bearing.

**Complement of M — settled.** ℂ∖M is a computably enumerable (equivalently: computable, in the sense of computable analysis) open set. This follows from the standard escape‑time algorithm: for any c ∉ M, iterating z ↦ z²+c will eventually produce |z_n| > 2, a finite certificate. Hertling's work shows that the exterior of the Mandelbrot set, the boundary of the Mandelbrot set, and the hyperbolic components satisfy certain natural computability conditions.

**Is M itself RE, and is M recursive — open.** This is the part where the popular‑science summaries (which even claim Hertling "proved M is not recursively computable") overstate the actual theorem. What Hertling (2005, *Math. Logic Quarterly*) actually proved is conditional: the two-sided distance function of the Mandelbrot set is computable if the famous hyperbolicity conjecture is true (density of hyperbolicity — every component of the interior of M is hyperbolic — a conjecture still open in complex dynamics itself). A separate survey summarizing the state of the art (arXiv:cs/0604003, "Hypercomputing the Mandelbrot Set?") lays out a table of the various computability models and, for essentially every reasonable model (Turing‑computability over ℚ, computable analysis à la Brattka–Weihrauch), the Mandelbrot‑set entry is a bare "?" — the author is not aware of a current result implying non-computability of the rational Mandelbrot set, even though one would cautiously expect it. Under the Blum–Shub–Smale model over ℝ it's actually a firm "no" (BSS‑decidability fails for essentially trivial reasons tied to exact real equality being undecidable in that model), but that's a much cruder/different notion than "recursive" in the sense Penrose and mathlib mean.

So, precisely:

1. **Is M RE?** — Open/unproven. Not established either way.
2. **Is ℂ∖M RE?** — Yes, proved (Hertling 2005, formalizing the classical escape‑time argument).
3. **Is M recursive?** — Open, unproven unconditionally. Known conditionally: hyperbolicity conjecture ⟹ M computable (Hertling 2005). No proof of non‑recursiveness exists.

**On Blum:** Blum, Shub and Smale's 1993 book *Complexity and Real Computation* supplies the BSS model in which these questions are even posable, and is the correct citation for that framework — but the claim sometimes attributed to them that "the Mandelbrot set is not Turing computable" is not a theorem about the sense of "computable" Penrose is using (RE/recursive over the naturals via a rational‑coordinate encoding); it's, at best, a statement about non-decidability in the BSS real-number model, which is a different and in some ways much weaker/trivial obstruction. Treat that specific claim in secondary sources with caution.

**Formalization status:** I found no evidence of any Lean or Coq/Rocq formalization of Mandelbrot‑set computability — unsurprising, since it's an unresolved research question in computable analysis/complex dynamics resting on continuum‑level machinery (computable analysis over ℂ, hyperbolic‑component theory) well beyond what mathlib's `Computability` library (which is essentially discrete, ℕ‑based recursion theory) or the Coq undecidability library currently cover. It's proved neither informally in full (only conditionally, by Hertling) nor in any proof assistant.


-----------


Penrose tells that for 1st list of rules there is a general algorithm to find if two words are equal and no general algorithm to find if two words are not equal ?



But rules of Gardner are different? there is no general algorithm to find if two words are equal and no general algorithm to find if two words are not equal ?



\begin{aligned} 1.\ \text{AH} &= \text{HA} \\ 2.\ \text{OH} &= \text{HO} \\ 3.\ \text{AT} &= \text{TA} \\ 4.\ \text{OT} &= \text{TO} \\ 5.\ \text{TAI} &= \text{IT} \\ 6.\ \text{HOI} &= \text{IH} \\ 7.\ \text{THAT} &= \text{ITHT} \end{aligned}



Correct? Why so? In lean



For 1st rules how to prove "there exists general algorithm to find if two words are equal" ?



For 1st rules how to prove "there not exists general algorithm to find if two words are not equal" ?



For Gardner rules how to prove "there not exists general algorithm to find if two words are equal" ?



For Gardner rules how to prove "there not exists general algorithm to find if two words are not equal" ?



Are Gardner rules Turing complete? How to prove?



For first rules there is a pattern that can use to find if two words are not equal (count of A+W+M is constant) and for Gardner too (count of T or H is constant). So in this case I see no difference. But Penrose tells they are completely different in power? Why?

------------


You made mistakes. Rules are bidirectional, so Your point about list of rules number 1 "Every rule strictly shortens the word" is wrong



2 I expected formalization of



For 1st rules how to prove "there exists general algorithm to find if two words are not equal" ?



To use mathlib



-- RE set

def RePred {α} [Primcodable α] (p : α → Prop) : Prop :=

  Partrec fun a => Part.assert (p a) fun _ => Part.some ()

-- "p is the domain of some partial computable function"



-- Recursive set (R)

def ComputablePred {α} [Primcodable α] (p : α → Prop) : Prop :=

  ∃ _ : DecidablePred p, Computable fun a => decide (p a)

-- "p has a total computable characteristic function"



theorem ComputablePred.computable_iff_re_compl_re {p : α → Prop} :

    ComputablePred p ↔ RePred p ∧ RePred fun a => ¬ p a



theorem ComputablePred.halting_problem_re (n) :

    RePred fun c => (c.eval n).Dom

theorem ComputablePred.halting_problem (n) :

    ¬ ComputablePred fun c => (c.eval n).Dom

theorem ComputablePred.halting_problem_not_re (n) :

    ¬ RePred fun c => ¬ (c.eval n

).Dom



I expected You will translate rules to use Fin instead of Char





Same formalization do for Gardner rules  "there not exists general algorithm to find if two words are not equal" since You claim difference between rules 1 and Gardner are in "two words are not equal" algorithm


-------

## Setup: Fin-based alphabets, both systems

```lean
import Mathlib.Computability.Halting
import Mathlib.Computability.Partrec
import Mathlib.Data.List.Basic

abbrev Word (n : ℕ) := List (Fin n)

-- Step includes BOTH directions of every rule explicitly — this is `Equiv`'s real content.
inductive Step (rules : List (Word n × Word n)) : Word n → Word n → Prop
  | fwd {pre suf l r} (h : (l, r) ∈ rules) : Step rules (pre ++ l ++ suf) (pre ++ r ++ suf)
  | bwd {pre suf l r} (h : (l, r) ∈ rules) : Step rules (pre ++ r ++ suf) (pre ++ l ++ suf)

def Equiv (rules : List (Word n × Word n)) : Word n → Word n → Prop :=
  Relation.ReflTransGen (Step rules)
```

**List 1**, alphabet as `Fin 12`:

```lean
-- 0=A 1=C 2=E 3=I 4=L 5=M 6=N 7=O 8=P 9=R 10=T 11=W
def rules1 : List (Word 12 × Word 12) :=
  [ ([2,0,10], [0,10]),         -- EAT = AT
    ([0,10,2], [0]),            -- ATE = A
    ([4,0,10,2,9], [4,7,11]),   -- LATER = LOW
    ([8,0,6], [8,3,4,4,7,11]),  -- PAN = PILLOW
    ([1,0,9,8], [5,2]) ]        -- CARP = ME
```

**Gardner/Tseitin**, alphabet as `Fin 5`:

```lean
-- 0=A 1=H 2=O 3=T 4=I
def rulesG : List (Word 5 × Word 5) :=
  [ ([0,1],[1,0]),         -- AH = HA
    ([2,1],[1,2]),         -- OH = HO
    ([0,3],[3,0]),         -- AT = TA
    ([2,3],[3,2]),         -- OT = TO
    ([3,0,4],[4,3]),       -- TAI = IT
    ([1,2,4],[4,1]),       -- HOI = IH
    ([3,1,0,3],[4,3,1,3]) ] -- THAT = ITHT
```

## The "not equal" side is always r.e. for a *decidable* Step relation

One thing that's true regardless of which rule list you use: `Step rules` has a decidable graph (finitely many rules, finitely many ways to split a finite word), so bounded-depth reachability is decidable, and unbounded search over depth gives `RePred` for the **equal** side, for free, on *both* lists:

```lean
theorem equal_is_re (rules : List (Word n × Word n)) (w1 : Word n) :
    RePred (fun w2 => Equiv rules w1 w2) := by
  sorry -- standard: Equiv rules w1 w2 ↔ ∃ k, reach_le k w1 w2 = true,
        -- reach_le decidable, so this is a Nat.rfind-style search ⇒ Partrec
```

This is the "always free" half from my earlier answer, now written in the target API. The whole question is what happens to the **complement**.

## List 1: getting `RePred (fun w2 => ¬ Equiv rules1 w1 w2)`

The honest route is via `computable_iff_re_compl_re`, and the honest route to that is exhibiting a *computable normal-form function*, which is exactly the confluence-completion work flagged above — not something I can wave past. Structurally:

```lean
-- (1) Completion work: rules1 as given isn't confluent when oriented
--     (EA = A is a real derived consequence not among the 5 original rules,
--     found via the EATE critical pair). A genuine proof needs a *completed*
--     finite rewriting system `rules1'` — the 5 rules plus every relation
--     forced by resolving critical pairs, iterated until no new ones appear —
--     together with a proof it terminates (e.g. length as the well-founded
--     measure) and is locally confluent (finite case-check over rules1's
--     critical pairs), then Newman's Lemma for global confluence.
axiom rules1_complete :
  { rules1' : List (Word 12 × Word 12) //
      Equiv rules1' = Equiv rules1 ∧
      -- terminating + locally confluent, hence (Newman) confluent
      True }

noncomputable def normalForm1 (w : Word 12) : Word 12 := sorry
  -- iterate rules1'.left-to-right reduction to a fixpoint; well-defined
  -- and computable given rules1_complete's termination witness

theorem normalForm1_correct (w1 w2 : Word 12) :
    normalForm1 w1 = normalForm1 w2 ↔ Equiv rules1 w1 w2 := sorry

theorem list1_decidable (w1 : Word 12) :
    ComputablePred (fun w2 => Equiv rules1 w1 w2) :=
  ⟨inferInstance, by
     have : Computable (fun w2 => decide (normalForm1 w1 = normalForm1 w2)) := sorry
     simpa [normalForm1_correct] using this⟩

theorem list1_not_equal_re (w1 : Word 12) :
    RePred (fun w2 => ¬ Equiv rules1 w1 w2) :=
  ((ComputablePred.computable_iff_re_compl_re).mp (list1_decidable w1)).2
```

The `sorry`s are exactly the completion/termination/confluence facts — genuine, finite, checkable-by-hand-or-computer casework for a 5-rule system, but I haven't carried the full completion out here (it's the "intelligence" Penrose alludes to, made literal: an actual Knuth–Bendix completion run).

## Gardner: `¬ RePred (fun w2 => ¬ Equiv rulesG w1 w2)`

Same target predicate, opposite answer, proved by reduction *from* the halting problem you pasted:

```lean
-- The actual mathematical content of Tseitin's 1958 paper: a computable
-- encoding of Turing-machine non-halting instances as pairs of Gardner-words,
-- such that non-halting corresponds exactly to inequality.
axiom tseitin_encode : Nat.Partrec.Code → ℕ → Word 5
axiom tseitin_encode_computable : Computable₂ tseitin_encode
axiom tseitin_correct (w1 : Word 5) :
    ∀ c n, ¬ (c.eval n).Dom ↔ ¬ Equiv rulesG w1 (tseitin_encode c n)

-- RE predicates are closed under pulling back along a computable map
theorem RePred.comp {p : Word 5 → Prop} (hp : RePred p)
    {f : α → Word 5} (hf : Computable f) : RePred (fun a => p (f a)) := by
  unfold RePred at hp ⊢
  exact hp.comp hf   -- Partrec.comp

theorem gardner_not_equal_not_re (w1 : Word 5) :
    ¬ RePred (fun w2 => ¬ Equiv rulesG w1 w2) := by
  intro h
  have h' : RePred (fun p : Nat.Partrec.Code × ℕ =>
      ¬ Equiv rulesG w1 (tseitin_encode p.1 p.2)) :=
    h.comp (f := fun p => tseitin_encode p.1 p.2)
      (tseitin_encode_computable.comp Computable.fst Computable.snd)
  have h'' : RePred (fun p : Nat.Partrec.Code × ℕ => ¬ (p.1.eval p.2).Dom) := by
    simpa [tseitin_correct w1] using h'
  exact absurd h'' (by
    -- uncurried version of ComputablePred.halting_problem_not_re
    sorry)
```

Everything here is mechanical *except* `tseitin_encode` / `tseitin_correct` — those two axioms are literally Tseitin's theorem. I'm marking them as `axiom` rather than pretending to derive them, because that derivation is the actual 1958 paper (translated in Nyberg-Brodda's arXiv:2401.11757 if you want the real construction to formalize against) — a genuine research-level reduction encoding Turing-machine tape configurations into these seven relations via the permutation rules 1–4 (used to shuffle a state marker into position) and the length-preserving rule 7 (which performs the actual transition step), which is precisely why it can't be produced by finding a clever letter-counting invariant the way `CARPET ≠ MEAT` could.

That contrast — `sorry`-able-by-hand completion for list 1 versus irreducibly-an-axiom-from-a-real-paper for Gardner's list — is the formal shape of "these are different in kind," not just different in how much casework they take.
