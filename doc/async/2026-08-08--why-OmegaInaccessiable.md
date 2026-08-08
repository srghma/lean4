<details>
<summary>why use OmegaInaccessiable? is it used as fuel? why not not just "forall Nat -> proof that false is not possible"</summary>

In short: **`OmegaInaccessibles` is not fuel.** It is a **large cardinal axiom** (a hypothesis about mathematical consistency strength). 

Here is why `OmegaInaccessibles` is used, and why your alternative wouldn't work.

---

### 1. Why `OmegaInaccessibles` is needed

#### A. Gödel's Incompleteness Theorem
By Gödel's Second Incompleteness Theorem, any formal system capable of basic arithmetic (like Lean) **cannot prove its own consistency**. 

To prove that Lean cannot derive `False`, you must work in a system with **greater consistency strength** than Lean itself.

#### B. Modeling Lean's Universe Hierarchy
In Lean's type theory, types live in a hierarchy of universes:
* `Sort 0` (`Prop`)
* `Sort 1` (`Type 0`)
* `Sort 2` (`Type 1`)
* $\dots$
* `Sort n` (`Type (n-1)`)

To build a standard set-theoretic model (semantics) for Lean's type theory, each Lean universe `Sort n` is represented by a set-theoretic universe (a Grothendieck universe). In cardinal arithmetic:
* A set universe corresponds to an **inaccessible cardinal** $\kappa$.
* `Sort 0` needs $\kappa_0$.
* `Sort 1` needs a larger universe $\kappa_1 > \kappa_0$.
* `Sort n` needs $\kappa_n > \dots > \kappa_0$.

Because a Lean environment `env` can contain code referencing arbitrary universe levels $U \in \mathbb{N}$, constructing a single model $M$ that interprets all universe levels requires a strictly increasing sequence of infinitely many ($\omega$) inaccessible cardinals:
$$\kappa_0 < \kappa_1 < \kappa_2 < \dots$$

This is precisely what `OmegaInaccessibles` asserts:
```lean
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible
```

With this sequence $\kappa$, the proof can invoke `model_of_wf` to build a semantic model $M$ where every Lean type receives a mathematical set as its interpretation.

---

### 2. Why not `∀ Nat → proof that false is not possible`?

If you replaced `hlarge : OmegaInaccessibles` with:
```lean
(h : ∀ (U : Nat), ¬ ∃ e, env.HasType U [] e VExpr.false)
```
...the theorem statement would become:

> *"Assuming that no proof of `False` exists for any `U`, there is no proof of `False`."*

This would be a **trivial tautology** ($A \implies A$). It would prove nothing about Lean's type checker!

The goal of the `Lean4LeanModel` project is to prove **semantic soundness**:
$$\text{Large Cardinals (Set Theory Model)} \implies \text{Lean Type Checker is Sound (No Proof of False)}$$

---

### 3. How the proof actually works

Looking at the proof body in the snippet:

1. **`obtain ⟨assignment, M⟩ := model_of_wf hκ hi henv`**
   Uses the $\omega$ inaccessible cardinals to construct a model $M$ for the well-formed environment `env`.
2. **`have hmem := fundamental_hasType M ...`**
   Applies the **Fundamental Theorem of Logical Relations / Soundness**: If a Lean expression $e$ has type $T$ in Lean's typing rules, then the interpretation of $e$ in model $M$ must be an element of the interpretation of $T$.
3. **`rw [interp_false_eq_empty ...] at hmem`**
   Proves that the model interprets `VExpr.false` as the empty set $\emptyset$.
4. **`simp at hmem`**
   Since `hmem` says the interpretation of $e$ belongs to $\emptyset$, and no element can belong to the empty set, Lean derives a logical contradiction, completing the `¬ ∃ e, ...` proof.

   
</details>


<details>
<summary>is this idea with omega inaccessiables created by someone before? is it standard approach?
</summary>

**Yes, it is the standard, canonical approach in mathematical logic and computer-checked mathematics.** 

It was not invented for this pull request; rather, using $\omega$ (countably many) inaccessible cardinals to model a type theory with an infinite hierarchy of universes is a textbook method with a history spanning several decades.

---

### Key Milestones in the History of this Idea

1. **Alexander Grothendieck (1960s) – Grothendieck Universes**
   In category theory and algebraic geometry, Grothendieck introduced the concept of a *Grothendieck Universe* so mathematicians could talk about "the set of all small groups" without running into Russell's Paradox. In ZFC set theory, a Grothendieck universe is mathematically identical to a **strongly inaccessible cardinal** $\kappa$.

2. **Benjamin Werner (1997) – *Sets in Types, Types in Sets***
   - **Publication:** Benjamin Werner, "Sets in Types, Types in Sets", *Theoretical Aspects of Computer Software* (TACS 1997), LNCS 1281, pp. 530–546.
   - **URL:** https://doi.org/10.1007/BFb0014566
   Werner constructed set-theoretic models of the **Calculus of Inductive Constructions (CIC)**—the formal foundation underlying proof assistants like Coq and Lean. He established that to model a type theory with universe levels ($U_0, U_1, U_2, \dots$), set theory needs inaccessible cardinals to act as those universe levels.

3. **Bruno Barras (2010) – *Sets in Coq, Coq in Sets***
   - **Publication:** Bruno Barras, "Sets in Coq, Coq in Sets", *Journal of Formalized Reasoning*, Vol. 3, No. 1 (2010), pp. 29–48.
   - **URL:** https://doi.org/10.6092/issn.1972-5787/1695
   Barras extended this work by formalizing set-theoretic models of Coq inside Coq. He explicitly proved that modeling the Calculus of Constructions with an infinite universe hierarchy ($\text{CC}_\omega$) requires **an infinite sequence ($\omega$) of inaccessible cardinals**.

4. **Mario Carneiro (2019) – *The Type Theory of Lean***
   - **Publication:** Mario Carneiro, "The Type Theory of Lean", MS Thesis, Carnegie Mellon University (2019).
   - **URL:** https://github.com/digama0/lean-type-theory/releases/tag/v1.0
   In his CMU Master's thesis, Mario Carneiro (the primary author of Lean's `mathlib` and the `Lean4Lean` project in your PR) formalized the exact type theory of Lean 3 and proved its **equiconsistency** with ZFC set theory plus $\omega$ inaccessible cardinals (often denoted $\text{ZFC}_\omega$).

---

### Why is this the "Standard Approach"?

In dependent type theories like Lean, Coq, and Agda, universes are stratified:
* `Sort 0` ($\text{Prop}$)
* `Sort 1` ($\text{Type}_0$)
* `Sort 2` ($\text{Type}_1$)
* $\dots$
* `Sort n` ($\text{Type}_{n-1}$)

To build a set-theoretic model (semantics) that proves the type checker is sound:
1. $\text{Sort } 0$ is mapped to a set universe bounded by cardinal $\kappa_0$.
2. $\text{Sort } 1$ is mapped to a larger set universe bounded by cardinal $\kappa_1 > \kappa_0$.
3. $\text{Sort } n$ is mapped to $\kappa_n > \kappa_{n-1} > \dots > \kappa_0$.

Because Lean allows universe terms to mention arbitrary natural numbers $n$, giving a set-theoretic interpretation for the *entire* type system requires a sequence of cardinals $\kappa_0 < \kappa_1 < \kappa_2 < \dots$, which is precisely $\omega$ inaccessible cardinals.

### Summary

The theorem in that PR is proving **semantic soundness** for Lean 4 using the exact logical framework established over the last ~30 years:

$$\text{ZFC} + \omega \text{ Inaccessible Cardinals} \implies \text{Consistency of Lean}$$

By framing the theorem with `OmegaInaccessibles`, the project connects Lean's internal typechecker to the standard, well-studied consistency benchmark used across mathematical logic.

</details>


<details>
<summary>other approaches exist?</summary>

Yes, several other major approaches exist across mathematical logic, category theory, and programming language theory for proving the consistency and soundness of dependent type theories.

---

### 1. Syntactic / Proof-Theoretic Approaches (Normalization & Logical Relations)

Instead of building a set-theoretic model (semantics), this approach works directly on the **syntax** of the type theory.

* **How it works:** You prove **Strong Normalization** (every well-typed program terminates) or **Canonicity** (every closed term reduces to a canonical value, like `true`/`false` for booleans or `zero`/`succ` for natural numbers).
* **Proof Technique:** Uses **Logical Relations** (originating from Tait and Girard's *Candidates of Reducibility*) or **Normalization by Evaluation (NbE)**.
* **Why it proves consistency:** Since the `False` type has no canonical constructors (it has no introduction rules), if every term normalizes to a canonical value, no closed term of type `False` can exist.
* **Advantage:** It doesn't rely on set theory or large cardinal axioms.
* **Citation:** 
  - *Paper:* Yiyun Liu, Stephanie Weirich, "Functional Pearl: Short and Mechanized Logical Relation for Dependent Type Theories" (2024).
  - *URL:* https://doi.org/10.1145/3674634

---

### 2. Categorical & Realizability Models

Category theory offers a structural, abstract way to interpret types as objects and programs as morphisms (arrows).

* **How it works:** Types are interpreted as objects in specialized categories, such as:
  * **Locally Cartesian Closed Categories (LCCC)**
  * **Categories with Families (CwF)** (developed by Peter Dybjer)
  * **Presheaf Categories / Toposes**
  * **Realizability Toposes** (e.g., Martin Hyland’s Effective Topos)
* **Why it is used:** This approach is especially dominant when proving the consistency of type theories with special axioms that classical set theory doesn't naturally support—such as **Homotopy Type Theory (HoTT)** or **Cubical Type Theory**. For instance, Vladimir Voevodsky used the **Simplicial Set Model** to prove the consistency of the *Univalence Axiom*.
* **Citations:**
  - *Paper:* Peter Dybjer, "Internal Type Theory" (1996).
  - *URL:* https://doi.org/10.1007/3-540-60579-7_11
  - *Paper:* Daniel Gratzer et al., "Abstract Normalization by Evaluation for Dependent Types" (2022).
  - *URL:* https://arxiv.org/abs/2202.04944

---

### 3. Operational Semantics & Step-Indexed Logical Relations

Common in programming language theory (PLT), this approach proves type safety directly via abstract machine execution rules.

* **How it works:** You define a small-step operational semantics for how expressions evaluate. Then, you prove two properties:
  1. **Progress:** A well-typed expression is either already a final value or can take an evaluation step.
  2. **Preservation (Subject Reduction):** If a term $e$ has type $T$ and steps to $e'$, $e'$ still has type $T$.
* **Step-Indexing:** To handle complex features like self-referential types or general references, proofs use *step-indexed logical relations* (counting the number of evaluation steps remaining).
* **Why it proves consistency:** If a term of type `False` existed, taking evaluation steps could never arrive at a valid value (since no value of type `False` exists), violating Progress.
* **Citation:**
  - *Framework:* Iris Project (Separation Logic / Operational Semantics framework in Coq).
  - *URL:* https://iris-project.org/

---

### 4. Bounded / Relative Consistency (Internal Reflection)

Instead of assuming $\omega$ (infinitely many) inaccessible cardinals to prove consistency for **all** $N \in \mathbb{N}$ universes at once, you prove consistency for a **fixed, finite number of universes**.

* **How it works:** 
  - Lean with $N+1$ universes can construct a model for Lean with $N$ universes without needing any extra large cardinal axioms.
  - For example, Lean's built-in `Type 1` is large enough to construct a set-theoretic model for `Type 0`. Therefore, Lean can internally prove *"Lean restricted to `Type 0` is consistent"*.
* **Why `OmegaInaccessibles` was chosen in the PR instead:**
  - Lean allows functions that take a universe parameter $U : \mathbb{N}$ dynamically. To prove that Lean is consistent **unconditionally across all possible universe parameter choices $U$ in a single theorem**, you need the $\omega$-inaccessibles assumption.

---

### Comparison Summary

| Approach | Medium | Requires Large Cardinals? | Primary Use Case |
| :--- | :--- | :--- | :--- |
| **Set-Theoretic Models ($\text{ZFC}_\omega$)** | Set Theory | Yes ($\omega$ inaccessibles) | Proving full consistency of standard Lean / Coq with infinite universes. |
| **Syntactic Normalization** | Pure Syntax | No (uses ordinal strength) | Decidability of type checking, proof-theoretic analysis. |
| **Categorical Models** | Category Theory | Varies by category | Cubical Agda, HoTT, constructive type theories. |
| **Operational Semantics** | Abstract Machines | No | Verified compilers, Rust/C semantics (e.g., RustBelt, Iris). |
| **Bounded Models** | Internal Type Theory | No (relies on higher universe) | Self-consistency of bounded fragments of the system. |

</details>

2010  [Sets in Coq, Coq in Sets](https://www.lix.polytechnique.fr/page/index.php?username=barras&path=proofs/sets-old/sets.pdf)

<details>
<summary>

where he writes that is using Omega inaccessiables

</summary>

In Bruno Barras' paper *"Sets in Coq, Coq in Sets"*, he explicitly mentions using an infinite sequence / infinite number of inaccessible cardinals in two main places:

---

### 1. In the Introduction (Page 1, Paragraph 4)

In the introduction, Barras cites Benjamin Werner's earlier work and notes that building a set-theoretic model for the Calculus of Inductive Constructions (CIC) in ZF set theory requires infinitely many inaccessibles:

```markdown
"The Calculus of Constructions with universes (CCω) does not admit a finite model 
(as shown for instance by Miquel in [5] : a model of intuitionistic Zermelo can 
be built in a subtheory of CCω). This theory can be proven consistent in ZF [4], 
but Werner showed there is little hope that we can have a model of CIC in ZF 
without resorting to an infinite number of inaccessible cardinals."
```

---

### 2. In Section 4: "Model of the Calculus of Constructions with Universes (CCω)" (Page 5)

When formally describing the model construction for $\text{CC}_\omega$ (Calculus of Constructions with an infinite universe hierarchy $u_0, u_1, u_2, \dots$), Barras explicitly states the requirement:

```markdown
"An abstract model of CCω is an abstract model of CC, extended with a sequence 
(ui)_{i∈N} that satisfy the following properties :
∗ ∈ u0    un ∈ un+1    un ⊂ un+1
A ∈ un ∧ (∀x ∈ A, B(x) ∈ un) → Π(A, B) ∈ un
A ∈ ∗ ∧ (∀x ∈ A, B(x) ∈ un) → Π(A, B) ∈ un

As already mentioned, our long term goal is to build models for the Calculus of 
Inductive Constructions, so here we are not going to build a model of CCω under 
minimal assumptions. We require the existence of an infinite sequence of 
inaccessible cardinals."
```

---

### Summary of why he uses it here
In Section 4, each universe $u_n$ in the sequence $(u_i)_{i \in \mathbb{N}}$ corresponds to a Grothendieck universe, which in set theory is formed using an **inaccessible cardinal** $\kappa_n$. To model the entire unbounded sequence $u_0, u_1, u_2, \dots$ of universes simultaneously, he assumes an infinite sequence $(\kappa_n)_{n \in \mathbb{N}}$ of inaccessible cardinals ($\omega$ inaccessibles).


</details>



<details>
<summary>

1. what it means "Calculus of Constructions with Universes does not admit a finite model"?
1. he tells You cannot make model of CCw with finite datatypes? needthem to have infinite number inside?
1. then "This theory can be proven consistent in ZF, but CIC cannot"?
1. why what is different? CIC is even more "higher"?

</summary>

Here is a step-by-step breakdown of what that passage means, answering each of your questions in detail.

---

### 1. What does "does not admit a finite model" mean?

A **model** of a type theory is a mathematical universe (like a set of sets) where every type in the theory gets mapped to a mathematical object. 

* A **finite model** means you can interpret the entire type theory using **only finite sets** (e.g., sets with 2 elements, 10 elements, or the set of hereditarily finite sets $V_\omega$).
* **Basic $CC$ (Calculus of Constructions without universe levels):** You **can** build a finite model! As Barras shows in Section 1 of his paper, basic $CC$ is simple enough that it can be modeled entirely inside $V_\omega$ (finite sets). You don't need the concept of infinity to prove basic $CC$ is consistent.
* **$CC_\omega$ (Calculus of Constructions with Universes $Type_0, Type_1, \dots$):** Miquel proved that $CC_\omega$ is powerful enough to encode **Intuitionistic Zermelo Set Theory (IZ)**. 
  * Because Zermelo set theory contains the **Axiom of Infinity** (which proves infinite sets like $\mathbb{N} = \{0, 1, 2, \dots\}$ exist), any model of $CC_\omega$ **must contain infinite sets**.
  * Therefore, you **cannot** make a model of $CC_\omega$ using only finite data structures. Any model of $CC_\omega$ *must* contain infinite objects.

---

### 2. Can $CC_\omega$ be proven consistent in ZF, but CIC cannot?

**Yes, exactly.**

* **$CC_\omega$** can be proven consistent using standard **ZF** (Zermelo-Fraenkel) set theory without needing any extra axioms (proven by Zhaohui Luo in 1990).
* **CIC** (Calculus of Inductive Constructions) **cannot** be proven consistent in standard ZF set theory alone. It requires **inaccessible cardinals** (extra large cardinal axioms in set theory).

---

### 3. Why? What is the difference? Is CIC "higher" / stronger?

Yes, **CIC is logically much stronger ("higher") than $CC_\omega$.**

Here is what sets them apart:

#### What is $CC_\omega$?
$CC_\omega$ only has **function types** ($\Pi$-types) and a sequence of universes ($Type_0, Type_1, Type_2, \dots$). 
* In $CC_\omega$, you can write functions, dependent functions, and universe hierarchies.
* Standard ZF set theory easily has enough "room" (via standard set stages like $V_{\omega+\omega}$) to build function spaces for all the universes in $CC_\omega$. Standard ZF can easily prove $CC_\omega$ will never derive a contradiction.

#### What is CIC?
$$\text{CIC} = CC_\omega + \text{\textbf{Inductive Types}}$$

CIC takes $CC_\omega$ and adds **Inductive Types** (such as `nat`, `list`, trees, inductive families, and general fixpoint/recursion operators).

Adding inductive types makes a **massive difference** in proof-theoretic strength for two reasons:

1. **Powerful Recursion & Transfinite Induction:** Inductive types allow you to define recursive types and perform transfinite induction over well-founded trees.
2. **Large Eliminations:** In CIC, you can define inductive types in `Type` and pattern-match on them to construct new `Type`s. This lets you construct deep, nested hierarchies of universes *dynamically* inside the type theory.

Because of inductive types, **CIC is so strong that it can construct models of set theories that are stronger than standard ZF itself!** 

Since a system cannot prove the consistency of something stronger than itself (Gödel's Incompleteness Theorem), standard ZF set theory is **too weak** to prove that CIC is consistent. 

To prove CIC is consistent, set theory must be upgraded by adding **inaccessible cardinals** ($\text{ZFC} + \text{inaccessibles}$).

---

### Summary Comparison

| System | Key Features | Can it have a Finite Model? | Consistency Strength |
| :--- | :--- | :--- | :--- |
| **Basic $CC$** | Functions ($\Pi$-types), single `Prop` | **Yes** (Hereditarily finite sets $V_\omega$) | Very weak (weaker than basic arithmetic) |
| **$CC_\omega$** | Functions + Infinite Universes ($Type_n$) | **No** (Requires infinite sets) | Equivalent to Zermelo Set Theory (Proven consistent in standard **ZF**) |
| **CIC** | Functions + Universes + **Inductive Types** | **No** (Requires infinite sets) | **Stronger than ZF** (Requires **ZF + Inaccessible Cardinals**) |



</details>

2020 [Coq Coq Correct!](https://sozeau.gitlabpages.inria.fr/www/research/publications/Coq_Coq_Correct-POPL20.pdf)


<details>
<summary>

how about Coq Coq Correct! how does it prove?


</summary>

In the paper ***"Coq Coq Correct! Verification of Type Checking and Erasure for Coq, in Coq"*** (Sozeau et al., POPL 2020), the authors take a completely different approach to the consistency problem. 

Instead of trying to prove that Coq's type system is consistent (which Gödel's Second Incompleteness Theorem prevents Coq from doing internally without extra axioms), they prove that **Coq's actual type-checking software implementation is 100% bug-free relative to its formal specification**.

---

### 1. The Problem They Solved: TCB vs. TTB

Traditionally, using Coq required trusting two separate things:
1. **The Theory (Metatheory):** The logical rules of the Calculus of Inductive Constructions (CIC).
2. **The Code Base (TCB - Trusted Code Base):** The ~18,000 lines of OCaml code that implement Coq's kernel (the type checker, conversion checker, guard checker, etc.).

Even if the *theory* of CIC is consistent, the *OCaml implementation* can have bugs. In fact, historically, **about one critical bug was found in Coq's OCaml kernel every year**.

The paper moves Coq from a **Trusted Code Base (TCB)** to a **Trusted Theory Base (TTB)**.

---

### 2. How Does the Proof Work?

The project (part of **MetaCoq**) breaks the proof into four main layers:

```
[ Abstract PCUIC Specification (Inductive Rules: Γ ⊢ e : T) ]
                         ▲
                         │ Proven Sound & Complete in Coq
                         ▼
   [ Executable Type Checker in Coq (check_type env ctx e) ]
                         │
                         │ Proven Semantic-Preserving
                         ▼
        [ Certified Erasure (Stripping Proofs/Types) ]
                         │
                         ▼
              [ Executable OCaml Kernel ]
```

#### Step 1: Formalize Coq's Specification (PCUIC)
They define the mathematical rules of Coq inside Coq as an inductive relation called **PCUIC** (*Polymorphic, Cumulative Calculus of Inductive Constructions*).
* $1.1.1
This defines what it means declaratively for a context $\Gamma$, term $e$, and type $T$ to satisfy $\Gamma \vdash e : T$.

#### Step 2: Write an Executable Type Checker
They write an actual Coq program:
$$\text{check\_type} : \text{Environment} \to \text{Context} \to \text{Term} \to \text{Option Type}$$
This program handles weak head normal form (WHNF) reduction, conversion, universe constraint checking, and inductive guard checking.

#### Step 3: Prove Soundness and Completeness
They prove two main theorems inside Coq about `check_type`:

1. **Soundness (No False Positives):** 
   If `check_type env ctx e` returns `Some T`, then there is a valid formal derivation $\Gamma \vdash e : T$ in the PCUIC specification. *(The type checker will never accept an invalid proof or broken term).*
2. **Completeness (No False Negatives):** 
   If a valid derivation $\Gamma \vdash e : T$ exists according to the PCUIC specification, then `check_type env ctx e` will succeed and return `Some T'` (where $T'$ is convertible to $T$).

#### Step 4: Certified Erasure
To run the type checker efficiently, Coq definitions must be extracted to executable OCaml code. They write and formally prove a **proof erasure step** that strips away pure types and proof terms while guaranteeing that the program's runtime execution behavior is strictly preserved.

---

### 3. How does this handle Gödel's Incompleteness Theorem?

The authors explicitly address Gödel's theorem in the paper:

> *"Note that because of Gödel's second incompleteness theorem, there is no hope to prove completely the soundness of the specification of Coq inside Coq (in particular strong normalization)... but it is possible to prove the correctness of the implementation assuming the soundness of the specification."*

Instead of proving **Absolute Consistency** ($\vdash \text{Consistent}(\text{Coq})$), the paper proves **Conditional Correctness**:

$$\text{Soundness of Specification} \implies \text{Executable Type Checker is 100\% Correct}$$

---

### Summary

* **`Lean4LeanModel` (from your previous question):** Uses set-theoretic axioms ($\omega$ inaccessibles) to prove **Semantic Soundness** (that Lean's theory cannot prove `False`).
* **`Coq Coq Correct!` (MetaCoq):** Uses inductive specification matching to prove **Implementation Soundness** (that the executable kernel program perfectly matches the paper specification, eliminating C++/OCaml programming bugs).
</details>


<details>
<summary>

Where is anologue of

```lean
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

theorem consistency (_ : OmegaInaccessibles.{u}) {env : VEnv} (_ : env.WF) (U : Nat) :
    ¬ ∃ e, env.HasType U [] e VExpr.false := by
  sorry
```

in https://github.com/rocq-archive/coq-in-coq/tree/master/theories


</summary>

**There is NO analogue of `OmegaInaccessibles` in `coq-in-coq`.**

In `coq-in-coq`, the consistency theorem is the exact theorem you just pasted at the bottom of `Consistency.v`:

```coq
Theorem coc_consistency : forall t, ~ typ nil t absurd_prop.
```

Notice that `coc_consistency` **has no hypothesis at all**—it is an unconditional theorem (`forall t, ~ ...`).

---

### Why doesn't `coq-in-coq` need `OmegaInaccessibles`?

The difference comes down to **what calculus is being modeled**:

1. **`Lean4LeanModel` models full Lean 4 (`CIC` with infinite universes $Sort\ u$):**
   * Lean has arbitrary universe levels $0, 1, 2, \dots, u$.
   * As we saw earlier, proving consistency for an infinite hierarchy of universes requires $\omega$ inaccessible cardinals.
   * Because Lean cannot prove the existence of $\omega$ inaccessibles inside a fixed ambient universe, `Lean4LeanModel` must take `OmegaInaccessibles` as an **explicit hypothesis**.

2. **`coq-in-coq` models basic $CC$ (Calculus of Constructions with only 2 fixed sorts: `prop` and `set`):**
   * `coq-in-coq` does **not** have an infinite sequence of universe parameters ($Type_0, Type_1, Type_2, \dots$). It only has `prop` and `set`.
   * Because the target language ($CC$) only has 2 fixed sorts, the host language (Coq) already has higher universe levels (`Type`) that are more than strong enough to interpret $CC$'s `prop` and `set`.
   * Therefore, Coq can prove the consistency of $CC$ **unconditionally**, without assuming any extra axioms or large cardinal hypotheses!

---

### How `coq-in-coq` proves consistency in these files

Instead of a set-theoretic model using inaccessible cardinals, `coq-in-coq` uses a **syntactic / logical relations model**:

1. **`Int_typ.v` / `Int_term.v` / `Int_stab.v`:** 
   Defines an interpretation (model) of $CC$ terms into Coq's native types (`Prop`, `Set`, `Type`).
2. **`Strong_Norm.v`:** 
   Proves **Strong Normalization** (`str_norm`) for $CC$ using Girard's *Candidates of Reducibility* (Logical Relations) technique inside Coq.
3. **`Consistency.v`:** 
   Uses Strong Normalization (`str_norm`) and subject reduction to show that any proof of `absurd_prop` (`∀ P : Prop, P`) would reduce to a normal form. Since no normal form proof of `absurd_prop` exists (`coc_consistency_nf`), no term can prove `absurd_prop`.

   
</details>


`coq-in-coq` (Benjamin Werner, 1997)
Coq in Sets (Bruno Barras, 2010)

1. https://www.lix.polytechnique.fr/page/index.php?username=barras&path=proofs/sets/
2. https://github.com/barras/cic-model/

<details>
<summary>
what cic-model has
</summary>

<h3>Intuitionistic Zermelo-Fraenkel</h3>
<ul>
<li><a href="https://github.com/barras/cic-model/blob/master/ZFdef.v">Signatures of IZF</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZF.v">Introduction/Elimination Rules of IZF Axioms</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFrepl.v">Relationnal Replacement Axiom</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFpairs.v">Ordered pairs</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFrelations.v">Relations and Functions</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFsum.v">Disjoint Sum</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFnats.v">Natural Numbers</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFord.v">Ordinal Numbers</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFordcl.v">Classical Ordinal Numbers</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFfix.v">Fixpoint Theorem</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFgrothendieck.v">Grothendieck Universes</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFlambda.v">Lambda terms</a>

</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFcard.v">Cardinal Numbers</a>

</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFcoc.v">Semantics of CC in ZF</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFecc.v">Semantics of CCω in Tarski-Grothendieck Set Theory</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFindtypes.v">Inductive Types Nat and Ord</a>

</li><li><a href="https://github.com/barras/cic-model/blob/master/Choice.v">Type Theoretical Axiom of Choice</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/Ens.v">Model of IZF in Coq</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/EnsUniv.v">Building a Grothendieck Universe in Coq</a>

</li><li><a href="https://github.com/barras/cic-model/blob/master/ZFskol.v">Skolemization of IZF</a>
</li></ul>

<hr>

<h3>Hereditarily Finite Set Theory</h3>
<ul>
<li><a href="https://github.com/barras/cic-model/blob/master/HF.v">Hereditarily Finite Sets</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/HFrelation.v">HF Relations</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/HFcoc.v">Semantics of CC in HF</a>
</li></ul>

<hr>
<h3>Calculus of Constructions</h3>
<ul>
<li><a href="https://github.com/barras/cic-model/blob/master/Term.v">Terms</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/Conv.v">Conversion</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/Env.v">Environments</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/Types.v">Typing Rules</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/TypeJudge.v">Typing Rules (judgemental equality + Adams' proof)</a>
</li></ul>

<hr>

<h3>Calculus of Constructions with Universes</h3>
<ul>
<li><a href="https://github.com/barras/cic-model/blob/master/TermECC.v">Terms</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ConvECC.v">Conversion</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/EnvECC.v">Environments</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/TypeECC.v">Typing Rules</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/TypeJudgeECC.v">Typing Rules (judgemental equality)</a>
</li></ul>

<hr>

<h3>Models of the Calculus of Constructions (pure and with universes)</h3>
<ul>
<li><a href="https://github.com/barras/cic-model/blob/master/Models.v">Abstract Models of CC and CCω</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/GenModel.v">Soundness of Abstract Models of CC</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/GenModelSyntax.v">Mapping CC Syntax to the Abstract Model of CC</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ModelHF.v">Instantiation of the Abstract Model of CC in HF</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ModelZF.v">Instantiation of the Abstract Model of CC in IZF</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/ModelECC.v">Soundness of Abstract Models of CCω</a>

</li><li><a href="https://github.com/barras/cic-model/blob/master/ModelCIC.v">Model of CC with Natural Numbers
    (with type-based termination for fixpoints)</a>


</li><li><a href="https://github.com/barras/cic-model/blob/master/Lambda.v">Pure Lambda Terms</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/Can.v">Reducibility Candidates and Operations</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/Sat.v">Generic Interface of Saturated Sets</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/GenModelSN.v">Soundness of Abstract Strong
    Normalization Models of CC</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/SN_CC.v">Another Proof of Strong Normalization for the
    Calculus of Constructions</a>
</li></ul>

<hr>

<h3>General Purpose Libraries</h3>
<ul>
<li><a href="https://github.com/barras/cic-model/blob/master/basic.v">Useful definitions</a>
</li><li><a href="https://github.com/barras/cic-model/blob/master/VarMap.v">Maps</a>
</li></ul>

<!-- <hr> -->
<!-- <a href="https://github.com/barras/cic-model/blob/master/coqindex.v">Table of contents of Coq objects</a> -->


-------------------

This Coq development already formalizes inaccessible cardinals / Grothendieck universes and uses them to build models and prove consistency results (CC, ECC, etc.). You can find the Alexandrov/Tarski–Grothendieck-style universe machinery and the model/consistency theorems in these files.

- ZFinaccessible.v — VN_inaccessible and the link between inaccessibles and Grothendieck universes (definitions and lemmas about inaccessible cardinals):  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ZFinaccessible.v

- ZFgrothendieck.v — groth_univ, properties of Grothendieck universes and many lemmas used to build models:  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ZFgrothendieck.v

- ZFecc.v / ZFuniv.v / ZFuniv_real.v — constructions that build universes / ECC semantics in ZF (used for modelling CC & ECC with universes):  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ZFecc.v  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ZFuniv.v

- ModelECC.v — header/comments state the ECC model is built “based on ZF + infinitely many Grothendieck universes” (this is the file to look at if you want the analogue of requiring ω-many inaccessibles):  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ModelECC.v

- ModelCC.v, SN_CC.v, GenModelSN.v — consistency / strong-normalization proofs for CC (and variants). For example cc_consistency appears in ModelCC.v and consistency/strong_normalization appear in SN_CC.v:  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ModelCC.v  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/SN_CC.v

Consistency proofs (consistency of CC, variants with universes/ECC, and consistency derived from the strong-normalization model). 
These are proved by building set-theoretic models (in ZF / IZF, using Grothendieck universes / inaccessibles where needed) and then deriving that no closed proof of false exists in the object theory.


- ModelCC.v — Theorem cc_consistency: consistency of the (pure) Calculus of Constructions via a ZF model.  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ModelCC.v

- ModelCC_em.v — a variant using classical axioms (excluded middle) and an associated consistency statement.  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ModelCC_em.v

- ModelECC.v — construction of a model for ECC; header says “based on ZF + infinitely many Grothendieck universes”. This is the place that provides the analogue of assuming ω-many inaccessible cardinals to model universes.  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ModelECC.v

- GenModelSN.v and SN_CC.v — abstract model → strong normalization machinery and a consistency proof derived from the SN model (model_consistency, strong_normalization, and specific consistency lemmas).  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/GenModelSN.v  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/SN_CC.v

- ZFinaccessible.v and ZFgrothendieck.v — definitions/lemmas about (Grothendieck) universes and inaccessible cardinals used in the universe-based models.  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ZFinaccessible.v  
  https://github.com/barras/cic-model/blob/26bc9e081352aeb609f9ba7c31a19020a74cbba5/ZFgrothendieck.v

 For ECC with universes the development explicitly assumes many Grothendieck universes (inaccessibles). For the plain CC model the development works in IZF/ZF without needing those universes.


</details>


MetaCoq / Coq Coq Correct! (Sozeau et al., 2020)

* **What it formalizes:** Full modern Coq (pC(u)IC. **Predicative Calculus of Cumulative Inductive Constructions**).
* **What it proves:** **executable type-checking algorithm** correctly implements Coq's formal typing specification (`check_type t = Some T ↔ Γ ⊢ t : T`).

<details>
<summary>
what is proved
</summary>


```
metarocq/
│
├── template-coq/       # Quoting/unquoting library (reifies Coq terms into Coq ASTs)
│
├── pcuic/              # THE SPECIFICATION & METATHEORY
│   └── theories/
│       ├── PCUICTyping.v            # <--- Declarative typing specification (Σ ;;; Γ |- t : T)
│       ├── PCUICCumulativitySpec.v  # <--- Conversion & cumulativity specification
│       └── PCUICSR.v                # <--- Proof of Subject Reduction
│
├── safechecker/        # THE VERIFIED TYPE-CHECKER IMPLEMENTATION
│   └── theories/
│       ├── PCUICTypeChecker.v       # <--- Executable type checking algorithm
│       └── PCUICSafeChecker.v       # <--- Soundness & completeness proofs
│
└── erasure/            # CERTIFIED ERASURE PIPELINE
    └── theories/                    # <--- Proof stripping / extraction to Untyped Lambda Calculus
```

### **1. Weakening**
- **Files:** 
  - `pcuic/theories/Typing/PCUICWeakeningTyp.v` (local context weakening)
  - `pcuic/theories/Conversion/PCUICWeakeningConv.v` (conversion/reduction weakening)
  - `pcuic/theories/Typing/PCUICWeakeningEnvTyp.v` (global environment weakening)
  - `pcuic/theories/Conversion/PCUICWeakeningEnvConv.v` (environment weakening for conversion)
- **Main theorems:**
  - `weakening_typing` - Typing preserved by extending local context
  - `weakening_red` - Reduction preserved by context extension
  - `weakening_cumul` - Cumulativity preserved by weakening
  - `weakening_env_*` - Various weakening lemmas for global environment extension

### **2. Confluence**
- **File:** `pcuic/theories/PCUICConfluence.v`
- **Key results:**
  - Confluence via parallel reduction diamond property (`PCUICParallelReductionConfluence`)
  - Transitivity of conversion/cumulativity on well-typed terms

### **3. Subject Reduction**
- **File:** `pcuic/theories/PCUICSR.v` (line 840)
- **Main definition:**
  ```rocq prover
  Definition SR_red1 {cf} Σ Γ t T :=
    forall u (Hu : closed_red1 Σ Γ t u), Σ ;;; Γ |- u : T.
  ```

### **4. Principality**
- **File:** `pcuic/theories/PCUICPrincipality.v` (line 74)
- **Main theorem:**
  ```rocq prover
  Theorem principal_type {Γ u A} : Σ ;;; Γ |- u : A ->
    ∑ C, (forall B, Σ ;;; Γ |- u : B -> Σ ;;; Γ ⊢ C ≤ B × Σ ;;; Γ |- u : C).
  ```
- Every typable term has a smallest (principal) type

### **5. Bidirectional Typing**
- **Files:**
  - `pcuic/theories/Bidirectional/BDTyping.v` - Core bidirectional rules
  - `pcuic/theories/Bidirectional/BDToPCUIC.v` (line 105) - Bidirectional → undirected typing
  - `pcuic/theories/Bidirectional/BDFromPCUIC.v` (line 382) - Undirected → bidirectional typing
  - `pcuic/theories/Bidirectional/BDUnique.v` - Inferred types are unique
  - `pcuic/theories/Bidirectional/BDStrengthening.v` (line 475) - Weakening from contexts
- **Key theorems:**
  - `typing_infering` - Every typing derives an infering judgment
  - `typing_checking` - Every typing derives a checking judgment
  - Strengthening: unused variables can be removed from context

### **6. Elimination Restrictions**
- **File:** `pcuic/theories/PCUICElimination.v` (line 1)
- **Definitions:**
  - `SingletonProp` - Singleton elimination from Prop to Type restrictions
  - `Computational` - Computational inductives forbid proof arguments
  - `Subsingleton` - Subsingleton properties of inductives
- These ensure singleton elimination criterion for propositional types

### **7. Canonicity**
- **File:** `pcuic/theories/PCUICCanonicity.v` (line 1)
- **Main theorem:**
  ```rocq prover
  Lemma pcuic_canonicity {cf:checker_flags} {nor : normalizing_flags} Σ 
    {normalization_in: NormalizationIn Σ} t i u args :
    axiom_free Σ -> wf Σ ->
    Σ ;;; [] |- t : mkApps (tInd i u) args ->
    { t':term & (Σ ;;; [] |- t' : mkApps (tInd i u) args) * 
                (Σ ;;; [] |- t =s t') * construct_cofix_discr (head t')}.
  ```
- Weak head normal form of term of inductive type is a constructor application

### **8. Consistency**
- **File:** `pcuic/theories/PCUICConsistency.v` (line 1)
- **Main theorem:**
  ```rocq prover
  Theorem pcuic_consistent {cf:checker_flags} {nor : normalizing_flags} Σ
    {normalization_in: NormalizationIn Σ} t False_pcuic :
    declared_inductive Σ False_pcuic False_mib False_oib ->
    wf_ext Σ -> axiom_free Σ ->
    Σ ;;; [] |- t : tInd False_pcuic []  -> False.
  ```
- **Depends on:** `pcuic_canonicity` + `NormalizationIn` (strong normalization postulate)
- Proves PCUIC cannot derive `False` assuming strong normalization


</details>



<details>
<summary>
do they use Omega inaccessiables?
</summary>


  **No, they do not use inaccessible cardinals.**

Instead, MetaCoq circumvents Gödel's Incompleteness Theorem by making **Strong Normalization an explicit hypothesis** in the theorem statement:

```coq
{normalization_in : NormalizationIn Σ}
```

---

### How this theorem works

Look at the premises of `pcuic_consistent`:

1. `{normalization_in : NormalizationIn Σ}`  
   This is an **unproved hypothesis/parameter** asserting that every term in the environment $\Sigma$ strongly normalizes (terminates).
2. `axiom_free Σ`  
   Asserts that the environment contains no unproved axioms (like `sorry` or arbitrary postulates).
3. `declared_inductive Σ False_pcuic False_mib False_oib`  
   States that `False` is defined as an inductive type with **zero constructors** (`ind_ctors := []`).

#### The Proof Logic inside the snippet:
1. `destruct (pcuic_canonicity ...) as [...]`  
   Because of the `normalization_in` hypothesis, MetaCoq can invoke the **Canonicity Theorem** (`pcuic_canonicity`). Canonicity states: *"If a closed term $t$ has an inductive type, $t$ must evaluate to a constructor or cofixpoint."*
2. `destruct t0; try discriminate ctor.`  
   It checks what constructor $t$ evaluated to.
3. `cbn in H1. rewrite nth_error_nil in H1. discriminate.`  
   Since `False_oib` was defined with `ind_ctors := []` (0 constructors), no constructor exists for $t$ to evaluate to! This creates a contradiction and completes the proof that $t : \text{False}$ is impossible.

---

### Comparison with `Lean4LeanModel`

| Project | Hypothesis Used | Logical Meaning |
| :--- | :--- | :--- |
| **`Lean4LeanModel`** (Lean 4) | `OmegaInaccessibles` | *"Assuming set theory has $\omega$ inaccessible cardinals, Lean is consistent."* (Builds a Set-Theoretic Model) |
| **MetaCoq / MetaRocq** (Coq) | `NormalizationIn Σ` | *"Assuming PCUIC terms strongly normalize, PCUIC is consistent."* (Syntactic Canonicity Proof) |

Neither project violates Gödel's Incompleteness Theorem. Both require an unproved assumption to state consistency: Lean uses a **set-theoretic large cardinal hypothesis**, while MetaCoq uses a **proof-theoretic normalization hypothesis**.


</details>



<details>
<summary>
if we would use this idea of strong normalization instead of inaccessiables - how would consistency theorem look like for lean?
  
and how to define strong normalization in lean4lean-model?
</summary>


If we replace the set-theoretic approach (`OmegaInaccessibles`) with the syntactic approach (**Strong Normalization** and **Canonicity**), the consistency theorem for Lean would no longer depend on cardinal arithmetic. 

Instead, it would depend on a hypothesis asserting that **reduction in Lean terminates for all well-typed terms**.

---

### 1. How the Consistency Theorem Would Look in Lean 4

Currently, the theorem in `Lean4LeanModel` looks like this:

```lean
-- CURRENT APPROACH (Set-Theoretic / Model Theory)
theorem consistency (hlarge : OmegaInaccessibles.{u}) {env : VEnv} (henv : env.WF) (U : Nat) :
    ¬ ∃ e, env.HasType U [] e VExpr.false
```

With Strong Normalization, the theorem statement would look like this:

```lean
-- ALTERNATIVE APPROACH (Syntactic / Proof Theory)
theorem consistency_via_sn {env : VEnv} (henv : env.WF) (hax : env.AxiomFree)
    (hsn : env.StrongNormalization) (U : Nat) :
    ¬ ∃ e, env.HasType U [] e VExpr.false := by
  rintro ⟨e, he⟩
  -- 1. By Strong Normalization, `e` reduces to a normal form `v`
  obtain ⟨v, hred, hnf⟩ := hsn.has_normal_form he
  -- 2. By Subject Reduction, `v` also has type `VExpr.false`
  have hv_type : env.HasType U [] v VExpr.false := subject_reduction he hred
  -- 3. By Canonicity, a closed normal form of an inductive type must be a constructor
  have hctor := canonicity henv hnf hv_type
  -- 4. But `VExpr.false` has 0 constructors! Contradiction.
  exact no_constructors_for_false hctor
```

---

### 2. How to Define Strong Normalization in `lean4lean-model`

To formalize this in Lean 4, you need four key definitions: **One-Step Reduction**, **Normal Form**, **Accessibility (`Acc`)**, and **Canonicity**.

#### Step A: Define One-Step Reduction (`Step`)
First, define single-step reduction $e_1 \rightsquigarrow e_2$ in environment `env` ($\beta$-reduction for lambdas, $\zeta$-reduction for lets, $\delta$-reduction for unfolding definitions, and $\iota$-reduction for inductive pattern matching/recursors):

```lean
/-- Single-step reduction relation `e1 ⇝ e2` in an environment `env`. -/
inductive VEnv.Step (env : VEnv) : VExpr → VExpr → Prop
  | beta (a b : VExpr) :
      Step env (.app (.lam _ _ body) arg) (body.instantiate1 arg)
  | zeta (T val body : VExpr) :
      Step env (.letE _ T val body _) (body.instantiate1 val)
  | delta (name : Name) (decl : VDecl) (args : List VExpr) :
      env.find? name = Some decl → decl.value = Some val →
      Step env (.const name) val
  | iota ... -- recursor / pattern-matching reduction rules
  | app_left {e1 e2 e'} : Step env e1 e2 → Step env (.app e1 e') (.app e2 e')
  | app_right {e1 e2 e'} : Step env e1 e2 → Step env (.app e' e1) (.app e' e2)
```

#### Step B: Define Normal Forms (`IsNormalForm`)
An expression is in normal form if it cannot take any further reduction steps:

```lean
/-- An expression is in normal form if no reduction step can be taken. -/
def VExpr.IsNormalForm (env : VEnv) (e : VExpr) : Prop :=
  ∀ e', ¬ env.Step e e'
```

#### Step C: Define Strong Normalization using `Acc`
In Lean 4, "Strong Normalization" (no infinite reduction chains $e_0 \rightsquigarrow e_1 \rightsquigarrow e_2 \rightsquigarrow \dots$) is formally defined using Lean's built-in **`Acc` (Accessibility)** predicate on the reversed step relation:

```lean
/-- A term `e` is strongly normalizing if it is accessible under the reverse step relation.
    This means every reduction path starting at `e` is finite. -/
def VExpr.IsSN (env : VEnv) (e : VExpr) : Prop :=
  Acc (fun e2 e1 => env.Step e1 e2) e

/-- An environment `env` is strongly normalizing if all well-typed closed terms are strongly normalizing. -/
def VEnv.StrongNormalization (env : VEnv) : Prop :=
  ∀ (U : Nat) (e T : VExpr), env.HasType U [] e T → VExpr.IsSN env e
```

#### Step D: Define Canonicity (`Canonicity`)
Canonicity states that if a closed, normal-form expression `v` has an inductive type $I$, then `v` **must** be a constructor application of $I$:

```lean
/-- Canonicity: A closed, well-typed term in normal form whose type is an inductive type
    must be applied to one of that inductive type's constructors. -/
def VEnv.Canonicity (env : VEnv) : Prop :=
  ∀ (U : Nat) (v : VExpr) (ind_name : Name) (args : List VExpr),
    env.HasType U [] v (.app (.const ind_name) args) →
    v.IsNormalForm env →
    ∃ (ctor_name : Name) (ctor_args : List VExpr),
      v = .mkApps (.const ctor_name) ctor_args ∧
      env.IsConstructorOf ctor_name ind_name
```

---

### Summary of Differences

| Feature | Current Model (`OmegaInaccessibles`) | Alternative Model (`StrongNormalization`) |
| :--- | :--- | :--- |
| **Flavour** | **Set-Theoretic / Model-Theoretic** | **Proof-Theoretic / Syntactic** |
| **Core Hypothesis** | `∃ κ : ℕ → Cardinal, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible` | `∀ e T, env.HasType U [] e T → Acc (flip (env.Step)) e` |
| **Mechanism** | Maps Lean terms into mathematical sets ($V_{\kappa_n}$). `VExpr.false` evaluates to $\emptyset$. | Proves closed terms reduce to normal forms. `VExpr.false` has 0 normal form constructors. |
| **Similar To** | Werner (1997), Barras (2010), Mario Carneiro (2019) | MetaCoq / MetaRocq (Sozeau et al., 2020) |


</details>
