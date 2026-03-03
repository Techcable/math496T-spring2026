import MIL.Common
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Ring.Parity
import Mathlib.Order.RelClasses

/- # Lecture 12: Relations and Equivalence Relations

New tactics: **unfold, omega, trans, unfold**
Recall: **constructor, ext, rfl, calc, linarith, norm_num, ring, push_neg**

## Overview

A **binary relation** on a type α is a function `α → α → Prop`.
Given two elements, it returns a proposition (which may or may not be provable).

Two fundamental species of "well-behaved" relation:
  • **Equivalence relation** = reflexive + symmetric + transitive
  • **Partial order**        = reflexive + antisymmetric + transitive

We introduce three equivalence relations that will accompany us throughout.
-/

-- Properties of relations (Mathlib definitions):
#check @Reflexive        -- Reflexive r : ∀ x, r x x
#check @Symmetric       -- Symmetric r : ∀ ⦃x y⦄, r x y → r y x
#check @Transitive      -- Transitive r : ∀ ⦃x y z⦄, r x y → r y z → r x z
#check @Irreflexive      -- Irreflexive r : ∀ x, ¬ r x x
#check @Equivalence     -- Equivalence r : bundles refl, symm, trans

#check @Set.Subset.antisymm  -- s ⊆ t → t ⊆ s → s = t

-- Subset relation on sets is a **partial order**:
#check @Set.Subset.refl      -- ∀ (s : Set α), s ⊆ s
#check @Set.Subset.trans     -- s ⊆ t → t ⊆ u → s ⊆ u
#check @Set.empty_subset     -- ∅ ⊆ s
#check @Set.subset_univ      -- s ⊆ Set.univ
#check @Set.inter_subset_left   -- s ∩ t ⊆ s
#check @Set.subset_union_left   -- s ⊆ s ∪ t

-- Setoid (bundled equivalence relation — preview for next Lecture):
#check @Setoid

-- ============================================================================
-- ## Part 1: Three Running Examples
-- ============================================================================

/-
**Example A — Same parity.**
Two natural numbers are equivalent when they have the same remainder mod 2:
both even, or both odd.
-/

def SameParity (a b : ℕ) : Prop := ∃ k : ℤ, (a : ℤ) - b = 2 * k
#print SameParity

/-
**Example B — Congruence mod n.**
Two integers are congruent modulo n when n divides their difference.
This single definition is the engine of all modular arithmetic.
-/

def CongMod (n : ℕ) (a b : ℤ) : Prop := (n : ℤ) ∣ (a - b)

/-
**Example C — The function kernel.**
Given any function f : α → β, declare a ~ b whenever f a = f b —
"f cannot tell a and b apart."  This is the most general source of
equivalence relations: we will see in Lecture 13 that *every* equivalence
relation arises this way.
-/

def fKernel {α β : Type*} (f : α → β) (a b : α) : Prop := f a = f b

-- Quick checks:
example : SameParity 4 6           := ⟨-1,by rfl⟩               -- 4 − 6 = 2·(−1)
example : CongMod 5 17 2           := by unfold CongMod; norm_num  -- 5 ∣ 15
example : fKernel (· % 2 : ℕ → ℕ) 4 6 := by unfold fKernel; norm_num

example : ¬ SameParity 3 6         := by unfold SameParity; push_neg; intro k; omega
example : ¬ CongMod 5 17 3         := by unfold CongMod; norm_num

/-
SameParity is secretly the kernel of (· % 2)!
Both ask: "do a and b land in the same bucket when sorted by remainder mod 2?"
The two definitions are logically equivalent.
-/


theorem sameParity_iff_fKernel (a b : ℕ) :
    SameParity a b ↔ fKernel (· % 2 : ℕ → ℕ) a b := by
  -- unfold SameParity fKernel
  simp only [SameParity, fKernel]  -- compare `unfold` and `simp only`
  constructor
  · rintro ⟨k, hk⟩
    -- (a : ℤ) − b = 2k  implies  a % 2 = b % 2
    omega --  tactic, for resolving integer and natural linear arithmetic problems.
  · intro h
    -- a % 2 = b % 2  implies  2 ∣ (a : ℤ) − b; witness is ((a : ℤ) − b) / 2
    use ((a : ℤ) - b)/2
    omega

-- ### Exercises (Part 1) — verify concrete instances

-- (a) Check membership:
example : SameParity 11 3     := by
  dsimp [SameParity]
  use 4
  rfl
example : CongMod 7 100 2     := by
  dsimp [CongMod]
  dsimp [Dvd.dvd]
  use 14
  rfl


example : CongMod 3 13 4      := by
  dsimp [CongMod]
  dsimp [Dvd.dvd]
  use 3
  rfl

-- (b) The kernel of List.length relates lists of equal length:
example : fKernel List.length [1, 2, 3] [10, 20, 30] := by
  dsimp [fKernel] -- apparently this is enough



-- (c) Distinguish the relations:
-- SameParity sees 1 and 3 as the same (both odd).
-- CongMod 3 does not: 1 ≢ 3 (mod 3).
example :   SameParity 1 3  := by
  dsimp [SameParity]
  use -1
  rfl
example : ¬ CongMod 3 1 3   := by
  intro hcong
  dsimp [CongMod,Dvd.dvd] at hcong
  omega

-- ============================================================================
-- ## Part 2: Equivalence Relations
-- ============================================================================

/-
An **equivalence relation** on α is a relation R : α → α → Prop satisfying:

  **Reflexive**:    ∀ a,     R a a
  **Symmetric**:   ∀ a b,   R a b → R b a
  **Transitive**:  ∀ a b c, R a b → R b c → R a c

These three axioms are precisely what is needed to make "treating a and b
as the same" coherent:
  • Reflexivity:    every object is the same as itself.
  • Symmetry:      if we identify a with b, we identify b with a.
  • Transitivity:  chains of identifications compose.

Mathlib bundles these as `Equivalence R`.
-/

-- ### Example A

theorem sameParity_equivalence : Equivalence SameParity where
  refl  := by intro x; unfold SameParity; use 0; linarith
      -- fun a       => ⟨0,     by ring⟩      -- a − a = 0 = 2·0
  symm  := by
    intro a b ⟨k, hk⟩
    exact ⟨-k, by linarith⟩                      -- b − a = 2·(−k)
  trans := by
    intro a b c ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by linarith⟩                   -- a − c = 2·(k + l)

-- ### Example C — the proof is just the three properties of equality.

theorem fKernel_equivalence {α β : Type*} (f : α → β) : Equivalence (fKernel f) where
  refl  := by intro x; unfold fKernel; rfl
       -- fun _         => rfl
  symm  := by intro a b h;       exact h.symm
  trans := by intro a b c h1 h2; exact h1.trans h2

-- ### Example B

theorem congMod_equivalence (n : ℕ) : Equivalence (CongMod n) where
  refl  := by intro a; simp [CongMod]             -- n ∣ 0 = a − a
  symm  := by
    intro a b ⟨k, hk⟩
    exact ⟨-k, by linarith⟩                       -- b − a = n·(−k)
  trans := by
    intro a b c ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by linarith⟩                    -- a − c = n·(k + l)

/-
Observe: the three proofs are structurally identical.
This is not a coincidence: all three are kernels of the same type of function.
-/

-- ### The `trans` tactic

/-
When the goal is `a ~ c` for a transitive relation, `trans b` splits it
into `a ~ b` and `b ~ c`.  Works for `=`, `≤`, `⊆`, and custom relations.
-/

example : CongMod 3 7 1 := by
  apply @(congMod_equivalence 3).trans _ 4 -- NOTE the @ use to access implicit variables
  use 1; rfl
  use 1; rfl



example (a b c d : ℕ) (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d) : a ≤ d := by
  trans c
  trans b
  exact h1
  exact h2
  exact h3

example (a b c d : Set α) (h1 : a ⊆ b) (h2 : b ⊆ c) (h3 : c ⊆ d) : a ⊆ d :=
  calc a ⊆ b := h1
      _  ⊆ c := h2
      _  ⊆ d := h3

-- ### Exercises (Part 2)

-- (a) Prove equality on ℕ is an equivalence relation:
example : Equivalence (· = · : ℕ → ℕ → Prop) where
  refl  := by
    intro x
    rfl
  symm  := by
    intro x y heq
    rw [heq]
  trans := by
    intro x y z xeqy yeqz
    rw [xeqy]
    exact yeqz

-- (b) ≤ on ℕ is reflexive and transitive, but not symmetric:
example : Reflexive  (· ≤ · : ℕ → ℕ → Prop) := by
  intro x
  rfl
example : Transitive (· ≤ · : ℕ → ℕ → Prop) := by
  intro x y z xlty yltz
  -- This is cheating?
  trans y
  . exact xlty
  . exact yltz

example : ¬ Symmetric (· ≤ · : ℕ → ℕ → Prop) := by
  intro h
  dsimp [Symmetric] at h
  have h1 : 1 ≤ 2 := by
    linarith
  have h2 : 2 ≤ 1 := by
    apply h h1
  contradiction

-- (c) < on ℕ is irreflexive (so not an equivalence relation):
example : Irreflexive (· < · : ℕ → ℕ → Prop) := by
  intro x h
  have : 0 < 0 := by
    linarith
  contradiction

-- (d) Use `trans` to prove 12 ≡ 0 (mod 4) via intermediate value 8:
example : CongMod 4 12 0 := by
  dsimp [CongMod]
  use 3
  linarith

-- (e) Use `calc` to prove CongMod 5 17 2 via the chain 17 ≡ 12 ≡ 7 ≡ 2:
example : CongMod 5 17 2 := by sorry


-- ============================================================================
-- ## Part 3: Equivalence Classes — the Identified Objects
-- ============================================================================

/-
Given an equivalence relation R on α, the **equivalence class** of a is:

  `[a]_R  =  { x : α | R a x }`

This is the set of everything we have decided to identify with a.
It is the answer to the question: "what single object does `a` represent?"

We now prove three facts that justify this definition.
-/

section EquivClasses

variable {α : Type*} (R : α → α → Prop) (hR : Equivalence R)

def eqClass (a : α) : Set α := { x | R a x }

-- **Fact 1.**  Every element belongs to its own class.

theorem mem_eqClass_self (hR : Equivalence R) (a : α) : a ∈ (eqClass R a : Set α) := by apply hR.refl
#print mem_eqClass_self

/-
**Fact 2.**  Two elements are related if and only if they have the same class.

The forward direction is the key insight: if R a b, then [a] = [b].
Anything related to a is also related to b (by symmetry + transitivity),
and vice versa.  So the two "buckets" contain exactly the same elements.
-/

theorem eqClass_eq_of_rel (hR : Equivalence R) {a b : α}  (hab : R a b) :
    eqClass R a = eqClass R b := by
  sorry

-- The converse: equal classes imply the elements are related.
theorem rel_of_eqClass_eq (hR : Equivalence R) {a b : α} (h : eqClass R a = eqClass R b) : R a b := by
  -- a ∈ [a] = [b], so R b a.  By symmetry, R a b.
  have ha : a ∈ eqClass R b := by sorry
  exact hR.symm ha

-- Packaging both directions:
theorem eqClass_eq_iff_rel (hR : Equivalence R) {a b : α} : eqClass R a = eqClass R b ↔ R a b :=
  ⟨rel_of_eqClass_eq R hR, eqClass_eq_of_rel R hR⟩

/-
**Fact 3.**  Any two equivalence classes are equal or disjoint.

There is no "partial overlap": if [a] and [b] share even one element,
they must be the same class entirely.  This is the heart of why equivalence
classes form a clean partition.
-/

theorem eqClass_eq_or_disjoint (hR : Equivalence R) (a b : α) :
    eqClass R a = eqClass R b ∨ eqClass R a ∩ eqClass R b = ∅ := by
  by_cases h : ∃ x, x ∈ eqClass R a ∩ eqClass R b
  · -- Case 1: there is a common element x.
    left
    obtain ⟨x, hx⟩ := h
    rw [Set.mem_inter_iff] at hx
    -- Name the two membership facts explicitly.
    have hxa : R a x := hx.1   -- x ∈ [a], so R a x
    have hxb : R b x := hx.2   -- x ∈ [b], so R b x
    -- From R b x, symmetry gives R x b.
    have hxb' : R x b := hR.symm hxb
    -- From R a x and R x b, transitivity gives R a b.
    have hab : R a b := hR.trans hxa hxb'
    -- Now Fact 2 gives [a] = [b].
    exact eqClass_eq_of_rel R hR hab
  · -- Case 2: no common element exists.
    right
    push_neg at h
    -- h : ∀ x, x ∉ eqClass R a ∩ eqClass R b
    ext x; constructor
    · intro hx
      -- hx says x is in the intersection, but h x says it is not.
      exact absurd hx (h x)
    · intro hx
      -- Nothing is in ∅.
      contradiction


end EquivClasses

-- ### Exercises (Part 3) — working with classes

-- (a) Check membership in parity classes:
example : (4 : ℕ) ∈ eqClass SameParity 0 := by sorry   -- 4 is even
example : (7 : ℕ) ∈ eqClass SameParity 1 := by sorry   -- 7 is odd

-- (b) Two even numbers have the same class:
example : eqClass SameParity 0 = eqClass SameParity 8 := by sorry

-- (c) 10 belongs to the class of 1 under CongMod 3  (since 3 ∣ 9):
example : (10 : ℤ) ∈ eqClass (CongMod 3) 1 := by sorry

-- (d) Equal classes under CongMod 3:
example : eqClass (CongMod 3) 4 = eqClass (CongMod 3) 1 := by sorry

-- (e) Use eqClass_eq_iff_rel to give a one-line proof that SameParity 3 5:
example : SameParity 3 5 :=
  (eqClass_eq_iff_rel SameParity sameParity_equivalence).mp (by sorry)

-- (f) Show [0] and [3] are different classes under CongMod 5:
example : eqClass (CongMod 5) 0 ≠ eqClass (CongMod 5) 3 := by
  -- Hint: use eqClass_eq_iff_rel and unfold CongMod.
  sorry



-- ============================================================================
-- ## Part 4: The Partition Theorem
-- ============================================================================

/-
We now assemble the three facts into a complete answer to our question.

**Partition Theorem.**
For any equivalence relation R on α, the collection of all equivalence classes
is a **partition** of α:
  (P1)  Every element belongs to some class (and to its own class, by Fact 1).
  (P2)  Any two classes are equal or disjoint                    (Fact 3).
  (P3)  Every class is non-empty                                 (Fact 1).

A partition is a way of cutting the whole set into non-overlapping pieces.
The equivalence classes are exactly those pieces.

Let us make this completely explicit for our two main examples.
-/


-- ============================================================================
-- ### The parity partition of ℕ
-- ============================================================================

/-
Under SameParity, ℕ splits into exactly two classes:
  [0] = { 0, 2, 4, 6, ... }   the even numbers
  [1] = { 1, 3, 5, 7, ... }   the odd numbers

Every natural number is in exactly one of them.
-/

-- Every n is in [0] or [1]:
theorem parity_partition (n : ℕ) :
    n ∈ eqClass SameParity 0 ∨ n ∈ eqClass SameParity 1 := by
  simp only [eqClass, Set.mem_setOf_eq, SameParity]
  -- Split on whether n is even or odd.
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- n = k + k (even).  Witness for (0 : ℤ) − n = 2·(−k): check by ring.
    left;  exact ⟨-(k : ℤ), by omega⟩
  · -- n = 2k + 1 (odd).  Witness for (1 : ℤ) − n = 2·(−k): check by ring.
    right; exact ⟨-(k : ℤ), by omega⟩

-- [0] and [1] are disjoint:
theorem parity_classes_disjoint :
    eqClass SameParity 0 ∩ eqClass SameParity 1 = ∅ := by
  rcases eqClass_eq_or_disjoint SameParity sameParity_equivalence 0 1 with h | h
  · -- If [0] = [1] then 0 and 1 would be SameParity — impossible.
    exfalso
    -- Since [0] = [1], and 1 ∈ [1], we get 1 ∈ [0], i.e. SameParity 0 1.
    have h1_in_0 : (1 : ℕ) ∈ eqClass SameParity 0 :=
      h ▸ mem_eqClass_self SameParity sameParity_equivalence 1
    -- SameParity 0 1 means ∃ k : ℤ, (0 : ℤ) − 1 = 2k, i.e. −1 = 2k.
    simp only [eqClass, Set.mem_setOf_eq, SameParity] at h1_in_0
    obtain ⟨k, hk⟩ := h1_in_0
    -- No integer k satisfies −1 = 2k.
    omega
  · exact h

-- Summary: ℕ = [0] ⊔ [1] (disjoint union).  Exactly two pieces.


-- ============================================================================
-- ### The modular partition of ℤ
-- ============================================================================

/-
Under CongMod 5, ℤ splits into exactly five classes:
  [0], [1], [2], [3], [4]

(Every integer has a unique remainder 0, 1, 2, 3, or 4 when divided by 5,
and two integers are congruent mod 5 iff they have the same remainder.)

Let us verify that two of these classes are disjoint.
-/

example : eqClass (CongMod 5) 0 ∩ eqClass (CongMod 5) 1 = ∅ := by
  rcases eqClass_eq_or_disjoint (CongMod 5) (congMod_equivalence 5) 0 1 with h | h
  · exfalso
    have h1 : (1 : ℤ) ∈ eqClass (CongMod 5) 0 :=
      h ▸ mem_eqClass_self (CongMod 5) (congMod_equivalence 5) 1
    simp only [eqClass, Set.mem_setOf_eq, CongMod] at h1
    -- 5 ∣ 0 − 1 = −1 is false.
    norm_num at h1
  · exact h


-- ============================================================================
-- ### Setoid — packaging for Lean's quotient machinery
-- ============================================================================

/-
Lean's quotient type `Quotient` requires the equivalence relation to be
presented as a `Setoid`: a **typeclass** bundling the relation with its proof
of equivalence.

In Lecture 13 we will use `Setoid` to build **quotient types** — new types
whose elements *are* the equivalence classes.  For example, ℤ/nℤ will be
constructed as `Quotient (congModSetoid n)`.

For now, just observe how our `congMod_equivalence` slots straight in:
-/

instance congModSetoid (n : ℕ) : Setoid ℤ where
  r     := CongMod n
  iseqv := congMod_equivalence n


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================

/-
The exercises below range from straightforward to genuinely challenging.
The first few are warm-ups; the final ones require combining several ideas.
-/

-- ============================================================================
-- ### Warm-up
-- ============================================================================

-- (1) Show ∣ on ℕ is NOT symmetric (hence not an equivalence relation):
example : ¬ Symmetric (· ∣ · : ℕ → ℕ → Prop) := by
  sorry

-- (2) Show [2] ≠ [0] under CongMod 4  (since 4 ∤ 2):
example : eqClass (CongMod 4) 2 ≠ eqClass (CongMod 4) 0 := by
  sorry

-- (3) Show that the class of 0 under CongMod 2 contains all even integers:
example : (6 : ℤ) ∈ eqClass (CongMod 2) 0 := by sorry
example : (-4 : ℤ) ∈ eqClass (CongMod 2) 0 := by sorry


-- ============================================================================
-- ### Core
-- ============================================================================

-- (4) Prove CongMod 2 is an equivalence relation directly
-- (without invoking congMod_equivalence — reprove from scratch):
example : Equivalence (CongMod 2) where
  refl  := by sorry
  symm  := by sorry
  trans := by sorry

-- (5) < on ℕ is asymmetric: a < b implies ¬ b < a.
-- (Hence < cannot be an equivalence relation.)
example : ∀ (a b : ℕ), a < b → ¬ (b < a) := by
  sorry

-- (6) Prove that [0] under CongMod 2 is exactly the set of integers
-- divisible by 2.  Hint: unfold eqClass and CongMod, then use simp / omega.
example : eqClass (CongMod 2) 0 = { n : ℤ | 2 ∣ n } := by
  sorry


-- ============================================================================
-- ### Challenging
-- ============================================================================

-- (7) The intersection of two equivalence relations is an equivalence relation.
-- (Check all three axioms; each requires only one line.)
example {α : Type*} (R S : α → α → Prop)
    (hR : Equivalence R) (hS : Equivalence S) :
    Equivalence (fun a b => R a b ∧ S a b) where
  refl  := by sorry
  symm  := by sorry
  trans := by sorry

-- (8) The class [a] under the f-kernel is exactly the fiber f ⁻¹' {f a}.
-- This makes precise: "the equivalence classes of fKernel f are the level
-- sets of f."
-- Hint: unfold fKernel and eqClass; the key step is `eq_comm`.
example {α β : Type*} (f : α → β) (a : α) :
    eqClass (fKernel f) a = f ⁻¹' {f a} := by
  sorry

-- (9) Prove the other half of parity_partition: if n is NOT in [0],
-- it must be in [1].  (Use parity_partition directly.)
example (n : ℕ) (h : n ∉ eqClass SameParity 0) :
    n ∈ eqClass SameParity 1 := by
  sorry

-- (10) A partition defines an equivalence relation — the converse direction
-- of the Partition Theorem.
-- Given A and B that cover α and are disjoint, the relation
-- "a and b lie in the same piece" is an equivalence relation.
example {α : Type*} (A B : Set α)
    (hcover : ∀ x : α, x ∈ A ∨ x ∈ B)
    (hdisj  : A ∩ B = ∅) :
    Equivalence (fun a b => (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B)) where
  refl  := by
    intro a
    sorry
  symm  := by
    intro a b h
    sorry
  trans := by
    intro a b c hab hbc
    -- Hint: if a and b are in the same piece, and b and c are in the same
    -- piece, show a and c are in the same piece.  Use hdisj to rule out
    -- b being in both A and B simultaneously.
    sorry

/-
In Lean/Mathlib, many familiar relations are already defined:
  `(· ≤ ·)` on ℕ, ℤ, ℝ         — "less than or equal"
  `(· ∣ ·)` on ℕ, ℤ             — "divides"
  `(· ⊆ ·)` on Set α            — "is a subset of"
-/
-- Some familiar relations:
#check (· ≤ · : ℕ → ℕ → Prop)    -- the ≤ relation on ℕ
#check (· ∣ · : ℕ → ℕ → Prop)    -- the divisibility relation on ℕ

-- Let's prove these properties for specific relations.

-- ### Divisibility on ℕ

-- Reflexive: every number divides itself
example : Reflexive (· ∣ · : ℕ → ℕ → Prop) := by
  intro x
  use 1
  linarith

-- Transitive: if a ∣ b and b ∣ c then a ∣ c
example : Transitive (· ∣ · : ℕ → ℕ → Prop) := by
  rintro a b c ⟨k, b_mult_a⟩ ⟨m, c_mult_b⟩
  dsimp [Dvd.dvd]
  have : c = a * (k * m) := by
    calc
      c = (a * k) * m := by
        rw [← b_mult_a]
        exact c_mult_b
      _ = a * (k * m) := by
        rw [mul_assoc]
  use (k * m)


-- NOT symmetric: 2 ∣ 4 but ¬ (4 ∣ 2)
example : ¬ Symmetric (· ∣ · : ℕ → ℕ → Prop) := by
  sorry

-- Prove that ≤ on ℕ is reflexive:
example : Reflexive (· ≤ · : ℕ → ℕ → Prop) := by
  sorry

-- Prove that ≤ on ℕ is transitive:
example : Transitive (· ≤ · : ℕ → ℕ → Prop) := by
  sorry

-- Prove that ≤ on ℕ is NOT symmetric:
example : ¬ Symmetric (· ≤ · : ℕ → ℕ → Prop) := by
  sorry

-- Prove that ≤ on ℕ is antisymmetric:
example : ∀ (a b : ℕ), a ≤ b → b ≤ a → a = b := by
  sorry

-- Prove that < on ℕ is irreflexive:
example : Irreflexive (· < · : ℕ → ℕ → Prop) := by
  sorry

-- Prove that < on ℕ is transitive:
example : Transitive (· < · : ℕ → ℕ → Prop) := by
  sorry

-- Prove that < on ℕ is asymmetric:
-- (Hint: if a < b and b < a, derive a contradiction.)
example : ∀ (a b : ℕ), a < b → ¬ (b < a) := by
  sorry
