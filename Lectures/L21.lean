import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Irrational

/- # Lecture 21: Archimedean Property and Density of `ℚ` in `ℝ`

New concepts: **Int.floor, #search**
Recall: **linarith, nlinarith, field_simp, positivity, push_cast, exact_mod_cast, norm_num, obtain, use, have, calc, intro, apply, constructor**

## Overview

Today we prove two beautiful facts in analysis.
First, between any two distinct real numbers **there is a rational number**.
Second — and equally surprisingly — **there is also an irrational number**.
Both `ℚ` and `ℝ \ ℚ` are *dense* in `ℝ`.

This is striking because `ℚ` is countable while `ℝ` is uncountable.
So "almost all" real numbers are irrational — yet rationals are
everywhere.  And the irrationals, despite being uncountable, are no more
"spread out" than the rationals.

The proofs use the **Archimedean property** and the **floor function**.  We
build from three lemmas, then assemble the main theorem.

### An Interesting Fact: Dedekind's Cut

In 1858, while teaching calculus in Zurich, Richard Dedekind realized he could
not rigorously prove that a monotone bounded sequence converges — because `ℝ`
had no proper definition.  His 1872 solution: partition `ℚ` into two nonempty
sets `L` and `R` such that every element of `L` is less than every element of
`R`.  Each such partition — a **Dedekind cut** — defines a real number.  The
cut for `√2` is `L = { q ∈ ℚ : q < 0 ∨ q² < 2 }`.  The density of `ℚ` in
`ℝ`, which we prove today, is the starting point of this construction.

# Nicholas Notes
Dr. Cherkis prefers ⌊x⌋ over ↑x to cast from ℝ to ℤ as it is more specific about casting direction.
-/


-- ============================================================================
-- ## Part 1: The Archimedean Property in Depth
-- ============================================================================

/-
Recall from Lecture 20: `ℝ` is **Archimedean**, meaning for every real `x`
there is a natural number `n` with `n > x`.

The Archimedean property says `ℕ` reaches every corner of `ℝ`.  We now extract
two consequences that drive the density proof.
-/

#check exists_nat_gt         -- (x : R) :  ∃ n : ℕ, x < ↑n
#check exists_nat_one_div_lt -- (hε : 0 < ε) : ∃ n : ℕ, 1 / (↑n + 1) < ε

/-
**Consequence**: for any `ε > 0`, we can find `n ∈ ℕ` such that `1/n < ε`.
This will underpin every ε-N argument in Stage 11.
-/

theorem archimedean_inv (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ 1 / (↑n : ℝ) < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n + 1, Nat.succ_pos n, ?_⟩
  push_cast
  exact hn
-- alternatively
--   use n+1
-- constructor
-- . apply Nat.succ_pos n
-- . exact_mod_cast hn

/-
**There is no smallest positive real number.**
Given any `x > 0`, we can find a smaller positive real (for instance `x/2`).
This distinguishes `ℝ` and `ℚ` from `ℕ` and `ℤ`.
-/

theorem no_smallest_positive (x : ℝ) (hx : 0 < x) :
    ∃ y : ℝ, 0 < y ∧ y < x := by
  use x / 2
  constructor <;> linarith

-- NOTE: a way of searching for a theorem via LeanSearch (or Moogle)
#search "div_lt_iff₀?"

-- Exercise (Part 1): The classical Archimedean property says every real is
-- exceeded by some multiple of any positive number.
example (a b : ℝ) (ha : 0 < a) : ∃ n : ℕ, b < ↑n * a := by
  suffices ∃n : ℕ, (b / a) < ↑n by simp [← div_lt_iff₀ ha,this]
  apply exists_nat_gt



-- Exercise (Part 1): Every real number is bounded in absolute value by some
-- natural number.
example (x : ℝ) : ∃ n : ℕ, |x| < ↑n := by
  simp [exists_nat_gt]




-- ============================================================================
-- ## Part 2: The Floor Function
-- ============================================================================

/-
The **floor** of a real number `x`, written `⌊x⌋`, is the greatest integer
`≤ x`.  For example, `⌊3.7⌋ = 3` and `⌊-1.2⌋ = -2`.

In Lean, the floor function for reals is `Int.floor`:
-/

#check Int.floor
#check Int.floor_le          -- ⌊a⌋ ≤ a
#check Int.lt_floor_add_one  -- a < ⌊a⌋ + 1

-- The two key properti es say exactly that `⌊x⌋ ≤ x < ⌊x⌋ + 1`:
example (x : ℝ) : (⌊x⌋ : ℝ) ≤ x ∧ x < ↑⌊x⌋ + 1 :=
  ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

-- Concrete examples (on `ℚ`, where `#eval` works):
#eval ⌊(3.7 : ℚ)⌋    -- 3
#eval ⌊(-1.2 : ℚ)⌋   -- -2

/-
**Lemma (integer between)**: If two real numbers are more than `1` apart,
there is an integer strictly between them.

*Strategy*: since `⌊a⌋` is the greatest integer `≤ a`, we know `a < ⌊a⌋ + 1`.
And `⌊a⌋ ≤ a` implies `⌊a⌋ + 1 ≤ a + 1 < b`.  So `m = ⌊a⌋ + 1` lands
between `a` and `b`.
-/

lemma int_between {a b : ℝ} (h : a + 1 < b) :
    ∃ m : ℤ, a < (m : ℝ) ∧ m < b := by
  use ⌊a⌋ + 1
  constructor
  · -- a < ⌊a⌋ + 1 is exactly `Int.lt_floor_add_one`:
    exact_mod_cast Int.lt_floor_add_one a
  · -- ⌊a⌋ + 1 < b: since ⌊a⌋ ≤ a, we have ⌊a⌋ + 1 ≤ a + 1 < b.
    have h1 : ((⌊a⌋ : ℝ) + 1) ≤ a + 1 := by linarith [Int.floor_le a]
    push_cast
    linarith

-- Exercise (Part 2): The floor function shifts by integer translation.
-- Hint: search for a Mathlib lemma, or use the characterization: an integer
-- `m` equals `⌊y⌋` iff `↑m ≤ y ∧ y < ↑m + 1`.
example (x : ℝ) (n : ℤ) : ⌊x + ↑n⌋ = ⌊x⌋ + n := by
  rw [← Int.floor_add_intCast]

-- Exercise (Part 2): Characterize the floor by trapping `x` in a unit interval.
-- Hint: prove `⌊x⌋ ≤ m` and `m ≤ ⌊x⌋` using `Int.floor_le` and `Int.le_floor`.
example (x : ℝ) (m : ℤ) (h₁ : (m : ℝ) ≤ x) (h₂ : x < (m : ℝ) + 1) :
    ⌊x⌋ = m := by
  simp_all [Int.floor_eq_iff]
  -- gives the same result:
  -- aesop (add simp Int.floor_eq_iff)


-- ============================================================================
-- ## Part 3: Density of ℚ in ℝ — The Full Proof
-- ============================================================================

/-
We now prove the main theorem.  The strategy has three steps:
 1. Scale the interval `(x, y)` by a large natural number `n` so that
    the length `n(y - x)` exceeds `1`.
 2. Find an integer `m` in the scaled interval `(nx, ny)`.
 3. Divide back by `n` to get the rational `m/n` in `(x, y)`.
-/

/-
**Lemma A (scaling)**: For `x < y`, there exists `n ∈ ℕ` with `0 < n`
and `n · x + 1 < n · y`.

The gap `y - x` may be tiny, but the Archimedean property gives us `n` so
large that `n(y - x) > 1`.  Once the scaled interval has length > 1, the
floor function guarantees an integer inside.
-/

lemma scaling_lemma {x y : ℝ} (hxy : x < y) :
    ∃ n : ℕ, 0 < n ∧ ↑n * x + 1 < ↑n * y := by
  have hd : 0 < y - x := by linarith
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
  use n+1
  constructor
  . exact Nat.succ_pos n
  . push_cast
    have hn_pos : (0 : ℝ) < (↑n : ℝ) + 1 := by positivity
    have hmul : 1 < (y - x) * ((↑n : ℝ) + 1) := by
       exact (div_lt_iff₀ hn_pos).mp hn
    nlinarith

-- **Lemma B** is `int_between` from Part 2.

/-
### The Main Theorem: Density of ℚ in ℝ

**Theorem.** For every `x, y ∈ ℝ` with `x < y`, there exists `q ∈ ℚ` such that `x < q < y`.
-/

theorem density_of_rationals {x y : ℝ} (hxy : x < y) :
    ∃ q : ℚ, x < ↑q ∧ (↑q : ℝ) < y := by
  -- Step 1: Find `n` with `0 < n` and `n·x + 1 < n·y`.
  obtain ⟨n, hn_pos, hn⟩ := scaling_lemma hxy
  -- Step 2: Find an integer `m` with `n·x < m < n·y`.
  obtain ⟨m, hm_lo, hm_hi⟩ := int_between hn
  -- Step 3: Set `q = m / n : ℚ`.  Show `x < q < y`.
  use (m/n : ℚ)
  have hn_pos_real : (0 : ℝ) < ↑n := by exact_mod_cast hn_pos
  constructor <;> push_cast
  . rw [lt_div_iff₀]; linarith; exact hn_pos_real
  . rw [div_lt_iff₀]; linarith; exact hn_pos_real

/-
That is our proof, built from three clean lemmas.
Mathlib provides the same statement as `exists_rat_btwn`:
-/
#check exists_rat_btwn

/-
Knowing the theorem name is valuable: the manual proof teaches the technique
(Archimedean scaling + floor), while `exists_rat_btwn` lets you move quickly
in later proofs.

`ℚ` is countable — we proved this in Stage 7.  Yet it is dense in the
uncountable `ℝ`.  Between any two of the uncountably many reals, we can always
squeeze in a rational.  Countable does not mean sparse.
-/

-- Exercise (Part 3): Between any two rationals there is a third.
-- Hint: you can even construct such a rational
example (p q : ℚ) (h : p < q) :
    ∃ r : ℚ, p < r ∧ r < q := by
  sorry

-- Exercise (Part 3): You can approximate any real from above by a rational
-- within any prescribed error.
example (x ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℚ, x < ↑q ∧ (↑q : ℝ) < x + ε := by
  sorry


-- ============================================================================
-- ## Part 4: Density of Irrationals in ℝ
-- ============================================================================

/-
The density of `ℚ` might suggest that rationals are special.  But the
irrationals are equally dense: between any two distinct reals there is an
irrational number.

*Proof idea*: shift the interval by `√2`.  Apply density of `ℚ` to the shifted
interval `(a - √2, b - √2)` to find a rational `q` with
`a - √2 < q < b - √2`.  Then `z = q + √2` is irrational (a rational plus an
irrational is irrational) and satisfies `a < z < b`.
-/

theorem density_of_irrationals {a b : ℝ} (hab : a < b) :
    ∃ z : ℝ, Irrational z ∧ a < z ∧ z < b := by
  -- Apply density of ℚ to the shifted interval (a - √2, b - √2).
  have abshift : a - Real.sqrt 2 < b - Real.sqrt 2 := by linarith
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn abshift
  use q + √2
  constructor
  · -- z is irrational: a rational plus an irrational is irrational.
    apply Irrational.ratCast_add
    exact irrational_sqrt_two
  constructor <;> linarith

/-
Both `ℚ` and `ℝ \ ℚ` are dense in `ℝ`.  This makes `ℝ` much richer than
either part alone: no matter how closely you zoom in on the real line, you will
always find both rational and irrational numbers.
-/

#check Irrational.ratCast_add

-- Exercise (Part 4): Show that every open interval contains a rational number
-- and a larger irrational number.
example (a b : ℝ) (hab : a < b) :
    ∃ q : ℚ, ∃ z : ℝ, a < ↑q ∧ (↑q : ℝ) < z ∧ z < b ∧ Irrational z := by
  sorry

-- Exercise (Part 4): Between any two distinct reals there are two distinct
-- irrational numbers.
example (a b : ℝ) (hab : a < b) :
    ∃ z₁ z₂ : ℝ, Irrational z₁ ∧ Irrational z₂ ∧ a < z₁ ∧ z₁ < z₂ ∧ z₂ < b := by
  sorry


-- ============================================================================
-- ## Part 5: Preview — Toward ε-N Reasoning
-- ============================================================================

/-
We are going to define convergence of a sequence `a : ℕ → ℝ` to a limit
`L` by:

  `∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |a n - L| < ε`

The Archimedean property is the key tool: given `ε > 0`, we find `N` so that
`1/(N + 1) < ε`, then argue that sequence terms are within `ε` of `L` for all
`n ≥ N`.  The `archimedean_inv` theorem from Part 1 already provides this.
-/

-- Exercise (Part 5): For any `ε > 0`, there is a positive rational less than `ε`.
-- Hint: use `exists_rat_btwn` on `(0, ε)`.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ q : ℚ, 0 < (↑q : ℝ) ∧ (↑q : ℝ) < ε := by
  apply density_of_rationals (x := 0) (y := ε) hε

#check one_div_le_one_div_of_le
-- Exercise (Part 5): Strengthen `exists_nat_one_div_lt` to an eventual bound
-- that works for every larger index.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 / (↑n + 1 : ℝ) < ε := by
  sorry


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================


-- ============================================================================
-- ### Warm-up
-- ============================================================================

-- (1) Every real number is within `1` of some integer.
example (x : ℝ) : ∃ m : ℤ, |x - ↑m| < 1 := by
  sorry

-- (2) The fractional part of any real number lies in `[0, 1)`.
example (x : ℝ) : 0 ≤ x - ↑⌊x⌋ ∧ x - ↑⌊x⌋ < 1 := by
  sorry

-- (3) The midpoint of distinct reals lies strictly between them.
example (a b : ℝ) (h : a < b) : a < (a + b) / 2 ∧ (a + b) / 2 < b := by
  sorry


-- ============================================================================
-- ### Core
-- ============================================================================

-- (4) The Archimedean squeeze: if a nonnegative real is smaller than every
-- `1/n`, it must be zero. This is the single most-used consequence of the
-- Archimedean property in analysis.
example (x : ℝ) (hx : 0 ≤ x) (h : ∀ n : ℕ, 0 < n → x ≤ 1 / (↑n : ℝ)) :
    x = 0 := by
  sorry



#check abs_lt
-- (6) Every real can be approximated by a rational to any precision.
example (x ε : ℝ) (hε : 0 < ε) : ∃ q : ℚ, |x - ↑q| < ε := by
  sorry




-- ============================================================================
-- ### Challenging
-- ============================================================================

#check abs_pos.mpr
-- (8) Two reals that are within `1/n` of each other for every positive `n`
-- must be equal. This is the metric-space Archimedean squeeze.
example (x y : ℝ) (h : ∀ n : ℕ, 0 < n → |x - y| ≤ 1 / (↑n : ℝ)) :
    x = y := by
  sorry


-- (9) Preparation for `√2`: the set `{x : ℝ | x ^ 2 ≤ 2}` is nonempty
-- and bounded above, so completeness gives it a supremum.
example : (1 : ℝ) ∈ {x : ℝ | x ^ 2 ≤ 2} ∧
    ∃ B : ℝ, ∀ x ∈ {x : ℝ | x ^ 2 ≤ 2}, x ≤ B := by
  sorry

#check Int.floor_le
#check Int.lt_floor_add_one
-- (10) For any real `x`, some integer is within `1` of `n · x`. This is the
-- starting point of Dirichlet's approximation theorem.
example (x : ℝ) (n : ℕ) : ∃ m : ℤ, |↑n * x - ↑m| < 1 := by
  sorry
