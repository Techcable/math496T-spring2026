import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Rat.Cast.Order

/- # Lecture 20: From `ℕ` to `ℚ` to `ℝ` — The Number Systems

New tactics: **linarith, nlinarith, field_simp, positivity, push_cast**
Recall: **intro, exact, apply, use, obtain, rcases, simp, rw, ring, norm_num, omega, constructor, by_contra, push_neg, have, calc, gcongr**

## Overview

We climb the number ladder `ℕ ↪ ℤ ↪ ℚ ↪ ℝ`.  Each step repairs a deficiency:
`ℕ` has no subtraction, `ℤ` has no division, and `ℚ` has "holes" — there is no
rational whose square is `2`.  The real numbers `ℝ` fill every such hole.

We learn to move between these types in Lean via **coercions** and the tactics
`push_cast` / `exact_mod_cast`.  Then we introduce five powerful tactics —
`linarith`, `nlinarith`, `field_simp`, `positivity`, `push_cast`.
-/

-- ============================================================================
-- ## Part 1: Coercions Between Number Systems
-- ============================================================================

/-
`ℕ` has addition and multiplication but no subtraction: there is no natural
number `x` with `x + 3 = 0`.  `ℤ` adds negatives but lacks division: there
is no integer `x` with `2 * x = 1`.  That is where `ℚ` enters.

In Lean, we move from `ℕ` to `ℤ` with a **type coercion** written `↑`:
-/

section NatToInt

def n : ℕ := 5
#check n        -- n : ℕ
#check (n : ℤ)  -- ↑n : ℤ
#eval (n : ℤ)  -- 5
#check ((5 : ℕ) : ℤ)  -- ↑5 : ℤ


-- Its opposite of coercion is *truncation*:
#check (Int.toNat (5 : ℤ) : ℕ)
-- Be careful:
#eval (Int.toNat (5 : ℤ))   -- 5
#eval (Int.toNat (-5 : ℤ))  -- 0

end NatToInt

-- The coercion preserves arithmetic:
example (n m : ℕ) : (↑(n + m) : ℤ) = ↑n + ↑m := by push_cast; rfl
example (n m : ℕ) : (↑(n * m) : ℤ) = ↑n * ↑m := by push_cast; rfl

-- **Going back**: if two natural numbers are equal as integers,
-- they are equal as natural numbers.  The key tool is `Nat.cast_inj`:
#check @Nat.cast_inj ℤ  -- (↑n : ℤ) = ↑m ↔ n = m

example (n m : ℕ) (h : (↑n : ℤ) = ↑m) : n = m := by
  exact_mod_cast h

-- The tactic `exact_mod_cast` handles cast-related reasoning.

-- Prove that the coercion `ℕ → ℤ` preserves strict order.
example (n m : ℕ) (h : n < m) : (↑n : ℤ) < ↑m := by
  exact_mod_cast h


-- ============================================================================
-- ## Part 2: The Rational Numbers ℚ
-- ============================================================================

/-
`ℚ` is the first number system where we can divide by any nonzero element.
Such a system is called a **field**.  Since `ℚ` also has a total order `≤`
compatible with its arithmetic, it is a **linearly ordered field**.

**How Lean stores a rational number**: internally, each `q : ℚ` is a pair
(numerator, denominator) always kept in *lowest terms*.
-/

#eval (2/4 : ℚ)        -- 1/2
#eval ((2 / 4) : ℚ).num -- 1
#eval ((2/4) : ℚ).den -- 2
-- and
#eval (2 : ℚ) / 4          -- 1/2
#eval ((2 : ℚ) / 4).num    -- 1
#eval ((2 : ℚ) / 4).den    -- 2
-- Beware:
#eval (1 : ℚ) / 0          -- 0 (division by zero returns 0)

-- `norm_num` handles concrete numerical equalities and inequalities:
example : (2 : ℚ) / 4 = 1 / 2 := by norm_num
example : (3 : ℚ) / 7 < 1 / 2 := by norm_num
example : (1 : ℚ) / 3 + 1 / 6 = 1 / 2 := by norm_num

/-
**Coercion chain**: `ℕ ↪ ℤ ↪ ℚ`.
Every natural number is an integer, and every integer is a rational.
-/

example (n : ℕ) : (↑n : ℚ) = ↑(↑n : ℤ) := by push_cast; rfl
example (p q : ℤ) (h : (↑p : ℚ) = ↑q) : p = q := by exact_mod_cast h
-- working modulo (meaning "ignoring" or "normalizing") type casts or coercions.

/-
**What `ℚ` lacks**: *completeness*.

Consider `S = { q ∈ ℚ : q² < 2 }`.  This set is nonempty (`1 ∈ S`) and
bounded above (`2` is an upper bound).  Yet it has no *rational* least upper
bound — that number `s` would satisfy `s² = 2`, but no rational square
equals `2`.  The "missing number" is `√2`, which is irrational.

So `ℚ` has "holes."  The real numbers `ℝ` are what we get by filling those holes.
-/

-- A concrete rational inequality.
example : (1 : ℚ) / 3 + 1 / 4 < 2 / 3 := by
  norm_num



-- ============================================================================
-- ## Part 3: ℝ — The Axioms
-- ============================================================================

/-
We define `ℝ` by three axioms.  We do not *construct* `ℝ` yet — we state the
properties that characterize it.

**Axiom 1. `ℝ` is a linearly ordered field.**

Like `ℚ`, `ℝ` has `+`, `-`, `×`, `÷` (by nonzero), and a total order `≤`
compatible with the arithmetic.
-/

#check add_le_add    -- a ≤ b, c ≤ d → a + c ≤ b + d
#check mul_pos       -- 0 < a, 0 < b → 0 < a * b
#check div_pos       -- 0 < a, 0 < b → 0 < a / b
#check le_total      -- a ≤ b ∨ b ≤ a

-- Algebraic manipulations from `ℚ` also work in `ℝ`:
example (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by ring
example (a b c : ℝ) (h : a ≤ b) : a + c ≤ b + c := by gcongr

/-
**Axiom 2. `ℝ` is Archimedean.**

For every real `x`, there is a natural number `n` with `n > x`.  In other
words, `ℕ` is unbounded in `ℝ`.  Note: `ℚ` is also Archimedean, so this alone
does not distinguish `ℝ` from `ℚ`.
-/

#check exists_nat_gt    -- ∀ x, ∃ n : ℕ, x < ↑n

/-
**Axiom 3. `ℝ` is (Dedekind-)complete.**

Every nonempty set of real numbers that is bounded above has a least upper
bound (supremum).  This fills the "holes" in `ℚ`.
-/

-- `sSup s` is the least upper bound of `s` (if it exists).
#check IsLUB        -- `IsLUB s a` means `a` is a least upper bound of the set`s`
#check isLUB_csSup  -- nonempty + bounded above → `sSup s` is a least upper bound
#check le_csSup     -- every element of `s` ≤ the supremum
#check csSup_le     -- every upper bound ≥ the supremum

/-
**Theorem** (Uniqueness). These three properties — linearly ordered field,
Archimedean, complete — determine `ℝ` uniquely.

Completeness turns bounded approximation into a genuine number.  For
`{x : ℝ | x² < 2}`, there is now a least upper bound in `ℝ`, namely `√2`.

**Coercion `ℚ ↪ ℝ`**: every rational is a real.  The embedding preserves
arithmetic and order.
-/

example (p q : ℚ) (h : p < q) : (↑p : ℝ) < ↑q := by exact_mod_cast h
example (p q : ℚ) (h : (↑p : ℝ) = ↑q) : p = q := by exact_mod_cast h

/-
**The full coercion chain**: `ℕ ↪ ℤ ↪ ℚ ↪ ℝ`.
At each step the embedding is injective — we go back with `exact_mod_cast`.
-/

example (n m : ℕ) (h : (↑n : ℝ) = ↑m) : n = m := by exact_mod_cast h


-- Supremum EXERCISES:
-- Exercise (Part 3): Prove that the coercion `ℤ → ℝ` is injective.
example (a b : ℤ) (h : (↑a : ℝ) = ↑b) : a = b := by
  exact_mod_cast h

-- Practice with Supremum:
-- Uniqueness of the least upper bound
  theorem lubUnique (s : Set ℝ) (a b : ℝ) (ha : IsLUB s a) (hb : IsLUB s b) : a = b := by
    let ubounds := upperBounds s
    dsimp [IsLUB,IsLeast] at ha hb
    obtain ⟨aUp, aLowerUpper⟩ := ha
    obtain ⟨bUp, bLowerUpper⟩ := hb
    dsimp [lowerBounds] at aLowerUpper bLowerUpper
    have aLeB : a ≤ b := by
      exact aLowerUpper bUp
    have bLeA : b ≤ a := by
      exact bLowerUpper aUp
    apply le_antisymm aLeB bLeA



  -- Hint: `IsLUB` means `IsLeast (upperBounds s)`, so `ha.1` gives the
  -- upper-bound part and `ha.2` gives the least part. Use `le_antisymm`.

 -- A maximum element equals the supremum
  example (s : Set ℝ) (a : ℝ) (hs : s.Nonempty) (hbdd : BddAbove s)
      (hmem : a ∈ s) (hub : ∀ x ∈ s, x ≤ a) : sSup s = a := by
      simp [sSup,hs,hbdd]
      have lubA : IsLUB s a := by
        simp [IsLUB,IsLeast]
        dsimp [upperBounds]
        constructor
        . intro x
          exact hub x
        . dsimp [lowerBounds]
          intro x xUpper
          exact @xUpper a hmem
      have lubUnique : ∃! x, IsLUB s x := by
        use a
        constructor
        . exact lubA
        . intro y lubY
          exact lubUnique s y a lubY lubA
      let choice : ℝ := @Classical.choose ℝ (IsLUB s) lubUnique.exists
      show choice = a
      have choice_prop : IsLUB s choice := Classical.choose_spec lubUnique.exists
      exact lubUnique.unique choice_prop lubA


  -- Hint: `le_antisymm` with `csSup_le` and `le_csSup`.

  -- Monotonicity of supremum
  example (s t : Set ℝ) (hst : s ⊆ t) (hne : s.Nonempty) (hbdd : BddAbove t) :
      sSup s ≤ sSup t := by
    sorry
  -- Hint: use `csSup_le` and `le_csSup`.

  -- The epsilon characterization of supremum (Core)
  -- This is the single most-used property in analysis: you can always find an element of the set within any ε of the sup.

  example (s : Set ℝ) (hs : s.Nonempty) (hbdd : BddAbove s)(ε : ℝ) (hε : 0 < ε) : ∃ x ∈ s, sSup s - ε < x := by
    sorry
  -- Hint: argue by contradiction. If every x ∈ s satisfies x ≤ sSup s - ε,
  -- then `csSup_le` gives `sSup s ≤ sSup s - ε`, contradicting `hε`.
  -- Or: use `isLUB_csSup` and unfold `IsLUB`/`IsLeast` to get the
  -- contrapositive directly.

-- ============================================================================
-- ## Part 4: New Tactics — Worked Examples
-- ============================================================================

/-
We introduce five new tools through connected examples building toward the
**AM-GM inequality**.
-/

-- ### `linarith` — linear arithmetic over ordered fields
-- Closes goals that follow from hypotheses by linear combination.

example (a b : ℝ) (h : a < b) : a < (a + b) / 2 := by linarith

-- Exercise: the midpoint also lies below `b`.
example (a b : ℝ) (h : a < b) : (a + b) / 2 < b := by
  sorry

-- ### `nlinarith` — nonlinear arithmetic
-- Extends `linarith` to handle products and squares.

-- Every square is nonnegative:
example (a : ℝ) : 0 ≤ a ^ 2 := by nlinarith

-- The heart of AM-GM: `(a - b)² ≥ 0` rearranges to `2ab ≤ a² + b²`.
example (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (a - b)]

-- Exercise: if a sum of squares vanishes, each summand is zero.
example (a b : ℝ) (h : a ^ 2 + b ^ 2 = 0) : a = 0 := by
  sorry

-- ### `field_simp` — clear denominators
-- Eliminates denominators (given nonzero), turning fractions into polynomials.

example (a : ℝ) (ha : a ≠ 0) : 1 / a + 1 / a = 2 / a := by
  field_simp; ring

-- Exercise: for positive `x`, we have `x + 1/x ≥ 2` (AM-GM for `x` and `1/x`).
-- Hint: `field_simp`, then `nlinarith`.
example (x : ℝ) (hx : 0 < x) : 2 ≤ x + 1 / x := by
  sorry

-- ### `positivity` — prove nonnegativity or positivity

example (a : ℝ) : 0 ≤ a ^ 2 + 1 := by positivity
example (a b : ℝ) : 0 ≤ a ^ 2 + b ^ 2 := by positivity

-- Exercise: prove strict positivity.
example (a : ℝ) : (0 : ℝ) < a ^ 4 + 1 := by
  sorry

-- ### `push_cast` — normalize coercions
-- Expands `↑(n + m)` to `↑n + ↑m` so that `ring` or `linarith` can finish.

example (n m : ℕ) : (↑(n + m) : ℝ) = (↑n : ℝ) + ↑m := by push_cast; ring
example (n m : ℕ) : (↑(n * m) : ℝ) = (↑n : ℝ) * ↑m := by push_cast; ring
example (n : ℕ) (hn : 0 < n) : (0 : ℝ) < ↑n := by exact_mod_cast hn

-- Exercise: a polynomial identity survives the coercion `ℕ → ℝ`.
example (n : ℕ) : ((n ^ 2 + 1 : ℕ) : ℝ) = (↑n : ℝ) ^ 2 + 1 := by
  sorry


-- ============================================================================
-- ## Part 5: Absolute Value
-- ============================================================================

/-
The **absolute value** `|x|` measures distance from zero.  Key properties:
`|x| ≥ 0`, `|x| = 0 ↔ x = 0`, `|xy| = |x||y|`, and the
**triangle inequality** `|x + y| ≤ |x| + |y|` — the single most important
tool in analysis.
-/

#check @abs_nonneg ℝ _     -- 0 ≤ |a|
#check @abs_add ℝ _        -- |a + b| ≤ |a| + |b|
-- Distance is symmetric: `|a - b| = |b - a|`
example (a b : ℝ) : |a - b| = |b - a| := by rw [abs_sub_comm]

-- A useful characterization: `|a| ≤ b ↔ -b ≤ a ∧ a ≤ b`:
#check @abs_le ℝ _

example (x : ℝ) (h : |x| ≤ 3) : -3 ≤ x := by
  have := abs_le.mp h
  linarith

-- Exercise (Part 5): Deduce a bound from an absolute-value hypothesis.
-- Hint: use `abs_lt` to unpack the hypothesis, then `linarith`.
example (x : ℝ) (h : |x - 3| < 1) : 2 < x := by
  sorry


-- ============================================================================
-- ## End-of-Lecture Exercises
-- ============================================================================


-- ============================================================================
-- ### Warm-up
-- ============================================================================

-- (1) A point to the left of `c` is certainly to the left of `c + 1`.
-- Hint: `linarith`.
example (a b c : ℝ) (h₁ : a ≤ b) (h₂ : b < c) : a < c + 1 := by
  sorry

-- (2) A shifted square is never negative.
-- Hint: `nlinarith`.
example (x : ℝ) : 0 ≤ x ^ 2 - 2 * x + 1 := by
  sorry

-- (3) An odd natural number has the same value when viewed in `ℝ`.
-- Hint: `push_cast`, then `ring`.
example (n : ℕ) : (↑(2 * n + 1) : ℝ) = 2 * (↑n : ℝ) + 1 := by
  sorry

-- (4) A classical Egyptian-fraction identity.
-- Hint: `norm_num`.
example : (1 : ℚ) / 2 + 1 / 3 + 1 / 6 = 1 := by
  sorry


-- ============================================================================
-- ### Core
-- ============================================================================

-- (5) Rewrite this expression as a single fraction.
-- Hint: `field_simp`, then `ring`.
example (x : ℝ) (hx : x ≠ 0) : x + 1 / x = (x ^ 2 + 1) / x := by
  sorry

-- (6) The AM-GM inequality for two nonnegative reals.
-- Hint: `nlinarith`.
example (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ (a + b) ^ 2 / 4 := by
  sorry

-- (7) Consecutive natural numbers do not collapse when viewed inside `ℝ`.
example (n m : ℕ) (h : (↑n : ℝ) + 1 = (↑m : ℝ) + 1) : n = m := by
  sorry

-- (8) Two numbers of size less than `1` have sum of size less than `2`.
-- Hint: use the triangle inequality together with `linarith`.
example (x y : ℝ) (hx : |x| < 1) (hy : |y| < 1) : |x + y| < 2 := by
  sorry

-- (9) Translating every element by `c` shifts the supremum by `c`.
-- Hint: `le_antisymm`; for each direction use `csSup_le` on one side
-- and `le_csSup` on the other. Unpack set-builder membership with
-- `obtain ⟨y, hy, rfl⟩`. Finish with `linarith` or `gcongr`.
example (s : Set ℝ) (c : ℝ) (hs : s.Nonempty) (hbdd : BddAbove s) :
    sSup { x + c | x ∈ s } = sSup s + c := by
  sorry

-- ============================================================================
-- ### Challenging
-- ============================================================================

-- (9) Half of a positive real is still positive, but strictly smaller.
-- Hint: `constructor <;> linarith`.
example (x : ℝ) (hx : 0 < x) : 0 < x / 2 ∧ x / 2 < x := by
  sorry

-- (10) The average of distinct reals lies strictly between them.
-- Hint: `constructor <;> linarith`.
example (a b : ℝ) (h : a < b) :
    a < (a + b) / 2 ∧ (a + b) / 2 < b := by
  sorry

-- (11) A rectangle with side lengths `n` and `n + 1` has positive area.
-- Hint: `push_cast`, then `positivity` or `nlinarith`.
example (n : ℕ) (hn : 0 < n) : (0 : ℝ) < ((↑n : ℝ) + 1) * ↑n := by
  sorry

-- WARNING: We are to cover the intervals in the next lecture
-- Ignore it, or look up `Set.Icc` definition.

-- (12) The supremum of the unit interval is `1`.
-- Hint: `le_antisymm`; use `csSup_le` with `fun x hx => hx.2` for `≤`,
-- and `le_csSup` with `1 ∈ Set.Icc 0 1` for `≥`.
-- You will need `bddAbove_Icc` for the `BddAbove` hypothesis.
example : sSup (Set.Icc (0 : ℝ) 1) = 1 := by
  sorry
