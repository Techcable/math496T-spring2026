import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

--! # Homework 11: Topology, Continuity, IVT, and EVT

/-!
This homework covers Lectures 26-29.

Topics: open sets, closure points (sequential characterization),
ε-δ continuity, the Intermediate Value Theorem, and the Extreme Value
Theorem for sequentially compact subsets of `ℝ`.

**Total: 50 points.**

The definitions below reproduce those introduced in L26–L29 so that this
homework is self-contained.
-/

/-- A set `U ⊆ ℝ` is **open** if every point has an ε-neighborhood in `U`. -/
def IsOpenSet (U : Set ℝ) : Prop :=
  ∀ x ∈ U, ∃ ε > 0, ∀ y, |y - x| < ε → y ∈ U

/-- `x` is a **closure point** of `S` if every ε-neighborhood of `x` meets `S`. -/
def IsClosurePt (x : ℝ) (S : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ y ∈ S, |y - x| < ε

/-- `a n → L` in the ε-N sense. -/
def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε

/-- `f` is **continuous at `c`** in the ε-δ sense. -/
def ContAt (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

/-- We already proved the Intermediate Value Theorem (IVT) -/
axiom IVT (f : ℝ → ℝ) {a b : ℝ} (hab : a < b)
    (hcont : ∀ c ∈ Set.Icc a b, ContAt f c)
    (hfa : f a < 0) (hfb : 0 < f b) :
    ∃ c ∈ Set.Ioo a b, f c = 0

/-- We also proved the Extreme Value Theorem (EVT) in lecture 29 -/
axiom evt_min (hab : (a:ℝ) ≤ b)
    {f : ℝ → ℝ} (hcont : ∀ c ∈ Set.Icc a b, ContAt f c) :
    ∃ xmin ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f xmin ≤ f x

-- ============================================================================
-- Problem 1: Open intervals are open
-- ============================================================================

/-
Prove that the open interval `(a, b)` is open.
-/

#check min_le_right -- min a b ≤ b

example (a : ℝ) : 0<a → 0<√a := by apply Real.sqrt_pos_of_pos

example (a b c :ℝ) : a * b / c = a * (b/c) := by apply mul_div_assoc

@[autogradedProof 9]
theorem problem1 (a b : ℝ) : IsOpenSet (Set.Ioo a b) := by
  dsimp [IsOpenSet]
  intro x xMem
  have ⟨xGta,xLtB⟩ := xMem
  let dist : ℝ := min (x - a) (b - x)
  let ε := dist / 2
  have εPos : ε > 0 := by simp [dist,ε]; assumption
  use ε
  simp_all
  intro y yDist
  have hε := abs_lt.mp yDist
  constructor
  . have eSmall : ε < (x - a) := by
      suffices dist <= x - a by dsimp [ε,dist]; linarith
      apply min_le_left
    show a < y
    calc
      a < x - ε := by linarith
      _ < x + (y - x) := by linarith
      _ = y := by linarith
  . have eSmall : ε < (b - x) := by
      suffices dist <= b - x by dsimp [ε,dist]; linarith
      apply min_le_right
    suffices b > y by simp_all
    calc
      b = x + (b - x) := by linarith
      _ > x + ε := by linarith
      _ > y := by linarith

-- ============================================================================
-- Problem 2: Sequence → closure point (forward direction)
-- ============================================================================

/-
If a sequence `a : ℕ → ℝ` takes values in `S` and converges to `x`,
then `x` is a closure point of `S`.
-/

example (a : ℝ) : a ≤ a := le_refl a

@[autogradedProof 7]
theorem problem2 (S : Set ℝ) (x : ℝ) (a : ℕ → ℝ)
    (haS : ∀ n, a n ∈ S) (hconv : ConvergesTo a x) :
    IsClosurePt x S := by
  dsimp [IsClosurePt]
  intro ε εPos
  have ⟨N,hN⟩ := hconv ε εPos
  use a N
  constructor
  . exact haS N
  . exact hN N (by simp)


-- ============================================================================
-- Problems 3 and 4 : Identity and affine functions are continuous
-- ============================================================================

/-
4 (4 pts): The identity function is continuous at every point.
-/

@[autogradedProof 6]
theorem problem3 (c : ℝ) : ContAt (fun x => x) c := by
  intro ε εPos
  use ε
  simp_all

/-
4 (4 pts): Every affine function `x ↦ m * x + b` is continuous
at every `c`.
-/

@[autogradedProof 8]
theorem problem4 (m b c : ℝ) : ContAt (fun x => m * x + b) c := by
  dsimp [ContAt]
  intro ε εPos
  let factor := |m| + 1
  have factor.pos : factor > 0 := by positivity
  use (ε / factor)
  constructor
  . positivity
  . intro x hxDist
    simp
    show |m * x - m * c| < ε
    have hxDist' : factor * |x - c| < ε := by
      rw [mul_comm]
      exact (lt_div_iff₀ (by positivity)).mp hxDist
    calc
          |m * x - m * c|
      _ = |m * (x - c)| := by rw [← mul_sub]
      _ = |m| * |x - c| := by rw [abs_mul]
      _ ≤ factor * |x - c| := by
        apply mul_le_mul_of_nonneg_right
        . linarith
        . positivity
      _ < ε := hxDist'


-- ============================================================================
-- Problem 5 : Fixed-point theorem via IVT (strict-sign form)
-- ============================================================================

/-
If `f : ℝ → ℝ` is continuous on `[0, 1]` with `0 < f 0` and `f 1 < 1`,
then `f` has a fixed point in `(0, 1)`: some `c ∈ (0, 1)` with `f c = c`.

Hint:
Either apply the Intermediate Value Theorem to a new function you introduce
or (longer) prove it directly via separations and connectedness of `[0, 1]` (L27).
-/

#check IVT -- (f : ℝ → ℝ) → ((a : ℝ) < b) → (∀ c ∈ Set.Icc a b, ContAt f c) → f a < 0 → 0 < f b → ∃ c ∈ Set.Ioo a b, f c = 0
#check sub_eq_zero -- a - b = 0 ↔ a = b

@[autogradedProof 13]
theorem problem5 (f : ℝ → ℝ)
    (hcont : ∀ c ∈ Set.Icc (0 : ℝ) 1, ContAt f c)
    (h0 : 0 < f 0) (h1 : f 1 < 1) :
    ∃ c ∈ Set.Ioo (0 : ℝ) 1, f c = c := by
  let S := Set.Icc (0 : ℝ) 1
  let g : ℝ → ℝ := fun x => x - f x
  have gcont : ∀ x ∈ S, ContAt g x := by
    intro x xS
    dsimp [ContAt]
    intro ε εPos
    have ⟨δ,δPos,hδ⟩ := hcont x (by simp_all [Set.Icc,S]) (ε/2) (by positivity)
    let δ' := min δ (ε / 2)
    use δ'
    constructor
    . positivity
    . intro y yBound
      have distSmall : |x - y| < ε / 2 := by
        have : δ' ≤ ε / 2 := by apply min_le_right
        rw [abs_sub_comm]
        linarith
      have yBound' : |y - x| < δ := by
        calc
            |y - x|
          _ < δ' := by assumption
          _ ≤ δ := by apply min_le_left
      have fDistSmall : |f y - f x| < ε / 2 := hδ y yBound'
      -- i originally proved this for -g, so proved |(-g) y - (-g) x| < ε
      -- Due to linarith playing poorly with abs, I had to do everything by hand
      -- As a result, it is easier to rearrange the norm and then reuse my proof for -g
      calc
            |g y - g x|
        _ = |-(g y - g x)| := by rw [abs_neg]
        _ = |-(g y) - -(g x)| := by rw [neg_sub']
        _ = |-(y - f y) - -(x - f x)| := by dsimp [g]
        -- now this is my original proof
        _ = |(f y - y) - (f x - x)| := by rw [neg_sub,neg_sub]
        _ = |f y - y - f x + x| := by rw [sub_add]
        _ = |f y - f x - y + x| := by simp [sub_right_comm]
        _ = |(f y - f x) + (x - y)| := by rw [add_comm_sub]
        _ ≤ |f y - f x| + |x - y| := by apply abs_add_le
        _ < |f y - f x| + (ε / 2) := by linarith
        _ < ε := by linarith
  have g.upper : g 1 > 0 := by simp [g]; assumption
  have g.lower : g 0 < 0 := by simp [g]; assumption
  obtain ⟨c,hMem,cfixpoint⟩ := @IVT g 0 1 (by linarith) gcont g.lower g.upper
  use c
  constructor
  . assumption
  . linarith

#check abs_add

-- ============================================================================
-- Problem 6 : Positive continuous functions have a positive lower
-- bound on a closed interval
-- ============================================================================

/-
If `f : ℝ → ℝ` is continuous on `[a, b]` and strictly positive there,
then `f` has a strictly positive lower bound:
there is `m > 0` with `m ≤ f x` for every `x ∈ [a, b]`.

Hint: the minimum half of the Extreme Value Theorem (L29) `evt_min` provides some
`xmin ∈ [a, b]` attaining the minimum of `f`; set `m := f xmin`.
-/

#check evt_min -- (a:ℝ ≤ b) → (∀ c ∈ Icc a b, ContAt f c)
               --  →  ∃ xmin ∈ Icc a b, ∀ x ∈ K, f xmin ≤ f x

@[autogradedProof 7]
theorem problem6 (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ∀ c ∈ Set.Icc a b, ContAt f c)
    (hpos : ∀ x ∈ Set.Icc a b, 0 < f x):
    ∃ m > 0, ∀ x ∈ Set.Icc a b, m ≤ f x := by
    have ⟨m,mRange,mLowerBound⟩ := evt_min hab hcont
    use (f m)
    constructor
    . exact hpos m mRange
    . exact mLowerBound
