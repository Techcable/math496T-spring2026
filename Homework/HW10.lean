import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Ring.Parity

--! # Homework 10: Sequences and Limits

/-!
This homework covers Lectures 24-25.

Topics: epsilon-N convergence of sequences; divergence; order preservation
in limits; the Monotone Convergence Theorem; recursive sequences.

**Total: 5 problems, 50 points.**
-/


def ConvergesTo (a : ℕ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n, N ≤ n → |a n - L| < ε


-- ============================================================================
-- Problem 1 (6 points): A first epsilon-N proof
-- ============================================================================

/-
Prove that `1 / (2n + 1)` converges to `0`.
-/

#check exists_nat_one_div_lt
#check one_div_le_one_div_of_le

@[autogradedProof 6]
theorem problem1 : ConvergesTo (fun n => 1 / ((2 : ℝ) * n + 1)) 0 := by
  intro ε εPos
  have ⟨N,hN⟩ := exists_nat_one_div_lt εPos
  use N
  intro n nBound
  simp [-one_div]
  calc
      |1 / (2 * (n : ℝ) + 1)|
    _ = 1 / (2 * n + 1) := by exact abs_of_nonneg (by positivity)
    _ ≤ 1 / (n + 1) := by (
      apply one_div_le_one_div_of_le
      . positivity
      . linarith
    )
    _ ≤ 1 / (N + 1) := by (
      apply one_div_le_one_div_of_le
      . positivity
      . simp_all
    )
    _ < ε := hN


-- ============================================================================
-- Problem 2 (8 points): Order is preserved in the limit
-- ============================================================================

/-
If every term of a convergent sequence is at most `c`, then the limit is also
at most `c`.
-/

@[autogradedProof 8]
theorem problem2 (a : ℕ → ℝ) (L c : ℝ)
    (ha : ConvergesTo a L) (hc : ∀ n, a n ≤ c) : L ≤ c := by
  by_contra! limitLarger
  let ε := L - c
  have εPos : ε > 0 := by linarith
  have ⟨N,hAfterN⟩ := ha ε εPos
  have dist_aN := hAfterN N (by simp)
  rw [abs_sub_comm] at dist_aN
  have cbound_aN := hc N
  have aboveL : L < a N := by
    rw [abs_of_nonneg (by linarith)] at dist_aN
    linarith
  linarith


-- ============================================================================
-- Problem 3 (10 points): A sequence with no limit
-- ============================================================================

/-
Show that `(-1)^n` does not converge.
-/

#check Even.neg_one_pow
#check Odd.neg_one_pow

@[autogradedProof 10]
theorem problem3 : ¬ ∃ L : ℝ, ConvergesTo (fun n => (-1 : ℝ) ^ n) L := by
  rintro ⟨L,hConverge⟩
  by_cases hOne : L = 1
  . have ⟨N,hN⟩ := hConverge 1 (by simp)
    let n := N * 2 + 1
    have n.odd : Odd n := by simp [n]
    have an_close_neg1 := hN n (by dsimp [n]; linarith)
    simp_all
    rw [abs_of_neg (by linarith)] at an_close_neg1
    linarith
  . change L ≠ 1 at hOne
    let ε : ℝ := |L - 1| / 2
    have εPos : ε > 0 := by simp [ε,abs_sub_pos.mpr hOne]
    have ⟨N,hN⟩ := hConverge ε εPos
    let n := N * 2
    have n.odd : Even n := by simp [n]
    have Lclose1 := hN n (by dsimp [n]; linarith)
    simp_all [ε]
    by_cases Lgt1 : L > 1
    . simp_all
      rw [abs_sub_comm,abs_of_pos (by linarith)] at Lclose1
      linarith
    . have Llt1 : L < 1 := by
        rw [lt_iff_le_and_ne]
        simp_all
      rw [abs_sub_comm L 1] at Lclose1
      rw [abs_of_pos (by linarith)] at Lclose1
      linarith


-- ============================================================================
-- Limit algebra
-- ============================================================================

theorem add_const_converges (a : ℕ → ℝ) (L c : ℝ)
    (ha : ConvergesTo a L) :
    ConvergesTo (fun n => a n + c) (L + c) := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  simpa [show (a n + c) - (L + c) = a n - L by ring] using hN n hn

theorem mul_const_converges (a : ℕ → ℝ) (L c : ℝ)
    (ha : ConvergesTo a L) :
    ConvergesTo (fun n => c * a n) (c * L) := by
  by_cases hc : c = 0
  · intro ε hε
    use 0
    intro n hn
    simp [hc, hε]
  · intro ε hε
    have hcabs : 0 < |c| := abs_pos.mpr hc
    obtain ⟨N, hN⟩ := ha (ε / |c|) (div_pos hε hcabs)
    use N
    intro n hn
    have h := hN n hn
    have hEq : (c * a n) - c * L = c * (a n - L) := by ring
    rw [hEq, abs_mul]
    have hmul : |c| * |a n - L| < |c| * (ε / |c|) := by gcongr
    have hEq' : |c| * (ε / |c|) = ε := by field_simp [ne_of_gt hcabs]
    linarith


-- ============================================================================
-- Problem 4 (10 points): An algebraic limit
-- ============================================================================

/-- Prove that a ≤ b → a ≤ b² n for all naturals.

I could not find a theorem that handled the n = 0 case in mathlib.
In fact, I couldn't even find the statement `n ≤ n²` for all naturals.
The `le_mul_of_one_le_left` theorem is close but needlessly requires `n ≥ 1`.

I should ask on zulip about this. -/
lemma nat_le_squared {a b : ℕ} (h : a ≤ b) : a ≤ b^2  := by
  by_cases bzero : b = 0
  . nlinarith
  . change b ≠ 0 at bzero
    have npos : b > 0 := by positivity
    calc
      a ≤ b := h
      _ ≤ b * b := le_mul_of_one_le_left (by linarith) (by linarith)
      _ = b ^ 2 := by linarith

/-
Prove that `n² / (n² + 1) → 1`.
-/

@[autogradedProof 10]
theorem problem4 :
    ConvergesTo (fun n => ((n : ℝ) ^ 2) / (((n : ℝ) ^ 2) + 1)) 1 := by
  -- Observe that (n² / (n² + 1)) - 1 = -1/(n² + 1)
  -- This clearly converges to 0 = 1-1
  let a := fun n : ℕ => ((n : ℝ) ^ 2) / (((n : ℝ) ^ 2) + 1)
  let b := fun n : ℕ => (-1 : ℝ) / ((n : ℝ)^2 + 1)
  have b.negative : ∀ n : ℕ, b n < 0 := by
    intro n
    dsimp [b]
    exact div_neg_of_neg_of_pos (by simp) (by positivity)
  have haeq : a = b + 1 := by
    funext k
    dsimp [a,b]
    let k2 : ℝ := k ^2
    suffices k2 / (k2 + 1) - 1 = -1 / (k2 + 1) by linarith
    calc
          k2 / (k2 + 1) - 1
      _ = (k2 - (k2 + 1) * 1) / (k2 + 1) := by rw [div_sub']; positivity
      _ = (k2 - k2 - 1) / (k2 + 1) := by simp
      _ = -1 / (k2 + 1) := by simp
  have b.converges : ConvergesTo b 0 := by
    intro ε εPos
    have ⟨n,mBound⟩ := exists_nat_one_div_lt εPos
    use n
    intro m mGtN
    let m2 := m ^ 2
    have m2.aboveN : m2 ≥ n := by
      simp [m2,nat_le_squared mGtN]
    simp
    rw [abs_of_neg (b.negative m)]
    simp [b]
    let denom := (m : ℝ) ^ 2 + 1
    calc
          -(-1 / denom)
      _ = -(-(1 / denom)) := by rw [neg_div denom 1]
      _ = 1 / denom := by simp
      _ ≤ 1 / (↑n + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        dsimp [denom]
        suffices ↑n ≤ ↑m ^ 2 by norm_cast; simp_all
        exact m2.aboveN
      _ < ε := by linarith
  have add_converges := add_const_converges b 0 1 b.converges
  let a' := b + 1
  simp_all
  change ConvergesTo a' 1 at add_converges
  show ConvergesTo a 1
  simp_all [a',a,b]


-- ============================================================================
-- Monotone Convergence Theorem and limit identification
-- ============================================================================

theorem monotone_convergence (a : ℕ → ℝ)
    (hmon : Monotone a) (hbdd : BddAbove (Set.range a)) :
    ConvergesTo a (sSup (Set.range a)) := by
  intro ε hε
  have ⟨_, ⟨N, rfl⟩, hN⟩ : ∃ x ∈ Set.range a, sSup (Set.range a) - ε < x := by
    by_contra! h
    have hne : (Set.range a).Nonempty := ⟨a 0, ⟨0, rfl⟩⟩
    linarith [csSup_le hne h]
  use N
  intro n hn
  have hle : a n ≤ sSup (Set.range a) :=
    le_csSup hbdd (Set.mem_range.mpr ⟨n, rfl⟩)
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  linarith [hmon hn]

theorem tail_converges (a : ℕ → ℝ) (L : ℝ)
    (ha : ConvergesTo a L) :
    ConvergesTo (fun n => a (n + 1)) L := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  use N
  intro n hn
  exact hN (n + 1) (Nat.le_trans hn (Nat.le_succ n))

theorem limit_unique (a : ℕ → ℝ) (L M : ℝ)
    (hL : ConvergesTo a L) (hM : ConvergesTo a M) : L = M := by
  by_contra h
  have hε : 0 < |L - M| / 2 := by
    have : 0 < |L - M| := abs_pos.mpr (sub_ne_zero.mpr h)
    positivity
  obtain ⟨N₁, hN₁⟩ := hL _ hε
  obtain ⟨N₂, hN₂⟩ := hM _ hε
  have h1 := hN₁ (max N₁ N₂) (le_max_left N₁ N₂)
  have h2 := hN₂ (max N₁ N₂) (le_max_right N₁ N₂)
  have htri := abs_add_le (L - a (max N₁ N₂)) (a (max N₁ N₂) - M)
  rw [show (L - a (max N₁ N₂)) + (a (max N₁ N₂) - M) = L - M by ring,
      abs_sub_comm L (a (max N₁ N₂))] at htri
  linarith


-- ============================================================================
-- Problem 5 (16 points): Recursive-sequence capstone
-- ============================================================================

noncomputable def hw_seq : ℕ → ℝ
  | 0 => 0
  | n + 1 => (hw_seq n + 4) / 5

lemma hw_seq_le_one : ∀ n, hw_seq n ≤ 1 := by
  intro n
  induction' n with n ih
  · simp [hw_seq]
  · simp [hw_seq]; linarith

/-
The recursively defined sequence `a₀ = 0`, `aₙ₊₁ = (aₙ + 4) / 5` converges
to `1`.  The bound `hw_seq n ≤ 1` is provided above.
-/

#check monotone_nat_of_le_succ

@[autogradedProof 16]
theorem problem5 : ConvergesTo hw_seq 1 := by
  let S : Set ℝ := Set.range hw_seq
  have one_upper_bound : 1 ∈ upperBounds S := by
    intro x ⟨k, hk⟩
    rw [← hk]
    exact hw_seq_le_one k
  have hw_seq.bdd : BddAbove (Set.range hw_seq) := by use 1
  have hw_seq.nonempty : S.Nonempty := by
    simp [Set.Nonempty,S]
    use (hw_seq 0)
    use 0
  let sup : ℝ := sSup S
  have sup.pos : 0 < sup := by
    let y : ℝ := 4 / 5
    have y.memS : y ∈ S := by use 1; simp [y,hw_seq]
    calc
      0 < y := by simp [y]
      _ ≤ sup := le_csSup hw_seq.bdd y.memS
  have hw_seq.monotone : Monotone hw_seq := by
    apply monotone_nat_of_le_succ
    intro n
    dsimp [hw_seq]
    let x := hw_seq n
    show x ≤ (x + 4) / 5
    suffices (5 * x) ≤ (x + 4) by nlinarith
    have x.lt1 : x ≤ 1 := hw_seq_le_one n
    calc
      5 * x ≤ x + 4 * x := by linarith
          _ ≤ x + 4 := by linarith
  have hw_seq.conv : ConvergesTo hw_seq sup := by
    exact monotone_convergence hw_seq hw_seq.monotone hw_seq.bdd
  suffices 1 = sup by simp_all
  apply le_antisymm
  . by_contra! supBelow1
    let mid := (1 + sup) / 2
    have mid.lt1 : mid < 1 := by dsimp [mid]; linarith
    have mid.gtSup : mid > sup := by dsimp [mid]; linarith
    let ε := (min (1 - sup) sup) / 4
    have εPos : ε > 0 := by simp [ε]; constructor <;> linarith
    sorry
  . simp [sup]
    apply Real.sSup_le ?_ (by simp)
    rintro x ⟨k,hk⟩
    rw [← hk]
    exact hw_seq_le_one k
