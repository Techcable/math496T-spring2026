import MIL.Common

-- # Lecture 9: Induction practice. Summation formulas.
-- New tactics: **congrArg, linarith, calc**

/- Some formulas:
∑_{k=1}^n k = n(n + 1)/2
∑_{k=1}^n k^2 = n(n + 1)(2n + 1)/6
∑_{k=1}^n k^3 = (n(n + 1)/2)^2 = (∑_{k=1}^n k)^2
∑_{k=1}^n (2k - 1) = n^2
∑_{k=1}^n (2k) = n(n + 1)
∑_{k=1}^n k(k + 1) = n(n + 1)(n + 2)/3
-/

open Nat

def SumTo :ℕ → ℕ
   | 0 => 0
   | succ n => (succ n) + SumTo n

-- Note: this corresponds to the conventional sum from 1 to n.
def SumToOfF (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | succ m => (f (succ m)) + SumToOfF m f


-- ∑_{k=1}^n k = n(n + 1)/2
theorem SumTo_formula (n : Nat) : 2 * (SumTo n) = n * (succ n) := by
  induction' n with n hn
  . rfl
  . dsimp [SumTo]
    linarith



-- ∑_{k=1}^n k^2 = n(n + 1)(2n + 1)/6
theorem SumOfSquaresTo (n : Nat) : 6 * (SumToOfF n (fun x => x^2)) = n * (succ n) * (2 * n + 1) := by
  induction' n with m ih
  . rfl
  . dsimp [SumToOfF]
    rw [mul_add] -- distributive property
    rw [ih] -- elimnates SumToOfF in hypothesis
    rw [mul_comm] -- swap 6(m+1)^2=(m+1)^26
    rw [pow_two] -- rewrite (m+1)^2=(m+1)(m+1)
    rw [mul_comm m] --- swap m * m.succ -> m.succ * m
    rw [succ_eq_add_one] -- m.succ -> m + 1
    rw [mul_assoc,mul_assoc]
    rw [← mul_add] -- dist. property in reverse, factoring out
    rw [mul_assoc]
    apply congrArg -- eliminates leading factor of (m+1)
    -- simplify LHS of equation
    let r := 2*m*m + 7*m + 6;
    have h1 : (m+1) * 6 + m * (2 * m + 1) = r := by
      dsimp [r]
      calc
        (m + 1) * 6 + m * (2 * m + 1) = 6 * m + 6 + 2 * m * m  + m := by
          rw [mul_comm,mul_add,mul_one,mul_add,mul_one,mul_comm m,← add_assoc]
        _ = 2 * m * m + 7 * m + 6 := by
          rw [add_assoc (6 *m) 6 (2 * m * m),add_comm]
          rw [← add_assoc,add_comm m]
          have hm7 : (6 * m) + m = 7 * m := by
            nth_rewrite 2 [← mul_one m]
            rw [mul_comm 6 m,← mul_add]
            rw [add_one]
            have succ6 : succ 6 = 7  := by rfl
            rw [succ6]
            rw [mul_comm]
          rw [hm7]
          omega -- this just rearranges for us
    have h2 : (m+1 + 1) * (2 * (m + 1) + 1) = r := by
      linarith
    rw [h1,h2]

-- ∑_{k=1}^n k^3 = (n(n + 1)/2)^2 = (∑_{k=1}^n k)^2
theorem SumOfCubesTo (n : Nat) : 4 * (SumToOfF n (fun x => x^3)) = n^2 * (succ n)^2 := by
  sorry

-- HARD: Involves subtraction
-- ∑_{k=1}^n (2k - 1) = n^2
theorem oddSum (n : ℕ) : SumToOfF n (fun m => 2*m - 1) = n*n := by
  sorry


lemma sum_linear (n p : ℕ) (f : ℕ → ℕ) : SumToOfF n (fun m => p * f m) = p * SumToOfF n f := by
  sorry

lemma sumToOfId_eq_SumTo : SumToOfF n (fun m => m) = SumTo n := by
  sorry

-- ∑_{k=1}^n (2k) = n(n + 1)
example (n:ℕ) : SumToOfF n (fun m => 2*m) = n * (n+1) := by
  sorry




-- ∑_{k=1}^n k(k + 1) = n(n + 1)(n + 2)/3
example : 3 * SumToOfF n (fun m => m*(m+1)) = n * (n + 1) * (n + 2) := by
  sorry
