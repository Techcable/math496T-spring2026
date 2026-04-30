import MIL.Common

/- # Lecture 7: Induction -/

/- ## Natural Numbers
  __Peano Axioms:__
1. 0 is a natural number.
2. Every natural number n has a successor, denoted by S(n).
3. 0 is not the successor of any natural number.
4. If S(n) = S(m), then n = m, (the successor function is injective).
5. If a property holds for 0 and holds for S(n) whenever it holds for n, then it holds for all natural numbers.
-/


inductive myNat where
  | zero : myNat
  | succ : myNat → myNat

open myNat

-- 1. 0 is a natural number.
#check zero
-- 2. Every natural number n has a successor, denoted by S(n).
#check succ zero

-- 3. 0 is not the successor of any natural number.
theorem myNat.zero_ne_succ (n : myNat) : zero ≠ succ n := by
  intro h
  cases h -- this is the __case analysis__ tactic, it tries to create subgoals, and encounters two DIFFERENT constructors of myNat, discharging the goal


-- 4. If S(n) = S(m), then n = m, (the successor function is injective).
theorem myNat.succ_inj (n m : myNat) (h : succ n = succ m) : n = m := by
  cases h
  rfl

-- 5. If a property holds for 0 and holds for S(n) whenever it holds for n, then it holds for all natural numbers.
theorem myNat.induction {P : myNat → Prop} (h0 : P zero) (hS : ∀ n, P n → P (succ n)) : ∀ n, P n := by
  intro n
  induction' n with n ih -- this is the __induction__ tactic, it creates two subgoals, one for the base case and one for the inductive step
  · exact h0
  . exact hS n ih

theorem myNat.succ_ne_zero (n : myNat) : myNat.zero ≠ (myNat.succ n) := by
  apply myNat.zero_ne_succ

theorem myNat.zero_ne_one : myNat.zero ≠ myNat.succ myNat.zero := by
  apply myNat.zero_ne_succ


def myAdd : myNat → myNat → myNat
  | zero, m => m
  | succ n, m => succ (myAdd n m)

theorem myAdd_zero (n : myNat) : myAdd zero n = n := by
  cases n
  . rfl
  . dsimp [myAdd]

theorem zero_myAdd (n : myNat) : myAdd n zero = n := by
  induction' n with n ih
  · rfl
  . rw [myAdd]
    rw [ih]

theorem succ_myAdd (n m : myNat) : myAdd (succ n) m = succ (myAdd n m) := by
  dsimp [myAdd]


-- needed for myAdd_comm
theorem myAdd_succ (n m : myNat) : myAdd n (succ m) = succ (myAdd n m) := by
  induction' n with n ih
  . rw [myAdd_zero,myAdd_zero]
  . rw [succ_myAdd,ih,succ_myAdd]


theorem myAdd_comm (n m : myNat) : myAdd n m = myAdd m n := by
  induction' n with n ih
  . rw [myAdd_zero,zero_myAdd]
  . rw [succ_myAdd,myAdd_succ,ih]


theorem myAdd_assoc (n m k : myNat) : myAdd n (myAdd m k) = myAdd (myAdd n m) k := by
  induction' n with p ih
  · rfl
  . rw [succ_myAdd,succ_myAdd,succ_myAdd]
    rw [ih]

-- ## Multiplication

def myMul : myNat → myNat → myNat
  | zero, _m => zero
  | succ n, m => myAdd m (myMul n m)

theorem myMul_zero (n : myNat) : myMul zero n = zero := by
  rfl

theorem zero_myMul (n : myNat) : myMul n zero = zero := by
  induction' n with n ih
  . rfl
  . dsimp [myMul]
    rw [ih]
    rfl

theorem succ_myMul (n m : myNat) : myMul (succ n) m = myAdd m (myMul n m) := by
  rfl

-- needed for mMul_comm
theorem myMul_succ (n m : myNat) : myMul n (succ m) = myAdd n (myMul n m) := by
  induction' n with n ih
  . rfl
  . rw [succ_myMul n m.succ]
    rw [ih]
    rw [succ_myMul]
    dsimp [myAdd]
    rw [myAdd_assoc,myAdd_assoc,myAdd_comm n m]


theorem myMul_comm (n m : myNat) : myMul n m = myMul m n := by
  induction' n with n ih
  . rw [zero_myMul,myMul_zero]
  . rw [myMul_succ,succ_myMul,ih]


-- distributive property
theorem myNat.mul_add (n m k : myNat) : myMul n (myAdd m k) = myAdd (myMul n m) (myMul n k) := by
  induction' k with k ih
  . rw [zero_myAdd,zero_myMul,zero_myAdd]
  . rw [myMul_succ]
    -- now we WTS n(m+(k+1))=(nm+n+nk),
    -- need to rewrite LHS into ((nm+nk)+n) to invoke the IH
    rw [myAdd_comm n,myAdd_assoc]
    rw [← ih]
    -- now we WTS that n(m+(k+1))=(n(m+k))+n
    -- This can be done by rewriting the LHS as n((m+k)) + 1),
    -- reducing to the already proved myMull_succ
    rw [myAdd_succ]
    rw [myMul_succ,myAdd_comm]

theorem myNat.add_mul (n m k : myNat) : myMul (myAdd n m) k = myAdd (myMul n k) (myMul m k) := by
  -- follows from mul_add and commutativity
  rw [myMul_comm,myNat.mul_add,myMul_comm k n,myMul_comm k m]

theorem myMul_assoc (n m k : myNat) : myMul n (myMul m k) = myMul (myMul n m) k := by
  induction' n with n ih
  . rfl
  . rw [succ_myMul,succ_myMul,ih,add_mul]
