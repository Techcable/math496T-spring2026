import AutograderLib
import Mathlib.Tactic

/-! # Homework 1
To begin with let prove the basic properties of ∧, ∨, and ¬.
-/

section

variable (P Q R T: Prop)

-- Commutativity
@[autogradedProof 5]
theorem problem1 : P ∧ Q ↔ Q ∧ P := by
  constructor
  . rintro ⟨hp, hq⟩
    constructor
    . exact hq
    . exact hp
  . rintro ⟨hq, hp⟩
    constructor
    . exact hp
    . exact hq

@[autogradedProof 5]
theorem problem2 : P ∨ Q ↔ Q ∨ P := by
  constructor
  . rintro (p | q)
    . right
      exact p
    . left
      exact q
  . rintro (q | p)
    . right
      exact q
    . left
      exact p


 -- Associativity
@[autogradedProof 5]
theorem problem3 : (P ∧ Q) ∧ R ↔ Q ∧ (P ∧ R) := by
  constructor
  . rintro ⟨⟨hp, hq⟩, hr⟩
    constructor
    . exact hq
    . constructor
      . exact hp
      . exact hr
  . rintro ⟨hq, ⟨hp, hr⟩⟩
    constructor
    . constructor
      . exact hp
      . exact hq
    . exact hr

@[autogradedProof 5]
theorem problem4 : (P ∨ Q) ∨ R ↔ Q ∨ (P ∨ R) := by
  constructor
  . rintro ((hp | hq) | hr)
    . right
      left
      exact hp
    . left
      exact hq
    . right
      right
      exact hr
  . rintro (hq | (hp | hr))
    . left
      right
      exact hq
    . left
      left
      exact hp
    . right
      exact hr
  done

-- Distributivity of ∧ over ∨
@[autogradedProof 5]
theorem problem5 : P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := by
  constructor
  . rintro ⟨hp, (hq | hr)⟩
    . left
      exact ⟨hp, hq⟩ -- made a guess and discovered that this works :)
    . right
      exact ⟨hp, hr⟩
  . rintro (⟨hp, hq⟩ | ⟨hp, hr⟩)
    . constructor
      . exact hp
      . left
        exact hq
    . constructor
      . exact hp
      . right
        exact hr
  done

-- Distributivity of ∨ over ∧
@[autogradedProof 5]
theorem problem6 : P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := by
  constructor
  . rintro (hp | ⟨hq, hr⟩)
    . constructor
      . left
        exact hp
      . left
        exact hp
    . constructor
      . right
        exact hq
      . right
        exact hr
  . rintro ⟨(hp | hq), (hp | hr)⟩
    . left
      exact hp
    . left
      exact hp
    . left
      exact hp
    . right
      exact ⟨hq, hr⟩
  done

@[autogradedProof 5]
theorem problem7 : (P ∧ ¬ Q) → ¬ (P → Q) := by
  rintro ⟨hp, notq⟩
  rintro p_to_q
  obtain hq := p_to_q hp
  contradiction

@[autogradedProof 5]
theorem problem8 : ∀ S : Prop, ¬ P → (P → S) := by
  intro hs
  intro notp
  intro hp
  contradiction
  done

-- This might require some logical thinking first
@[autogradedProof 5]
theorem problem9 : ∃ Q, ∀ P, P ∨ Q ↔ Q := by
  sorry
  done

@[autogradedProof 5]
theorem problem10 : ∃ Q, ∀ P, P ∨ Q ↔ P := by
  sorry
  done

end
