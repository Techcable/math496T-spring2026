import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

/-! # Homework 5: Functions, Cancellation, and Images/Preimages
-/

section

variable {α β γ δ : Type*}

/- In category theory **injective** and **surjective** maps are called **monic** and **epic**. They are defined by
**Monic** : `f ∘ g = f ∘ h ⇒ g = h`
and
**Epic** : `g ∘ f = h ∘ f ⇒ g = h`
-/

-- (1) Injective iff left-cancellable.
@[autogradedProof 11]
theorem problem1 (c : γ) (f : α → β) :
    Function.Injective f ↔
    ∀ (g₁ g₂ : γ → α), f ∘ g₁ = f ∘ g₂ → g₁ = g₂ := by
  constructor
  . intro finj g1 g2 fg1_eq_fg2
    funext x
    have fg1x_eq_fg2x : (f ∘ g1) x = (f ∘ g2) x := by
      rw [fg1_eq_fg2]
    dsimp at fg1x_eq_fg2x
    exact finj fg1x_eq_fg2x
  . intro left_cancellable
    dsimp [Function.Injective]
    intro x y fx_eq_fy
    let g1 : γ → α := fun n => x
    let g2 : γ → α := fun n => y
    have fg1_eq_fg2 : f ∘ g1 = f ∘ g2 := by
      funext z
      dsimp [g1,g2]
      exact fx_eq_fy
    have g1_eq_g2 := left_cancellable g1 g2 fg1_eq_fg2
    have g1c_eq_g2c : g1 c = g2 c := by
      rw [g1_eq_g2]
    dsimp [g1,g2] at g1c_eq_g2c
    exact g1c_eq_g2c

-- (2) Injective idempotent is identity.
@[autogradedProof 7]
theorem problem2 {f : α → α}
    (hff : f ∘ f = f) (hinj : Function.Injective f) : f = id := by
  have ff_eq_fid : f ∘ f = f ∘ id := by
    rw [Function.comp_id]
    exact hff
  -- The only reason we need `funext` here is so we can produce a `c : α`
  -- to pass as the first parameter to problem1.
  -- It would be sufficient to use `a: NonEmpty` and `Classical.choice`,
  -- but `funext x` also produces an instance of α and is simpler.
  funext x
  have left_cancelled : f = id := (problem1 x f).mp hinj f id ff_eq_fid
  rw [left_cancelled]

-- Set-theoretic part
variable (f : α → β)
variable (S T : Set α)
variable (U V : Set β)

-- (3) Preimage respects intersection.
@[autogradedProof 4]
theorem problem3 : f ⁻¹' (U ∩ V) = (f ⁻¹' U) ∩ (f ⁻¹' V) := by
  sorry
  done

-- (4) Preimage respects union.
@[autogradedProof 4]
theorem problem4 : f ⁻¹' (U ∪ V) = (f ⁻¹' U) ∪ (f ⁻¹' V) := by
  sorry
  done

-- (5) Preimage respects complement.
@[autogradedProof 4]
theorem problem5 : f ⁻¹' (Uᶜ) = (f ⁻¹' U)ᶜ := by
  sorry
  done

-- (6) Image respects union.
@[autogradedProof 4]
theorem problem6 : f '' (S ∪ T) = (f '' S) ∪ (f '' T) := by
  sorry
  done

-- (7) Image/preimage Galois connection.
@[autogradedProof 6]
theorem problem7 : f '' S ⊆ U ↔ S ⊆ f ⁻¹' U := by
  sorry
  done

-- (8) Image does not generally respect intersection.
-- Provide an explicit counterexample where equality fails.
@[autogradedProof 5]
theorem problem8 :
    ∃ (A B : Set ℕ) (g : ℕ → ℕ),
      (g '' (A ∩ B)) ≠ (g '' A ∩ g '' B) := by
  sorry
  done

-- (9) Cancellation application.
-- Show that if g ∘ f is bijective, then f is injective and g is surjective.
@[autogradedProof 5]
theorem problem9 {f₁ : α → β} {g : β → γ}
    (h : Function.Bijective (g ∘ f₁)) :
    Function.Injective f₁ ∧ Function.Surjective g := by
  sorry
  done

end
