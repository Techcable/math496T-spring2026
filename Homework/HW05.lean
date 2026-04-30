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
  ext x
  constructor
  . rintro ⟨fx_in_u, fx_in_v⟩
    exact ⟨fx_in_u, fx_in_v⟩
  . rintro ⟨f_in_inv_u, f_in_inv_v⟩
    rw [Set.mem_preimage] at *
    exact ⟨f_in_inv_u, f_in_inv_v⟩

-- (4) Preimage respects union.
@[autogradedProof 4]
theorem problem4 : f ⁻¹' (U ∪ V) = (f ⁻¹' U) ∪ (f ⁻¹' V) := by
  ext x
  constructor
  . -- turns out simp [Set.mem_preimage] is sufficient for both sides
    simp [Set.mem_preimage]
    /-
    rw [Set.mem_preimage]
    rintro (fx_in_u | fx_in_v)
    . left
      rw [Set.mem_preimage]
      exact fx_in_u
    . right
      rw [Set.mem_preimage]
      exact fx_in_v -/
  . simp [Set.mem_preimage]


-- (5) Preimage respects complement.
@[autogradedProof 4]
theorem problem5 : f ⁻¹' (Uᶜ) = (f ⁻¹' U)ᶜ := by
  ext x
  constructor
  . intro x_in_inv_comp
    rw [Set.mem_preimage] at x_in_inv_comp
    rw [Set.mem_compl_iff] at x_in_inv_comp ⊢
    rw [Set.mem_preimage] at ⊢
    intro xf_in_u
    contradiction
  . intro x_in_comp_inv_u
    rw [Set.mem_compl_iff] at x_in_comp_inv_u
    rw [Set.mem_preimage] at x_in_comp_inv_u ⊢
    rw [Set.mem_compl_iff] at ⊢
    exact x_in_comp_inv_u

-- (6) Image respects union.
@[autogradedProof 4]
theorem problem6 : f '' (S ∪ T) = (f '' S) ∪ (f '' T) := by
  ext x
  constructor
  . rintro ⟨a, ⟨(a_in_s | a_in_u), fa_eq_x⟩⟩
    . left
      use a
    . right
      use a
  . rintro (⟨a, ⟨a_in_s, fa_eq_x⟩⟩ | ⟨a, ⟨a_in_t, fa_eq_x⟩⟩)
    rw [Set.mem_image] at ⊢
    . use a
      exact ⟨(by left; exact a_in_s), fa_eq_x⟩
    . use a
      exact ⟨(by right; exact a_in_t), fa_eq_x⟩


-- (7) Image/preimage Galois connection.
@[autogradedProof 6]
theorem problem7 : f '' S ⊆ U ↔ S ⊆ f ⁻¹' U := by
  constructor
  . intro fimage_sub_u x x_in_s
    rw [Set.mem_preimage]
    apply fimage_sub_u
    rw [Set.mem_image]
    use x
  . intro s_sub_inv_u
    intro x x_in_image_s
    rw [Set.mem_image] at x_in_image_s
    obtain ⟨a, ⟨a_in_s, fa_eq_x⟩⟩ := x_in_image_s
    have a_in_inv_u : a ∈ f⁻¹' U := by
      apply s_sub_inv_u
      exact a_in_s
    dsimp [Set.preimage] at a_in_inv_u
    rw [fa_eq_x] at a_in_inv_u
    exact a_in_inv_u

-- (8) Image does not generally respect intersection.
-- Provide an explicit counterexample where equality fails.
@[autogradedProof 5]
theorem problem8 :
    ∃ (A B : Set ℕ) (g : ℕ → ℕ),
      (g '' (A ∩ B)) ≠ (g '' A ∩ g '' B) := by
    -- the key is the fact the function is noninjective
    -- Observe that in the integers, f(x)=x^2 fails for A={1}, B={-1}
    -- For ℕ we achieve the same effect with truncating division
    let g : ℕ → ℕ := fun x =>  x / 2
    let A : Set ℕ := {0}
    let B : Set ℕ := {1}
    use A
    use B
    use g
    have : g '' (A ∩ B) = ∅ := by
      ext x
      constructor
      . rw [Set.mem_image]
        rintro ⟨a, ⟨⟨a_in_a,a_in_b⟩,ga_eq_x⟩⟩
        exfalso
        dsimp [A,B] at a_in_a a_in_b
        simp at *
        linarith
      . simp
    rw [this]
    dsimp only [A,B]
    simp only [Set.image_singleton]
    simp [g]
    intro emptyset_eq_zero
    let S : Set ℕ := {0}
    have s_eq_empty : S = ∅ := (by rw [emptyset_eq_zero])
    have nothing_in_s : ∀ (x : ℕ), ¬(x ∈ S) := by
      rw [Set.eq_empty_iff_forall_notMem] at s_eq_empty
      exact s_eq_empty
    apply nothing_in_s 0
    rfl



-- (9) Cancellation application.
-- Show that if g ∘ f is bijective, then f is injective and g is surjective.
@[autogradedProof 5]
theorem problem9 {f₁ : α → β} {g : β → γ}
    (h : Function.Bijective (g ∘ f₁)) :
    Function.Injective f₁ ∧ Function.Surjective g := by
  let f := f₁ -- shorthand
  constructor
  . dsimp [Function.Injective]
    intro x y fx_eq_fy
    apply h.left
    dsimp [Function.comp]
    rw [fx_eq_fy]
  . dsimp [Function.Surjective]
    intro z
    obtain ⟨x, gfx_eq_z⟩ := h.right z
    use f x
    rw [Function.comp] at gfx_eq_z
    exact gfx_eq_z
end
