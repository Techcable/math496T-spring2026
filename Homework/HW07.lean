import AutograderLib
import Mathlib.Tactic
import Mathlib.Data.Set.Function

--! # Homework 7: Completing the Schröder–Bernstein Theorem

-- noncomputable section
open Classical

section SchroederBernstein

variable {α β : Type*}

/-!
**The Schröder–Bernstein Theorem**:
Given injections f : α → β and g : β → α,
we construct a bijection h : α ↔ β.

**The construction**:
  A₀ = α \ range(g)    (elements of α not in the image of g)
  Aₙ₊₁ = (g ∘ f) '' Aₙ  (apply g ∘ f to the previous layer)
  A = ⋃ₙ Aₙ             (the union of all layers)

Then define:
  h(x) = f(x)        if x ∈ A
  h(x) = g⁻¹(x)     if x ∉ A

In Homework 6 you proved that h is well-defined (g⁻¹(x) exists when x ∉ A).
Now, you will prove that h is *bijective*.
-/

variable (f : α → β) (g : β → α)
variable (hf : Function.Injective f)
variable (hg : Function.Injective g)

-- Define the layers:
def A₀ (g : β → α) : Set α := (Set.range g)ᶜ

-- Then apply g ∘ f repeatedly to get the layers
def layer (f : α → β) (g : β → α) : ℕ → Set α
  | 0     => A₀ g
  | n + 1 => (g ∘ f) '' layer f g n

def A_all (f : α → β) (g : β → α) : Set α :=
  ⋃ n, layer f g n

-- Local shorthands used throughout this section.

local notation "A" => A_all f g

/-- (6.3) Key lemma: if x ∉ A_all, then g⁻¹(x) is well-defined.

Since x ∈ range(g) (by problem 1), there exists b with g(b) = x.
Moreover, b is unique (since g is injective).
This is problem 3 from Homework 6.
You can use this lemma in the problems below, but you don't need to reprove it. --/
@[legalAxiom]
axiom wellDefined {x : α} (xA : x ∉ A) : ∃! b : β, g b = x


/-- (6.4) Key lemma: if x ∉ A_all, and g(b) = x, then b ≠ f(y) for any y ∈ A_all.

This is problem 4 from Homework 6 (just slightly rephrased).
You can use this lemma in the problems below, but you don't need to reprove it.

Oirginal Proof idea: if b = f(y) for some y ∈ A_all, then x = g(b) = g(f(y)).
Since y ∈ sbLayer f g n for some n, g(f(y)) ∈ sbLayer f g (n+1) ⊆ A_all.
use problem2
But x ∉ A_all — contradiction.-/
@[legalAxiom]
axiom distinct
  {x  y : α} (xA : x ∉ A) (yA : y ∈ A) (b : β) : ¬ (g b = x ∧ b = f y)

-- Let us define the function h : α → β by cases on whether x ∈ A or not.
noncomputable def h_def (f : α → β) (g : β → α) (_hg : Function.Injective g) (x : α) : β :=
  if xA : x ∈ A_all f g
    then f x
    else Classical.choose (wellDefined (f := f) (g := g) xA)

local notation "h" => h_def f g hg

@[autogradedProof 5]
-- Prove that h equals f on A_all:
theorem problem1 : ∀ x ∈ A, h x = f x := by
  intro x xA
  simp [h_def,xA]

@[autogradedProof 5]
-- Prove that g is left inverse of h on the complement of A_all:
theorem problem2 : ∀ x, x ∉ A → g (h x) = x := by
  intro x x_notin_a
  simp [h_def,x_notin_a]
  let ⟨y, _⟩ := Classical.choose_spec (wellDefined (f := f) (g := g) x_notin_a)
  simp [y]

#check problem2 -- (f : α → β) (g : β → α) (hg : Function.Injective g) (x : α) : x ∉ A → g (h x) = x

/- Injectivity splits into (essentially) three cases:
Suppose h(a) = h(a').

Case 1: a,a' ∈ A, then (since on A h = f) we have
   f(a) = h(a) = h(a') = f(a'), so a = a' by injectivity of f.
Case 2: a,a' ∉ A, then (since on Aᶜ h=g⁻¹) we have
   a = g(h(a)) = g(h(a')) = a'.
Case 3: a ∈ A, a' ∉ A (or vice versa)
  Let b = h(a) = h(a').
  Then b = h(a) = f(a), and g(b) = g(h(a')) = a', so b = f(a) and g(b) = a',
    contradicting `lemma distinct`.
-/

-- Injectivity on A:
@[autogradedProof 6]
-- Case 1: a,a' ∈ A, then (since on A h = f) we have
--   f(a) = h(a) = h(a') = f(a'), so a = a' by injectivity of f.
theorem problem3 {a a' : α} (aA : a ∈ A)
(a'A : a' ∈ A) (hf : Function.Injective f) : h a = h a' → a = a' := by
  rw [problem1 f g hg a aA]
  rw [problem1 f g hg a' a'A]
  apply hf

-- Injectivity on Aᶜ:
@[autogradedProof 6]
-- Case 2: a,a' ∉ A, then (since on Aᶜ h=g⁻¹) we have
--   a = g(h(a)) = g(h(a')) = a'.
theorem problem4 {a a' : α} (aA : a ∉ A)
(a'A : a' ∉ A) : h a = h a' → a = a' := by
  intro heq
  calc
   a = g (h a) := by simp [problem2 (f := f) (g := g) (hg := hg) (x := a) aA]
   _ = g (h a') := by rw [heq]
   _ = a' := by simp [problem2 (f := f) (g := g) (hg := hg) (x := a') a'A]

-- h(A) is disjoint from h(Aᶜ):
@[autogradedProof 8]
-- Case 3: a ∈ A, a' ∉ A (or vice versa)
--    Let b = h(a) = h(a').
--    Then b = h(a) = f(a), and g(b) = g(h(a')) = a',
--    contradicting lemma `distinct`.
theorem problem5 (a a' : α) (aA : a ∈ A)
(a'A : a' ∉ A) : h a ≠ h a' := by
  intro ha_eq_ha'
  let b := h a
  have b_eq_fa : b = f a := by
    simp [b,h_def,aA]
  have gb_eq_a' : g b = a' := by
    calc
      g b = g (h a) := rfl
      _ = g (h a') := by rw [ha_eq_ha']
      _ = a' := by rw [problem2 f g hg a' a'A]
  -- distinct tells us g(b) = x => b ≠ f(y) for y ∈ A_all, x ∉ A_all
  -- In our case, g b = a' => b ≠ f (y) regardless of y ∈ a_all
  -- This conclusion then contradicts `b_eq_fa`
  have b_nevereq_fy : ∀ y, y ∈ A → b ≠ f y  := by
    intro y y_in_a b_eq_fy
    apply (distinct f g a'A y_in_a b) ⟨gb_eq_a',b_eq_fy⟩
  have b_neq_fa : b ≠ f a := b_nevereq_fy a aA
  contradiction

@[autogradedProof 14]
theorem problem7 (hf : Function.Injective f) (hg : Function.Injective g) :
  Function.Injective h
    := by
    sorry
     -- case 1: x,y ∈ A_all
    --  exact problem3 (f := f) (g := g) (hg := hg) (a := a) (a' := a') aA a'A hf heq
    -- pick_goal 3 -- allows us to jump to the last goal, leaving the hardest two case for desert
     -- case 2: x,y ∉ A_all
    -- .  sorry
     -- case 3: x ∈ A_all, y ∉ A_all
    -- .  sorry
     -- case 4: x ∉ A_all, y ∈ A_all (interchanging roles of a and a')
    -- .  sorry
    done

@[autogradedProof 6]
theorem problem8 (hing : Function.Injective g) :
  Function.Surjective h := by
  intro b
  by_cases bA : (g b) ∈ A
  -- if g(b) ∈ A, then we can find a ∈ A such that h a = f a = b
  . let hn := Set.mem_iUnion.mp bA
    obtain ⟨n,An⟩ := hn
    rcases n with hzero | n
    -- g(b) ∉ A₀, since it is in range(g)
    . sorry
      -- HINTS:
      -- exfalso
      -- exact Set.mem_range_self b
    -- g(b) ∈ Aₙ₊₁, so we can find a ∈ Aₙ such that g(f(a)) = g(b),
    -- and hence f(a) = b by injectivity of g and problem1.
    . dsimp [layer] at An
      rw [Set.mem_image] at An
      obtain ⟨a,an,eq⟩ := An
      have aA : a ∈ A := Set.mem_iUnion.mpr ⟨n, an⟩
      use a
      simp [problem1 (f := f) (g := g) (hg := hing) (x := a) aA]
      apply hing
      rw [← eq]
      simp
  -- if g(b) ∉ A, then we can use h=g⁻¹ to find a ∈ Aᶜ such that g(h(a)) = b
  -- using problem2 and injectivity of g.
  . use (g b)
    have hhh : g (h (g b)) = g b := by simp [problem2 (f := f) (g := g) (hg := hing) (x := g b) bA]
    sorry



theorem SchroederBernstein (hf : Function.Injective f) (hg : Function.Injective g) :
  Function.Bijective h := by
  constructor
  . -- injectivity is problem 7
    exact problem7 (f := f) (g := g) hg hf hg
  . -- surjectivity is problem 8
    exact problem8 (f := f) (g := g) hg hg

end SchroederBernstein
