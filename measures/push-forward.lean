import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.Contrapose

namespace MeasureTheory

/- TODO : bijectif : inj ∧ surj -/

/- def is_injective {α : Type _} {β : Type _} (hom : homeomorphism α β) := ∀ (sα : Set α), ∀ a₁ ∈ sα, ∀ a₂ ∈ sα, a₁ ≠ a₂ -> ∃ (sβ : Set β), ∃ b₁ ∈ sβ, ∃ b₂ ∈ sβ, b₁ ≠ b₂ ∧ hom.f a₁ = b₁ ∧ hom.f a₂ = b₂ -/

def is_injective {α : Type _} {β : Type _} (f : α -> β) :=  ∀ (a₁ a₂ : α), a₁ ≠ a₂ -> f a₁ ≠ f a₂

def is_surjective {α : Type _} {β : Type _} (f : α -> β) := ∀ (b : β), ∃ (a : α), f a = b

def is_bijective {α : Type _} {β : Type _} (f : α -> β) := ∀ (b : β),
∃ (a : α), (f a = b) ∧ (∀ (a₂ : α), a ≠ a₂ -> f a ≠ f a₂)

lemma deterministic_function {α : Type _} {β : Type _} (f : α -> β) : ∀ (a₁ a₂ : α), f a₁ ≠ f a₂ -> a₁ ≠ a₂ := by
intros a₁ a₂ h
contrapose h
push_neg at h 
push_neg
rw [h] 

theorem bijective_is_inj_and_surj {α : Type _} {β : Type _} (f : α -> β) (hinj : is_injective f) (hsurj : is_surjective f) : is_bijective f := by
intro b
specialize hsurj b
cases hsurj with
  | intro a fab =>
      use a
      constructor
      {exact fab}
      {
        intros a2 neqa
        exact hinj a a2 neqa
      }

def is_inversible {α : Type _} {β : Type _} (f : α -> β) (f_inv : β -> α) := ∀ (a : α), f_inv (f a) = a

/- example {α : Type _} {β : Type _} (hom : homeomorphism α β) (hinj : is_injective hom) (hsur : is_surjective hom) : -/

structure homeomorphism (α : Type _) (β : Type _)
where
f : α -> β
inv_f : β -> α
is_inj : is_injective f
is_surj : is_surjective f
is_inv : is_inversible f inv_f

example {α : Type _} {β : Type _} (hom : homeomorphism α β) : is_surjective hom.inv_f := by
intro a
use (hom.f a)
exact hom.is_inv a

example {α : Type _} {β : Type _} (hom : homeomorphism α β) : is_injective hom.inv_f := by
intros b₁ b₂ hdif
have h1 : ∃ (a : α), hom.f a = b₁ := hom.is_surj b₁
have h2 : ∃ (a : α), hom.f a = b₂ := hom.is_surj b₂
cases h1 with 
  | intro a₁ h1 =>
    cases h2 with 
      | intro a₂ h2 =>
        rw [← h1, ← h2]
        rw [hom.is_inv a₁, hom.is_inv a₂]
        rw [← h1, ← h2 ] at hdif
        exact deterministic_function hom.f a₁ a₂ hdif

def hom_is_bijective {α : Type _} {β : Type _} (hom : homeomorphism α β) := is_bijective hom.f
def inv_hom_is_bijective {α : Type _} {β : Type _} := ∀ (hom : homeomorphism α β), is_bijective hom.inv_f
def inv_hom {α : Type _} {β : Type _} (hom : homeomorphism α β) := ∀ (a : α), hom.inv_f (hom.f a) = a

example {α : Type _} {β : Type _} (hom : homeomorphism α β) : ∀ (a : α), hom.inv_f (hom.f a) = a := by
intro a
exact hom.is_inv a

structure Pushforward_Measure (α : Type _) (β : Type _) [MeasurableSpace α] [MeasurableSpace β] where
μ : Measure α
f : Set α -> Set β
