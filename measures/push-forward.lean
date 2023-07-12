import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic

namespace MeasureTheory


structure homeomorphism (α : Type _) (β : Type _)
where
f : α -> β
inv_f : β -> α

/- def is_injective {α : Type _} {β : Type _} (hom : homeomorphism α β) := ∀ (sα : Set α), ∀ a₁ ∈ sα, ∀ a₂ ∈ sα, a₁ ≠ a₂ -> ∃ (sβ : Set β), ∃ b₁ ∈ sβ, ∃ b₂ ∈ sβ, b₁ ≠ b₂ ∧ hom.f a₁ = b₁ ∧ hom.f a₂ = b₂ -/

def is_injective {α : Type _} {β : Type _} (f : α -> β) := ∀ (sα : Set α), ∀ a₁ ∈ sα, ∀ a₂ ∈ sα, a₁ ≠ a₂ -> f a₁ ≠ f a₂

def is_surjective {α : Type _} {β : Type _} (f : α -> β) := ∀ (sβ : Set β), ∀ b ∈ sβ, ∃ (sα : Set α), ∃ a ∈ sα, f a = b

def is_bijective {α : Type _} {β : Type _} (f : α -> β) := ∀ (sβ : Set β), ∀ b ∈ sβ,
∃ (sα : Set α), ∃ a ∈ sα, (f a = b) ∧ (∀ (sα : Set α), ∀ a₂ ∈ sα, f a ≠ f a₂)

example {α : Type _} {β : Type _} (f : α -> β) (hinj : is_injective f) (hsurj : is_surjective f) : is_bijective f := by
intros sβ b hb
specialize hsurj sβ b hb
cases hsurj with | 
  intro sα hsurj => 
  cases hsurj with | 
    intro a hsurj => 
      cases hsurj with | 
        intro ha fab => 
          use sα
          use a
          use ha
          constructor
          {
            exact fab
          }
          {
            
          }
sorry

/- example {α : Type _} {β : Type _} (hom : homeomorphism α β) (hinj : is_injective hom) (hsur : is_surjective hom) : -/

def is_inversible {α : Type _} {β : Type _} (f : α -> β) := ∀ (sα : Set α), ∀ (sβ : Set β), ∀ a ∈ sα, ∃ b ∈ sβ, ∃ (f_inv : β -> α), f a = b <-> f_inv b = a

structure Pushforward_Measure (α : Type _) (β : Type _) [MeasurableSpace α] [MeasurableSpace β] where
μ : Measure α
f : Set α -> Set β
