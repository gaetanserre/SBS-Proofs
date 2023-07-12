import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic

namespace MeasureTheory


structure homeomorphism (α : Type _) (β : Type _)
where
f : α -> β
inv_f : β -> α

def is_injective {α : Type _} {β : Type _} (hom : homeomorphism α β) := ∀ (sα : Set α), ∀ (sβ : Set β), ∀ a₁ ∈ sα, ∀ a₂ ∈ sα, a₁ ≠ a₂ -> ∃ b₁ ∈ sβ, ∃ b₂ ∈ sβ, b₁ ≠ b₂ ∧ hom.f a₁ = b₁ ∧ hom.f a₂ = b₂

def is_inversible {α : Type _} {β : Type _} (hom : homeomorphism α β) := ∀ (sα : Set α), ∀ (sβ : Set β), ∀ a ∈ sα, ∃ b ∈ sβ, hom.f a = b <-> hom.inv_f b = a

structure Pushforward_Measure (α : Type _) (β : Type _) [MeasurableSpace α] [MeasurableSpace β] where
μ : Measure α
f : Set α -> Set β
