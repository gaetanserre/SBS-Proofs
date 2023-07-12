import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace MeasureTheory

def absolutely_continuous {α : Type _} {_m : MeasurableSpace α} (μ ν : Measure α) : Prop := ∀ (s : Set α), ν s = 0 → μ s = 0

lemma absolutely_continuous_trans {α : Type _} {_m : MeasurableSpace α} (μ₁ μ₂ μ₃ : Measure α) (h1: absolutely_continuous μ₁ μ₂) (h2: absolutely_continuous μ₂ μ₃) : absolutely_continuous μ₁ μ₃ := by
  intros s hsigma
  specialize h1 s
  specialize h2 s
  exact h1 (h2 hsigma)

lemma absolutely_continuous_refl {α : Type _} {_m : MeasurableSpace α} (μ : Measure α) : absolutely_continuous μ μ := by
  intros _s h
  exact h
