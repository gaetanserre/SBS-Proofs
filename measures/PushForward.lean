import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Classical Topology BigOperators Filter ENNReal NNReal

namespace MeasureTheory

structure Pushforward_Measure (α : Type _) (β : Type _) [MeasurableSpace α] [MeasurableSpace β] extends Measure β where
μ : Measure α
f : Set α -> Set β
f_inv : Set β -> Set α

instance Pushforward_Measure.instCoeFun {α : Type _} {β : Type _} [MeasurableSpace α] [MeasurableSpace β] : CoeFun (Pushforward_Measure α β) fun _ => Set β → ℝ≥0∞ :=
  ⟨fun m => m.μ.toOuterMeasure ∘ m.f_inv⟩

variable (α : Type _) (β : Type _) (h1 : MeasurableSpace α) (h2 : MeasurableSpace β) (μ : Pushforward_Measure α β) (s : Set β)
#check μ s