import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace MeasureTheory

structure Pushforward_Measure (α : Type _) (β : Type _) [MeasurableSpace α] [MeasurableSpace β] where
μ : Measure α
f : Set α -> Set β
