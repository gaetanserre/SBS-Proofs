import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.Jacobian

import GOSVGDProofs.Bijection
import GOSVGDProofs.AbsoluteContinuity
open ENNReal

namespace MeasureTheory

def measure_set_of_pushforward_measure {α : Type _} {β : Type _} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (p_μ : Measure β) (f : β → α) := ∀ (B : Set β), p_μ B = μ (f '' B)

structure Pushforward_Measure (α : Type _) (β : Type _) [MeasurableSpace α] [MeasurableSpace β] extends Measure β where
p_μ : Measure β
μ : Measure α
T : α → β
T_inv : β → α
measure_app : measure_set_of_pushforward_measure μ p_μ T_inv
is_bij : is_bijective T
is_reci : is_reciprocal T T_inv

noncomputable def pushforward_average {α : Type _} {b : Type _} [MeasurableSpace α] [MeasurableSpace β] (μ : Pushforward_Measure α β) [IsProbabilityMeasure μ.p_μ] [IsProbabilityMeasure μ.μ] (f : β → ℝ≥0∞) := laverage μ.p_μ f = ∫⁻ x, f (μ.T x) ∂(μ.μ)

lemma measure_integral {α : Type _} [MeasurableSpace α] (μ : Measure α) (A : Set α) : μ A = ∫⁻ x in A, 1 ∂μ := 
by
sorry


lemma has_density {α : Type _} [MeasurableSpace α] {μ ν : Measure α} [IsProbabilityMeasure μ] (h : absolutely_continuous μ ν) : ∃ (d : α → ℝ≥0∞), ∀ (s : Set α), μ s = ∫⁻ x in s, d x ∂ν := by
-- Radon-Nikodym
sorry

def is_density {α : Type _} [MeasurableSpace α] (μ : Measure α) (ν : Measure α) (d : α → ℝ≥0∞) := ∀ (s : Set α), μ s = ∫⁻ x in s, d x ∂ν