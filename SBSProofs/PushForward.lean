/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.Jacobian

import SBSProofs.Bijection
import SBSProofs.AbsoluteContinuity
open ENNReal

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

def measure_set_of_pushforward_measure (μ : Measure α) (p_μ : Measure β) (f : β → α) := ∀ (B : Set β), p_μ B = μ (f '' B)

def push_forward_integration (μ : Measure α) (p_μ : Measure β) (T : α → β) (T_inv : β → α) := ∀ (φ : β → ℝ), ∀ (B : Set β), ∫ x in B, φ x ∂p_μ = ∫ x in T_inv '' B, (φ ∘ T) x ∂μ

structure Pushforward_Measure (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] extends Measure β where
p_μ : Measure β
μ : Measure α
T : α → β
T_inv : β → α
measure_app : measure_set_of_pushforward_measure μ p_μ T_inv
is_bij : is_bijective T
is_reci : is_reciprocal T T_inv
integration : push_forward_integration μ p_μ T T_inv

noncomputable def pushforward_average (μ : Pushforward_Measure α β) [IsProbabilityMeasure μ.p_μ] [IsProbabilityMeasure μ.μ] (f : β → ℝ≥0∞) := laverage μ.p_μ f = ∫⁻ x, f (μ.T x) ∂(μ.μ)

lemma has_density {μ ν : Measure α} [IsProbabilityMeasure μ] (h : absolutely_continuous μ ν) : ∃ (d : α → ℝ≥0∞), ∀ (s : Set α), μ s = ∫⁻ x in s, d x ∂ν :=
by
-- Radon-Nikodym
sorry

def is_density (μ : Measure α) (ν : Measure α) (d : α → ℝ≥0∞) := ∀ (s : Set α), μ s = ∫⁻ x in s, d x ∂ν

lemma density_lintegration (μ : Measure α) (ν : Measure α) (d : α → ℝ≥0∞) (h : is_density μ ν d) : ∀ (f : α → ℝ≥0∞), ∀ (s : Set α), ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, d x * f x ∂ν :=
by
-- Radon-Nikodym
sorry

lemma density_integration (μ : Measure α) (ν : Measure α) (d : α → ℝ≥0∞) (h : is_density μ ν d) : ∀ (f : α → ℝ), ∀ (s : Set α), ∫ x in s, f x ∂μ = ∫ x in s, ENNReal.toReal (d x) * f x ∂ν :=
by
-- Radon-Nikodym
sorry
