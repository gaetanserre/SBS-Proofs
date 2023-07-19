import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Init.Set
import GOSVGDProofs.Bijection
import GOSVGDProofs.AbsoluteContinuity
open ENNReal

namespace MeasureTheory

def measure_set_of_pushforward_measure {α : Type _} {β : Type _} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (p_μ : Measure β) (f : Set β -> Set α) := ∀ (B : Set β), p_μ B = μ (f B)

structure Pushforward_Measure (α : Type _) (β : Type _) [MeasurableSpace α] [MeasurableSpace β] extends Measure β where
p_μ : Measure β
μ : Measure α
f : α -> β
f_set : Set α -> Set β
is_set_ext : is_set_extension f f_set
f_inv : β -> α
f_set_inv : Set β -> Set α
measure_app : measure_set_of_pushforward_measure μ p_μ f_set_inv
is_set_inv_ext : is_set_extension f_inv f_set_inv
is_bij : is_bijective f
is_reci : is_reciprocal f f_inv


variable (α : Type _) (β : Type _) (hα : MeasurableSpace α) (hβ : MeasurableSpace β)
variable (ν : Measure α) -- Lebesgue
variable (μ_t : Pushforward_Measure α α) (h1 : IsProbabilityMeasure μ_t.p_μ) (h2 : IsProbabilityMeasure μ_t.μ)
variable (habs1 : absolutely_continuous μ_t.μ ν) (habs2 : absolutely_continuous μ_t.p_μ ν)


noncomputable def pushforward_average (μ : Pushforward_Measure α β) [IsProbabilityMeasure μ.p_μ] [IsProbabilityMeasure μ.μ] (f : β -> ℝ≥0∞) := laverage μ.p_μ f = ∫⁻ x, f (μ.f x) ∂(μ.μ)

def measure_integral (μ : Measure α) (A : Set α) := μ A = ∫⁻ x in A, 1 ∂μ


def is_density {α : Type _} [MeasurableSpace α] (μ : Measure α) (ν : Measure α) (d : α -> ℝ≥0∞) := ∀ (s : Set α), μ s = ∫⁻ x in s, d x ∂ν

lemma has_density {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : absolutely_continuous μ ν) : ∃ (d : α -> ℝ≥0∞), ∀ (s : Set α), μ s = ∫⁻ x in s, d x ∂ν := by
-- Radon-Nikodym
sorry

lemma push_forward_density_equality (d_mu : α -> ℝ≥0∞) (d_p_mu : α -> ℝ≥0∞) (hf1 : is_density μ_t.μ ν d_mu) (hf2 : is_density μ_t.p_μ ν d_p_mu) : ∀ (A : Set α), ∫⁻ x in A, d_mu x ∂ν = ∫⁻ x in (μ_t.f_set A), d_p_mu x ∂ν := by
intro A
rw [← hf1 A, ← hf2 (μ_t.f_set A)]
rw [μ_t.measure_app]
rw [←identity_reciprocal_set_extension μ_t.f μ_t.f_inv μ_t.f_set μ_t.f_set_inv μ_t.is_reci μ_t.is_set_ext μ_t.is_set_inv_ext A]

/- instance Pushforward_Measure.instCoeFun {α : Type _} {β : Type _} [MeasurableSpace α] [MeasurableSpace β] : CoeFun (Pushforward_Measure α β) fun _ => Set β → ℝ≥0∞ :=
  ⟨fun m => m.μ.toOuterMeasure ∘ m.f_inv⟩

variable (α : Type _) (β : Type _) (h1 : MeasurableSpace α) (h2 : MeasurableSpace β) (μ : Pushforward_Measure α β) (s : Set β)
#check μ s -/