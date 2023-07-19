import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Init.Set
import GOSVGDProofs.Bijection
import GOSVGDProofs.AbsoluteContinuity
open ENNReal

namespace MeasureTheory

structure Pushforward_Measure (α : Type _) (β : Type _) [MeasurableSpace α] [MeasurableSpace β] extends Measure β where
p_μ : Measure β
μ : Measure α
f : α -> β
f_inv : β -> α
is_bij : is_bijective f
is_reci : is_reciprocal f f_inv

variable (α : Type _) (β : Type _) (h1 : MeasurableSpace α) (h2 : MeasurableSpace β)
variable (ν : Measure α) -- Lebesgue
variable (μ_t : Pushforward_Measure α α) (h1 : IsProbabilityMeasure μ_t.p_μ) (h2 : IsProbabilityMeasure μ_t.μ)

noncomputable def pushforward_average (μ : Pushforward_Measure α β) [IsProbabilityMeasure μ.p_μ] [IsProbabilityMeasure μ.μ] (f : β -> ℝ≥0∞) := laverage μ.p_μ f = ∫⁻ x, f (μ.f x) ∂(μ.μ)

def measure_integral (μ : Measure α) (A : Set α) := μ A = ∫⁻ x in A, 1 ∂μ

lemma has_density {μ ν : Measure α} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : absolutely_continuous μ ν) : ∃ (d : α -> ℝ≥0∞), ∀ (s : Set α), μ s = ∫⁻ x in s, d x ∂ν := by
-- Radon-Nikodym
sorry

def is_density {α : Type _} [MeasurableSpace α] (μ : Measure α) (ν : Measure α) (d : α -> ℝ≥0∞) := ∀ (s : Set α), μ s = ∫⁻ x in s, d x ∂ν

lemma test (f : α -> β) (f_inv : β -> α) (f_set : Set α -> Set β) (f_set_inv : Set β -> Set α) (h1 : is_reciprocal f f_inv) (h2 : is_set_extension f f_set) (h3 : is_set_extension f_inv f_set_inv) : ∀ (A : Set α), A = f_set_inv (f_set A) :=
by
intro A
ext a
constructor
{ 
  intro ainA
  rw [h3]
  use (f a)
  constructor
  {
    rw [h2]
    use a
    constructor
    { exact ainA }
    { exact Eq.refl (f a) }
  }
  exact h1.right a
}

{
  intro ainF
  rw [h3] at ainF
  cases ainF with
    | intro b ainF =>
      cases ainF with
        | intro binF r =>
          rw [h2] at binF
          cases binF with
            | intro l rr =>
              cases rr with
                | intro rr1 rr2 =>
                  rw [←rr2] at r
                  rw [h1.right l] at r
                  rwa [r] at rr1 
}

variable (f : Set α -> Set α)

lemma push_forward_density_equality (h1 : absolutely_continuous μ_t.μ ν) (f_mu : α -> ℝ≥0∞) (f_p_mu : α -> ℝ≥0∞) (hf1 : is_density μ_t.μ ν f_mu) (hf2 : is_density μ_t.p_μ ν f_p_mu) : ∀ (s : Set α), ∫⁻ x in s, f_mu x ∂ν = ∫⁻ x in (f s), f_p_mu x ∂ν := by
sorry


/- instance Pushforward_Measure.instCoeFun {α : Type _} {β : Type _} [MeasurableSpace α] [MeasurableSpace β] : CoeFun (Pushforward_Measure α β) fun _ => Set β → ℝ≥0∞ :=
  ⟨fun m => m.μ.toOuterMeasure ∘ m.f_inv⟩

variable (α : Type _) (β : Type _) (h1 : MeasurableSpace α) (h2 : MeasurableSpace β) (μ : Pushforward_Measure α β) (s : Set β)
#check μ s -/