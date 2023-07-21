import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Group.Measure

import GOSVGDProofs.Bijection
import GOSVGDProofs.AbsoluteContinuity
import GOSVGDProofs.PushForward
open ENNReal

open MeasureTheory MeasureTheory.Measure

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α] [BorelSpace α]
variable (T' : α → α →L[ℝ] α) (d_μ : α → ℝ≥0∞)
variable {ν : Measure α} [IsAddHaarMeasure ν] -- Lebesgue
variable (μ_t : Pushforward_Measure α α) {h1 : IsProbabilityMeasure μ_t.p_μ} {h2 : IsProbabilityMeasure μ_t.μ}
variable {habs1 : absolutely_continuous μ_t.μ ν} {habs2 : absolutely_continuous μ_t.p_μ ν}

/- lemma push_forward_density_equality : ∃ (d_μ d_p_μ : α → ℝ≥0∞),  ∀ (A : Set α), ∫⁻ x in A, d_μ x ∂ν = ∫⁻ x in (μ_t.T '' A), d_p_μ x ∂ν :=
by

have h_density_μ : ∃ (d : α → ℝ≥0∞), ∀ (s : Set α), μ_t.μ s = ∫⁻ x in s, d x ∂ν := has_density habs1

have h_density_p_μ : ∃ (d : α → ℝ≥0∞), ∀ (s : Set α), μ_t.p_μ s = ∫⁻ x in s, d x ∂ν := has_density habs2

cases h_density_μ with
  | intro d_μ h_density_μ =>
    use d_μ
    cases h_density_p_μ with
      | intro d_p_μ h_density_p_μ =>
        use d_p_μ
        intro A
        rw [← h_density_μ A, ← h_density_p_μ (μ_t.T '' A)]
        rw [μ_t.measure_app]
        rw [← (identity_reciprocal_set_extension μ_t.T μ_t.T_inv μ_t.is_reci).left A] -/

lemma push_forward_density (h1 : is_density μ_t.μ ν d_μ) (h2 : ∀ (s : Set α), MeasurableSet s ∧ ∀ x ∈ s, HasFDerivWithinAt μ_t.T_inv (T' x) s x) : is_density μ_t.p_μ ν (fun x => ENNReal.ofReal |(T' x).det| * d_μ (μ_t.T_inv x)) :=
by
unfold is_density
intro A
/- We show that f_inv is injective on A using the fact that f is bijective -/
have T_invisInjonA : Set.InjOn μ_t.T_inv A := by
{
  apply is_inj_imp_set_inj
  have key : is_bijective μ_t.T_inv := reciprocal_of_bij_is_bij μ_t.T μ_t.T_inv μ_t.is_reci μ_t.is_bij
  exact key.left
}

rw [μ_t.measure_app]
specialize h2 A
cases h2 with
  | intro AisM FisD =>
    rw [h1 (μ_t.T_inv '' A)]
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul ν AisM FisD T_invisInjonA d_μ]

noncomputable def d_p_μ (h : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt μ_t.T_inv (T' x) s x) (a : α) := ENNReal.ofReal |(T' a).det| * d_μ (μ_t.T_inv a)

/- Derivative of f^(-1)' (f x) = x ∧ |det 1| = 1 -/
lemma int (h : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt μ_t.T_inv (T' x) s x) : ∀ (a : α), |(T' (μ_t.T a)).det| = 1 := by sorry

lemma push_forward_density_equality (h : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt μ_t.T_inv (T' x) s x) : ∀ (a : α), (d_p_μ T' d_μ μ_t h) (μ_t.T a) = d_μ a :=
by
intro a
unfold d_p_μ
rw [μ_t.is_reci.right a]
rw [int T' μ_t h a]
simp