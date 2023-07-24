import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import GOSVGDProofs.Bijection
import GOSVGDProofs.AbsoluteContinuity
import GOSVGDProofs.PushForward
open ENNReal

set_option trace.Meta.Tactic.simp.rewrite true

open MeasureTheory MeasureTheory.Measure

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α] [BorelSpace α]
variable {ν : Measure α} [IsAddHaarMeasure ν] -- Lebesgue
variable (μ_t : Pushforward_Measure α α) {is_prob_m_μ : IsProbabilityMeasure μ_t.μ} {is_prob_m_p_μ : IsProbabilityMeasure μ_t.p_μ}
variable {habs1 : absolutely_continuous μ_t.μ ν}
variable (T' : α → α →L[ℝ] α) (hT' : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt μ_t.T_inv (T' x) s x) (d_μ : α → ℝ≥0∞) (h_density_μ : is_density μ_t.μ ν d_μ)

noncomputable def push_forward_density (μ_t : Pushforward_Measure α α) (d_μ : α → ℝ≥0∞) (_h : is_density μ_t.μ ν d_μ) (T' : α → α →L[ℝ] α) (_h2 : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt μ_t.T_inv (T' x) s x) (x : α) := ENNReal.ofReal |(T' x).det| * d_μ (μ_t.T_inv x)

lemma push_forward_has_density (h1 : is_density μ_t.μ ν d_μ) (h2 : ∀ (s : Set α), MeasurableSet s) : is_density μ_t.p_μ ν (push_forward_density μ_t d_μ h1 T' hT') :=
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
rw [h1 (μ_t.T_inv '' A)]
rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul ν (h2 A) (hT' A) T_invisInjonA d_μ]
unfold push_forward_density
simp

variable (s : Set α) (s_unique_diff : UniqueDiffOn ℝ s)
lemma det_of_derivative_of_composition_of_reciprocal_eq_1 (f : α → β) (f_inv : β → α) (h1 : is_reciprocal f f_inv) (h2 : ∀ x ∈ s, HasFDerivWithinAt (f_inv ∘ f) (T' x) s x) : ∀ (a : α), a ∈ s → (T' a).det = 1 :=
by
intros a ainS
have key : T' a = ContinuousLinearMap.id ℝ α := by
{
  have k1 : HasFDerivWithinAt id (ContinuousLinearMap.id ℝ α) s a := by
  {
    have k2 : fderivWithin ℝ id s a = ContinuousLinearMap.id ℝ α := fderivWithin_id (s_unique_diff a ainS)
    rw [←k2]
    have k3 : DifferentiableWithinAt ℝ id s a := by
    {
      use T' a
      rw [← (composition_inv_eq_id f f_inv h1).right]
      exact h2 a ainS
    }
    exact DifferentiableWithinAt.hasFDerivWithinAt k3
  }
  specialize h2 a ainS
  rw [(composition_inv_eq_id f f_inv h1).right] at h2
  exact UniqueDiffOn.eq s_unique_diff ainS h2 k1
}
rw [key]
unfold ContinuousLinearMap.det
simp

def push_forward_density_composition (f : α → α) (T_compose' : α → α →L[ℝ] α) (_h :  ∀ x ∈ s, HasFDerivWithinAt (μ_t.T_inv ∘ f) (T_compose' x) s x) := ∀ (x : α), ((push_forward_density μ_t d_μ h_density_μ T' hT') ∘ f) x = ENNReal.ofReal |(T_compose' x).det| * d_μ ((μ_t.T_inv ∘ f) x)

lemma push_forward_density_equality (T_compose' : α → α →L[ℝ] α) (h : ∀ x ∈ s, HasFDerivWithinAt (μ_t.T_inv ∘ μ_t.T) (T_compose' x) s x) (h2 : push_forward_density_composition μ_t T' hT' d_μ h_density_μ s μ_t.T T_compose' h) : ∀ (a : α), a ∈ s → ((push_forward_density μ_t d_μ h_density_μ T' hT') ∘ μ_t.T) a  = d_μ a :=
by
intro a ainS
rw [h2]
rw [(composition_inv_eq_id μ_t.T μ_t.T_inv μ_t.is_reci).right]
rw [det_of_derivative_of_composition_of_reciprocal_eq_1 T_compose' s s_unique_diff μ_t.T μ_t.T_inv μ_t.is_reci h a ainS]
simp

variable (π : Measure α) (d_π : α → ℝ≥0∞)
variable (π_t : Pushforward_Measure α α) (h_pi_T : π_t.T = μ_t.T_inv) (h_pi_μ : π_t.μ = π) (h_density_π : is_density π_t.μ ν d_π) [IsProbabilityMeasure π_t.μ] [IsProbabilityMeasure π_t.p_μ]

noncomputable def d_p := push_forward_density μ_t d_μ h_density_μ T' hT'
variable (h_density_p_μ : is_density μ_t.p_μ ν (d_p μ_t T' hT' d_μ h_density_μ))

variable (Tπ' : α → α →L[ℝ] α) (hTπ' : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt π_t.T_inv (Tπ' x) s x)
variable (h_density_p_π : is_density π_t.p_μ ν (d_p π_t Tπ' hTπ' d_π h_density_π))

noncomputable def log (a : ℝ≥0∞) := Real.log (ENNReal.toReal a)

noncomputable def KL (μ : Measure α) (d_μ : α → ℝ≥0∞) (d_π : α → ℝ≥0∞) := ∫ x in Set.univ, log ((d_μ x) / (d_π x)) ∂μ

variable (univ_unique_diff : UniqueDiffOn ℝ (Set.univ : Set α))
example (Tμ_comp' : α → α →L[ℝ] α) (Tπ_comp' : α → α →L[ℝ] α) (h1 : ∀ x ∈ Set.univ, HasFDerivWithinAt (μ_t.T_inv ∘ μ_t.T) (Tμ_comp' x) Set.univ x) (h2 : ∀ x ∈ Set.univ, HasFDerivWithinAt (π_t.T_inv ∘ π_t.T) (Tπ_comp' x) Set.univ x) (h3 : push_forward_density_composition μ_t T' hT' d_μ h_density_μ Set.univ μ_t.T Tμ_comp' h1) (h4 : push_forward_density_composition π_t Tπ' htπ' d_π h_density_π Set.univ π_t.T Tπ_comp' h2) : KL μ_t.p_μ (d_p μ_t T' hT' d_μ h_density_μ) d_π = KL μ_t.μ d_μ (d_p π_t Tπ' hTπ' d_π h_density_π) :=
by
--rw [KL_μ_t_π]
unfold KL
rw [μ_t.integration]

have k_μ : (fun x => log (d_p μ_t T' hT' d_μ h_density_μ x / d_π x)) ∘ μ_t.T = (fun x => log ((d_μ x) / ((d_π ∘ μ_t.T) x)) ):= by
{
  have k : ∀ (a : α), (d_p μ_t T' hT' d_μ h_density_μ ∘ μ_t.T) a = d_μ a := by 
  {
    have key := push_forward_density_equality μ_t T' hT' d_μ h_density_μ Set.univ univ_unique_diff Tμ_comp' h1 h3
    intro a
    exact key a (by simp)
  }
  conv =>
    rhs
    intro x
    rw [←k]
}

rw [k_μ]
rw [image_of_univ_is_univ μ_t.T μ_t.T_inv μ_t.is_bij μ_t.is_reci]

have k_π : (d_p π_t Tπ' hTπ' d_π h_density_π) = (d_π ∘ μ_t.T) := by 
{
  have key := push_forward_density_equality π_t Tπ' hTπ' d_π h_density_π Set.univ univ_unique_diff Tπ_comp' h2 h4
  ext a
  unfold Function.comp at key
  unfold Function.comp
  rw [←key (μ_t.T a) (by simp)]
  rw [h_pi_T]
  rw [μ_t.is_reci.right a]
  unfold d_p
  simp
}

rw [k_π]
