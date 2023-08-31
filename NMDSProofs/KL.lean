import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import NMDSProofs.Bijection
import NMDSProofs.AbsoluteContinuity
import NMDSProofs.PushForward
import NMDSProofs.Utils
open ENNReal

set_option trace.Meta.Tactic.simp.rewrite true

open MeasureTheory MeasureTheory.Measure

variable {α β : Type _} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup α] [NormedSpace ℝ α] [FiniteDimensional ℝ α] [BorelSpace α]
variable {ν : Measure α} [IsAddHaarMeasure ν] -- Lebesgue
variable (μ_t : Pushforward_Measure α α) {is_prob_m_μ : IsProbabilityMeasure μ_t.μ} {is_prob_m_p_μ : IsProbabilityMeasure μ_t.p_μ}
variable {habs1 : absolutely_continuous μ_t.μ ν}
variable (T' : α → α →L[ℝ] α) (hT' : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt μ_t.T_inv (T' x) s x) (d_μ : α → ℝ≥0∞) (h_density_μ : is_density μ_t.μ ν d_μ)

/--
  Expression of the (supposed for now) density of a pushforward measure.
-/
noncomputable def push_forward_density := fun x ↦ ENNReal.ofReal |(T' x).det| * d_μ (μ_t.T_inv x)

/--
  Given a map T and a measure μ, if μ admits a density dμ w.r.t. the Lebesgue measure, then T#µ admits a density d x ↦ |det(∂ₓT x)| ⬝ dμ (T⁻¹ x)).
-/
lemma push_forward_has_density (h1 : ∀ (s : Set α), MeasurableSet s) : is_density μ_t.p_μ ν (push_forward_density μ_t T' d_μ) :=
by
  unfold is_density
  intro A

  -- We show that f_inv is injective on A using the fact that f is bijective.
  have T_invisInjonA : Set.InjOn μ_t.T_inv A := by
  {
    apply is_inj_imp_set_inj
    have key : is_bijective μ_t.T_inv := reciprocal_of_bij_is_bij μ_t.T μ_t.T_inv μ_t.is_reci μ_t.is_bij
    exact key.left
  }

  -- We use pushforward measure and density definitions.
  rw [μ_t.measure_app]
  rw [h_density_μ (μ_t.T_inv '' A)]

  -- Change of variable in integration.
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul ν (h1 A) (hT' A) T_invisInjonA d_μ]
  unfold push_forward_density
  simp


variable (s : Set α) (s_unique_diff : UniqueDiffOn ℝ s)

/--
  Given a map f, det (∂ₓ (f⁻¹ ∘ f) x) = 1.
-/
lemma det_of_derivative_of_composition_of_reciprocal_eq_1 (f : α → β) (f_inv : β → α) (h1 : is_reciprocal f f_inv) (h2 : ∀ x ∈ s, HasFDerivWithinAt (f_inv ∘ f) (T' x) s x) : ∀ (a : α), a ∈ s → (T' a).det = 1 :=
by
  intros a ainS

  -- We prove that ∂ₓ (f⁻¹ ∘ f) = 1 using that f⁻¹ ∘ f = id, ∂ₓ id = 1 and that the derivative is unique.
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

/--
When composing the density of a pushforward measure with a function, the composition appears **inside** the derivative.
-/
def push_forward_density_composition (f : α → α) (T_compose' : α → α →L[ℝ] α) (_h1 :  ∀ x ∈ s, HasFDerivWithinAt (μ_t.T_inv ∘ f) (T_compose' x) s x) := ∀ (x : α), (push_forward_density μ_t T' d_μ ∘ f) x = ENNReal.ofReal |(T_compose' x).det| * d_μ ((μ_t.T_inv ∘ f) x)

/--
Given a map T and a measure μ such that it admits a density dμ w.r.t. the Lebesgue measure, then the composition between the density of T#μ d and T equals dμ : d ∘ T = dμ
-/
lemma push_forward_density_equality (T_compose' : α → α →L[ℝ] α) (h : ∀ x ∈ s, HasFDerivWithinAt (μ_t.T_inv ∘ μ_t.T) (T_compose' x) s x) (h2 : push_forward_density_composition μ_t T' d_μ s μ_t.T T_compose' h) : ∀ (a : α), a ∈ s → (push_forward_density μ_t T' d_μ ∘ μ_t.T) a  = d_μ a :=
by
  intro a ainS
  rw [h2]
  
  rw [(composition_inv_eq_id μ_t.T μ_t.T_inv μ_t.is_reci).right]
  rw [det_of_derivative_of_composition_of_reciprocal_eq_1 T_compose' s s_unique_diff μ_t.T μ_t.T_inv μ_t.is_reci h a ainS]
  simp

variable (π : Measure α) (d_π : α → ℝ≥0∞)
variable (π_t : Pushforward_Measure α α) (h_pi_T : π_t.T = μ_t.T_inv) (h_pi_μ : π_t.μ = π) (h_density_π : is_density π_t.μ ν d_π) [IsProbabilityMeasure π_t.μ] [IsProbabilityMeasure π_t.p_μ]

variable (Tπ' : α → α →L[ℝ] α) (hTπ' : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt π_t.T_inv (Tπ' x) s x)

variable (univ_unique_diff : UniqueDiffOn ℝ (Set.univ : Set α))


/--
  Given a map T and two measures μ π, both admitting density w.r.t. the Lebesgue measure, then KL(T#μ || π) = KL(μ || T⁻¹#π)
-/
theorem KL_of_μ_t_π_eq_KL_of_π_t_μ (Tμ_comp' : α → α →L[ℝ] α) (Tπ_comp' : α → α →L[ℝ] α) (h1 : ∀ x ∈ Set.univ, HasFDerivWithinAt (μ_t.T_inv ∘ μ_t.T) (Tμ_comp' x) Set.univ x) (h2 : ∀ x ∈ Set.univ, HasFDerivWithinAt (π_t.T_inv ∘ π_t.T) (Tπ_comp' x) Set.univ x) (h3 : push_forward_density_composition μ_t T' d_μ Set.univ μ_t.T Tμ_comp' h1) (h4 : push_forward_density_composition π_t Tπ' d_π Set.univ π_t.T Tπ_comp' h2) : KL μ_t.p_μ (push_forward_density μ_t T' d_μ) d_π = KL μ_t.μ d_μ (push_forward_density π_t Tπ' d_π) :=
by

  -- We use the composition propriety of the pushforward measure
  unfold KL
  rw [μ_t.integration]

  -- We unfold the composition and use the *push_forward_density_equality* lemma
  have k_μ : (fun x ↦ log (push_forward_density μ_t T' d_μ x / d_π x)) ∘ μ_t.T = (fun x ↦ log ((d_μ x) / ((d_π ∘ μ_t.T) x)) ):= by
  {
    have k : ∀ (a : α), (push_forward_density μ_t T' d_μ  ∘ μ_t.T) a = d_μ a := by 
    {
      have key := push_forward_density_equality μ_t T' d_μ Set.univ univ_unique_diff Tμ_comp' h1 h3
      intro a
      exact key a (by simp)
    }
    conv =>
      rhs
      intro x
      rw [←k x]
  }

  rw [k_μ]
  rw [image_of_univ_is_univ μ_t.T μ_t.T_inv μ_t.is_bij μ_t.is_reci]

  -- We show that dπ ∘ T is equal to the density of T⁻¹#π
  have k_π : push_forward_density π_t Tπ' d_π = (d_π ∘ μ_t.T) := by 
  {
    have key := push_forward_density_equality π_t Tπ' d_π Set.univ univ_unique_diff Tπ_comp' h2 h4
    ext a
    unfold Function.comp at key ⊢
    rw [←key (μ_t.T a) (by simp)]
    rw [h_pi_T]
    rw [μ_t.is_reci.right a]
  }

  rw [←k_π]
