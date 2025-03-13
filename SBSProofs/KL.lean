/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.MeasureTheory.Function.Jacobian

import SBSProofs.Measure
import SBSProofs.Utils

open ENNReal

open MeasureTheory MeasureTheory.Measure

/--
  Expression of the (supposed for now) density of a pushforward measure.
-/
noncomputable def push_forward_density {α : Type*}
    [NormedAddCommGroup α] [Module ℝ α] [MeasureSpace α]
     (μ : DensityMeasure α) (μ_t : Pushforward_Measure α α)
    (_ : μ_t.μ = μ.toMeasure) (T' : α → α →L[ℝ] α) :=
  λ x ↦ ENNReal.ofReal |(T' x).det| * μ.d (μ_t.T_inv x)

namespace DetDerivative

variable {α β : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
{s : Set α} (T' : α → α →L[ℝ] α)

/--
  Given a map f, det (∂ₓ (f⁻¹ ∘ f) x) = 1.
-/
lemma det_of_derivative_of_composition_of_reciprocal_eq_1 (f : α → β) (f_inv : β → α)
    (h1 : is_reciprocal f f_inv)
    (h2 : ∀ x ∈ s, HasFDerivWithinAt (f_inv ∘ f) (T' x) s x)
    (s_unique_diff : UniqueDiffOn ℝ s) :
    ∀ (a : α), a ∈ s → (T' a).det = 1 :=
by
  intros a ainS

  -- We prove that ∂ₓ (f⁻¹ ∘ f) = 1 using that f⁻¹ ∘ f = id, ∂ₓ id = 1 and that the derivative is unique.
  have key : T' a = ContinuousLinearMap.id ℝ α := by
  {
    have k1 : HasFDerivWithinAt id (ContinuousLinearMap.id ℝ α) s a := by
    {
      have k2 : fderivWithin ℝ id s a = ContinuousLinearMap.id ℝ α :=
        fderivWithin_id (s_unique_diff a ainS)
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

end DetDerivative

namespace PushforwardDensity

variable {α : Type*} [MeasureSpace α] [NormedAddCommGroup α] [NormedSpace ℝ α]
(T' : α → α →L[ℝ] α) (μ : DensityMeasure α) (μ_t : Pushforward_Measure α α)
(h_μ : μ_t.μ = μ.toMeasure)

/--
  Given a map T and a measure μ, if μ admits a density dμ w.r.t. the Lebesgue measure, then T#µ admits a density d x ↦ |det(∂ₓT x)| ⬝ dμ (T⁻¹ x)).
-/
lemma push_forward_has_density [FiniteDimensional ℝ α] [BorelSpace α]
    [IsAddHaarMeasure (volume : Measure α)] (h1 : ∀ (s : Set α), MeasurableSet s)
    (hT' : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt μ_t.T_inv (T' x) s x):
    ∀ (s : Set α), μ_t.p_μ s = ∫⁻ x in s, (push_forward_density μ μ_t h_μ T') x :=
by
  intro A

  -- We use pushforward measure and density definitions.
  rw [μ_t.measure_app, h_μ]
  rw [μ.is_density (h1 (μ_t.T_inv '' A))]

  -- We show that f_inv is injective on A using the fact that f is bijective.
  have T_invisInjonA : Set.InjOn μ_t.T_inv A := by
  {
    apply is_inj_imp_set_inj
    have key : is_bijective μ_t.T_inv := reciprocal_of_bij_is_bij μ_t.T μ_t.T_inv μ_t.is_reci μ_t.is_bij
    exact key.left
  }

  -- Change of variable in integration.
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (h1 A) (hT' A) T_invisInjonA μ.d]
  unfold push_forward_density
  rfl

variable {s : Set α}

/--
When composing the density of a pushforward measure with a function, the composition appears **inside** the derivative.
-/
def push_forward_density_composition (f : α → α) (T_compose' : α → α →L[ℝ] α)
    (_h1 : ∀ x ∈ s, HasFDerivWithinAt (μ_t.T_inv ∘ f) (T_compose' x) s x) :=
  ∀ (x : α), (push_forward_density μ μ_t h_μ T' ∘ f) x
  = ENNReal.ofReal |(T_compose' x).det| * μ.d ((μ_t.T_inv ∘ f) x)

/--
Given a map T and a measure μ such that it admits a density dμ w.r.t. the Lebesgue measure, then the composition between the density of T#μ d and T equals dμ : d ∘ T = dμ
-/
lemma push_forward_density_equality (T_compose' : α → α →L[ℝ] α)
  (h : ∀ x ∈ s, HasFDerivWithinAt (μ_t.T_inv ∘ μ_t.T) (T_compose' x) s x)
  (h2 : push_forward_density_composition T' μ μ_t h_μ μ_t.T T_compose' h)
  (s_unique_diff : UniqueDiffOn ℝ s) :
  ∀ (a : α), a ∈ s → (push_forward_density μ μ_t h_μ T' ∘ μ_t.T) a = μ.d a :=
by
  intro a ainS
  rw [h2]
  rw [(composition_inv_eq_id μ_t.T μ_t.T_inv μ_t.is_reci).right]
  rw [
    DetDerivative.det_of_derivative_of_composition_of_reciprocal_eq_1
    T_compose'
    μ_t.T
    μ_t.T_inv
    μ_t.is_reci
    h
    s_unique_diff
    a
    ainS
  ]
  simp
end PushforwardDensity

variable {α β : Type*} [MeasureSpace α] [MeasureSpace β] [NormedAddCommGroup α] [NormedSpace ℝ α]

variable (μ_t : Pushforward_Measure α α) (μ : DensityMeasure α) (h_μ : μ_t.μ = μ.toMeasure)
[IsProbabilityMeasure μ_t.μ] [IsProbabilityMeasure μ_t.p_μ]

variable (T' : α → α →L[ℝ] α) (hT' : ∀ (s : Set α), ∀ x ∈ s, HasFDerivWithinAt μ_t.T_inv (T' x) s x)

variable (π : DensityMeasure α) (π_t : Pushforward_Measure α α) (h_π : π_t.μ = π.toMeasure)

variable (Tπ' : α → α →L[ℝ] α)


open PushforwardDensity

/--
  **Main resutlt:** Given a map T and two measures μ π, both admitting density w.r.t.
  the Lebesgue measure, then KL(T#μ || π) = KL(μ || T⁻¹#π).
-/
theorem KL_of_μ_t_π_eq_KL_of_π_t_μ (Tμ_comp' : α → α →L[ℝ] α) (Tπ_comp' : α → α →L[ℝ] α)
    (h1 : ∀ x ∈ Set.univ, HasFDerivWithinAt (μ_t.T_inv ∘ μ_t.T) (Tμ_comp' x) Set.univ x)
    (h2 : ∀ x ∈ Set.univ, HasFDerivWithinAt (π_t.T_inv ∘ π_t.T) (Tπ_comp' x) Set.univ x)
    (h3 : push_forward_density_composition T' μ μ_t h_μ μ_t.T Tμ_comp' h1)
    (h4 : push_forward_density_composition Tπ' π π_t h_π π_t.T Tπ_comp' h2)
    (univ_unique_diff : UniqueDiffOn ℝ (Set.univ : Set α))
    (h_pi_T : π_t.T = μ_t.T_inv) :
    KL μ_t.p_μ (push_forward_density μ μ_t h_μ T') π.d
    = KL μ_t.μ μ.d (push_forward_density π π_t h_π Tπ') :=
by

  -- We use the composition propriety of the pushforward measure
  unfold KL
  rw [μ_t.integration]

  -- We unfold the composition and use the *push_forward_density_equality* lemma
  have k_μ : (λ x ↦ log (push_forward_density μ μ_t h_μ T' x / π.d x)) ∘ μ_t.T = (λ x ↦ log ((μ.d x) / ((π.d ∘ μ_t.T) x)) ):= by
  {
    have k : ∀ (a : α), (push_forward_density μ μ_t h_μ T' ∘ μ_t.T) a = μ.d a := by
    {
      have key := push_forward_density_equality T' μ μ_t h_μ Tμ_comp' h1 h3 univ_unique_diff
      intro a
      exact key a (by simp)
    }
    conv =>
      rhs
      intro x
      rw [←k x]
    rfl
  }

  rw [k_μ]
  rw [image_of_univ_is_univ μ_t.T μ_t.T_inv μ_t.is_bij μ_t.is_reci]

  -- We show that dπ ∘ T is equal to the density of T⁻¹#π
  have k_π : push_forward_density π π_t h_π Tπ' = (π.d ∘ μ_t.T) := by
  {
    have key := push_forward_density_equality Tπ' π π_t h_π Tπ_comp' h2 h4 univ_unique_diff
    ext a
    unfold Function.comp at key ⊢
    rw [←key (μ_t.T a) (by simp)]
    rw [h_pi_T]
    rw [μ_t.is_reci.right a]
  }

  rw [←k_π]
