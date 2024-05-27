/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.MeasureTheory.Function.AEEqOfIntegral

import SBSProofs.Bijection

open ENNReal MeasureTheory

set_option maxHeartbeats 400000

variable {α β : Type*} [MeasureSpace α] [MeasureSpace β]

/-
  Definition of pushforward measure
-/

def measure_set_of_pushforward_measure (μ : Measure α) (p_μ : Measure β) (f : β → α) := ∀ (B : Set β), p_μ B = μ (f '' B)

def push_forward_integration (μ : Measure α) (p_μ : Measure β) (T : α → β) (T_inv : β → α) := ∀ (φ : β → ℝ), ∀ (B : Set β), ∫ x in B, φ x ∂p_μ = ∫ x in T_inv '' B, (φ ∘ T) x ∂μ

structure Pushforward_Measure (α β : Type*) [MeasureSpace α] [MeasureSpace β] where
  p_μ : Measure β
  μ : Measure α
  T : α → β
  T_inv : β → α
  measure_app : measure_set_of_pushforward_measure μ p_μ T_inv
  is_bij : is_bijective T
  is_reci : is_reciprocal T T_inv
  integration : push_forward_integration μ p_μ T T_inv

/--
  Definition of measure with density w.r.t. the Lesbegue measure.
-/
structure DensityMeasure (α : Type*) [MeasureSpace α] extends Measure α where
  d : α → ℝ≥0∞
  d_neq_top : ∀ x, d x ≠ ⊤
  d_measurable : Measurable d
  d_finite : ∫⁻ x, d x ≠ ∞
  lebesgue_density : toMeasure = volume.withDensity d

variable {μ : Measure α}

theorem fun_ae_imp_set_ae {f g : α → β} :
    f =ᵐ[μ] g ↔ ∀ (s : Set α), ∀ᵐ x ∂ μ, x ∈ s → f x = g x :=
  Iff.intro
  (λ h s ↦ by filter_upwards [h] with _ ha _ using ha)
  (λ h ↦ by filter_upwards [h Set.univ] with _ ha using (ha (by simp)))

lemma coe_ae {μ : Measure α} {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : (λ x ↦ (f x).toReal) =ᵐ[μ] (λ x ↦ (g x).toReal) := by

  have compl_ss : {x | (f x).toReal = (g x).toReal}ᶜ ⊆ {x | f x = g x}ᶜ := by {
    have eq_ss : {x | f x = g x} ⊆ {x | (f x).toReal = (g x).toReal} := by {
      intro x (hx : f x = g x)
      exact congrArg ENNReal.toReal hx
    }
    exact Set.compl_subset_compl_of_subset eq_ss
  }

  have leq_μ : μ {x | (f x).toReal = (g x).toReal}ᶜ  <= μ {x | f x = g x}ᶜ := measure_mono compl_ss

  have  h_ae: μ {x | f x ≠ g x} = 0 := by exact h
  rw [h] at leq_μ
  exact nonpos_iff_eq_zero.mp leq_μ

namespace DensityMeasure

instance instCoeFun : CoeFun (DensityMeasure α) λ _ => Set α → ℝ≥0∞ := ⟨fun m => m.toMeasure⟩

theorem is_density (μ : DensityMeasure α) : ∀ ⦃s⦄, MeasurableSet s → μ s = ∫⁻ x in s, μ.d x := by
  intro s hs
  rw [←withDensity_apply μ.d hs]
  exact congrFun (congrArg OuterMeasure.measureOf (congrArg Measure.toOuterMeasure μ.lebesgue_density)) s

lemma density_integration {μ : DensityMeasure α} {f : α → ℝ} (hi : Integrable f μ.toMeasure) (hm_up : Measurable (λ x ↦ ENNReal.ofReal (f x))) (hm_lo : Measurable (λ x ↦ ENNReal.ofReal (-f x))) (hi_mul : Integrable (λ x ↦ (μ.d x).toReal * f x)) : ∫ x, f x ∂μ.toMeasure = ∫ x, ENNReal.toReal (μ.d x) * f x := by

  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi, μ.lebesgue_density]
  rw [lintegral_withDensity_eq_lintegral_mul volume μ.d_measurable hm_up]
  rw [lintegral_withDensity_eq_lintegral_mul volume μ.d_measurable hm_lo]

  have rw_fun : ∀ (f : α → ℝ), ∀ a, (μ.d * (λ a ↦ ENNReal.ofReal (f a))) a = μ.d a * ENNReal.ofReal (f a) := by {
    intro f a
    rfl
  }
  simp_rw [rw_fun f, rw_fun (λ x ↦ -f x)]

  have coe_density_nonneg : ∀ a, 0 <= (μ.d a).toReal := λ a ↦ toReal_nonneg

  have enn_up_coe : ∀ a, ENNReal.ofReal ((μ.d a).toReal * f a) = μ.d a * ENNReal.ofReal (f a) := by {
    intro a
    rw (config := {occs := .pos [2]}) [←ofReal_toReal_eq_iff.mpr (μ.d_neq_top a)]
    exact ofReal_mul (coe_density_nonneg a)
  }
  simp_rw [←enn_up_coe]

  have enn_lo_coe : ∀ a, ENNReal.ofReal (-((μ.d a).toReal * (f a))) = μ.d a * ENNReal.ofReal (-f a) := by {
    intro a
    rw [show -((μ.d a).toReal * (f a)) = (μ.d a).toReal * (-f a) by ring]
    rw (config := {occs := .pos [2]}) [←ofReal_toReal_eq_iff.mpr (μ.d_neq_top a)]
    exact ofReal_mul (coe_density_nonneg a)
  }
  simp_rw [←enn_lo_coe]

  rw[←integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi_mul]

theorem density_lintegration {μ : DensityMeasure α} (f : α → ℝ≥0∞) (hm : Measurable f) : ∫⁻ x, f x ∂μ.toMeasure = ∫⁻ x, μ.d x * f x :=
by
  rw [μ.lebesgue_density]
  rw [lintegral_withDensity_eq_lintegral_mul volume μ.d_measurable hm]
  simp only [Pi.mul_apply]

@[ext]
theorem ext {μ₁ μ₂ : DensityMeasure α} (h : ∀ x, μ₁.d x = μ₂.d x) : μ₁ = μ₂ := by
  have f_ext := funext h
  rw [show (λ x ↦ μ₁.d x) = μ₁.d by rfl] at f_ext
  rw [show (λ x ↦ μ₂.d x) = μ₂.d by rfl] at f_ext

  have eq_measure : μ₁.toMeasure = μ₂.toMeasure := by {
    rw [μ₁.lebesgue_density, μ₂.lebesgue_density, f_ext]
  }

  have destruct : μ₁ = {
      toMeasure := μ₁.toMeasure,
        d := μ₁.d,
        d_neq_top := μ₁.d_neq_top,
        d_measurable := μ₁.d_measurable,
        d_finite := μ₁.d_finite
      lebesgue_density := μ₁.lebesgue_density
      } := rfl

  rewrite (config := {occs := .pos [1]}) [destruct]
  simp_rw [eq_measure, f_ext]


lemma coe_ext_measure (μ₁ μ₂ : Measure α) (h : ∀ s, MeasurableSet s → μ₁ s = μ₂ s) : μ₁ = μ₂ := Measure.ext_iff.mpr h

/--
TODO: Add to Mathlib
-/
theorem densities_ae_eq_iff_eq_measure {μ₁ μ₂ : DensityMeasure α} :
    μ₁.d =ᵐ[volume] μ₂.d ↔ μ₁.toMeasure = μ₂.toMeasure := by
  constructor
  · intro h
    rw [μ₁.lebesgue_density, μ₂.lebesgue_density]
    exact withDensity_congr_ae h
  intro h
  have eq_set_lintegral : ∀ ⦃s⦄, MeasurableSet s → volume s < ∞ → ∫⁻ x in s, μ₁.d x = ∫⁻ x in s, μ₂.d x := by {
    intro s hs _
    rw [←μ₁.is_density hs, ←μ₂.is_density hs]
    exact congrFun (congrArg OuterMeasure.measureOf (congrArg Measure.toOuterMeasure h)) s
  }
  exact AEMeasurable.ae_eq_of_forall_set_lintegral_eq
    (Measurable.aemeasurable μ₁.d_measurable)
    (Measurable.aemeasurable μ₂.d_measurable)
    μ₁.d_finite μ₂.d_finite eq_set_lintegral

/--
TODO: Add to Mathlib
-/
theorem ae_density_measure_iff_ae_volume {μ : DensityMeasure α} {f g : α → ℝ≥0∞} (h_nonneg : ∀ x, μ.d x ≠ 0) : (f =ᵐ[μ.toMeasure] g) ↔ (f =ᵐ[volume] g) := by

  let s := {x | f x = g x}ᶜ

  have nonneg_eq_univ : {x | μ.d x ≠ 0} = Set.univ := by {
    ext x
    constructor
    · intro _; trivial
    intro _; exact h_nonneg x
  }

  constructor
  · intro (h : μ s = 0)
    rw [μ.lebesgue_density] at h
    have extract_density : volume ({x | μ.d x ≠ 0} ∩ s) = 0 := (withDensity_apply_eq_zero μ.d_measurable).mp h
    rwa [nonneg_eq_univ, Set.univ_inter s] at extract_density

  intro (h : volume s = 0)
  rw [show (f =ᵐ[μ.toMeasure] g) ↔ (μ {x | f x = g x}ᶜ) = 0 by rfl]
  rw [μ.lebesgue_density]
  rw [withDensity_apply_eq_zero μ.d_measurable]
  rwa [nonneg_eq_univ, Set.univ_inter s]

end DensityMeasure
