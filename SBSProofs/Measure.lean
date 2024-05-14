/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.MeasureTheory.Integral.Bochner

import SBSProofs.Bijection

open ENNReal MeasureTheory

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
  lebesgue_density : toMeasure = volume.withDensity d

instance DensityMeasure.instCoeFun : CoeFun (DensityMeasure α) λ _ => Set α → ℝ≥0∞ := ⟨fun m => m.toOuterMeasure⟩

namespace DensityMeasure

lemma is_density (μ : DensityMeasure α) : ∀ ⦃s⦄, MeasurableSet s → μ.measureOf s = ∫⁻ x in s, μ.d x := by
  intro s hs
  rw [←withDensity_apply μ.d hs]
  have t := μ.lebesgue_density
  exact congrFun (congrArg OuterMeasure.measureOf (congrArg Measure.toOuterMeasure t)) s

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

lemma density_lintegration {μ : DensityMeasure α} (f : α → ℝ≥0∞) (hm : Measurable f) : ∫⁻ x, f x ∂μ.toMeasure = ∫⁻ x, μ.d x * f x :=
by
  rw [μ.lebesgue_density]
  rw [lintegral_withDensity_eq_lintegral_mul volume μ.d_measurable hm]
  simp_rw [show ∀ x, (μ.d * f) x = μ.d x * f x by simp]

attribute [coe] DensityMeasure.toMeasure

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
      lebesgue_density := μ₁.lebesgue_density
      } := rfl

  rewrite (config := {occs := .pos [1]}) [destruct]
  simp_rw [eq_measure, f_ext]

lemma coe_ext_measure (m1 m2 : Measure α) (h : ∀ s, MeasurableSet s → m1 s = m2 s) : m1 = m2 := Measure.ext_iff.mpr h

theorem density_ae_eq_imp_eq_measure (m1 m2 : DensityMeasure α) (h : m1.d =ᵐ[volume] m2.d) : m1.toMeasure = m2.toMeasure := by

  apply coe_ext_measure
  intro s hs
  rw [m1.is_density hs, m2.is_density hs]

  have ae_eq_set : ∀ᵐ x, x ∈ s → m1.d x = m2.d x := by {
    unfold Filter.EventuallyEq at h
    unfold Filter.Eventually at *
    have subset : {x | ¬(x ∈ s → m1.d x = m2.d x)} ⊆ {x | (m1.d x ≠ m2.d x)} := by {
      intro x hx; push_neg at hx
      exact hx.2
    }
    rw [mem_ae_iff] at *
    rw [show {x | m1.d x = m2.d x}ᶜ = {x | m1.d x ≠ m2.d x} by rfl] at h
    rw [show {x | x ∈ s → m1.d x = m2.d x}ᶜ = {x | ¬(x ∈ s → m1.d x = m2.d x)} by rfl]

    let A := {x | m1.d x ≠ m2.d x}
    let B := {x | ¬(x ∈ s → m1.d x = m2.d x)}

    have measure_increasing : volume B <= volume A := volume.mono subset
    rw [h] at measure_increasing
    exact nonpos_iff_eq_zero.mp measure_increasing
  }

  exact set_lintegral_congr_fun hs ae_eq_set

end DensityMeasure
