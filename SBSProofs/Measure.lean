/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.MeasureTheory.Integral.Bochner

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
  d_finite : ∀ s, ∫⁻ x in s, d x ≠ ∞
  lebesgue_density : toMeasure = volume.withDensity d

/--
TODO: Add to Mathlib
-/
lemma ae_eq_imp_set_ae_eq {μ : Measure α} {f g : α → ℝ≥0∞} (h : f =ᵐ[μ] g) : ∀ (s : Set α), ∀ᵐ x ∂μ, x ∈ s → f x = g x := by
  intro s
  unfold Filter.EventuallyEq at h
  unfold Filter.Eventually at *
  have subset : {x | ¬(x ∈ s → f x = g x)} ⊆ {x | (f x ≠ g x)} := by {
    intro x hx; push_neg at hx
    exact hx.2
  }
  rw [mem_ae_iff] at *
  rw [show {x | f x = g x}ᶜ = {x | f x ≠ g x} by rfl] at h
  rw [show {x | x ∈ s → f x = g x}ᶜ = {x | ¬(x ∈ s → f x = g x)} by rfl]

  let A := {x | f x ≠ g x}
  let B := {x | ¬(x ∈ s → f x = g x)}

  have measure_increasing : μ B <= μ A := μ.mono subset
  rw [h] at measure_increasing
  exact nonpos_iff_eq_zero.mp measure_increasing

/--
TODO: Add to Mathlib
-/
theorem set_lintegral_eq_iff_ae_eq {μ : Measure α} {f g : α → ℝ≥0∞} (hfm : Measurable f) (hgm : Measurable g) (hfi : ∀ s, ∫⁻ x in s, f x ∂μ ≠ ∞) (hgi : ∀ s, ∫⁻ x in s, g x ∂μ ≠ ∞) (hft : ∀ x, f x ≠ ⊤) (hgt : ∀ x, g x ≠ ⊤) : (∀ ⦃s⦄, MeasurableSet s → ∫⁻ x in s, f x ∂μ = ∫⁻ x in s, g x ∂μ) ↔ f =ᵐ[μ] g := by
  constructor
  · intro h
    let A := {x | f x < g x}
    have hmA : MeasurableSet A := measurableSet_lt hfm hgm

    let B := {x | g x < f x}
    have hmB : MeasurableSet B := measurableSet_lt hgm hfm

    have union_eq_neq : A ∪ B = {x | f x = g x}ᶜ := by {
      ext x
      constructor
      · intro hx
        cases hx with
        | inl hx =>
          have ineq_coe := (toReal_lt_toReal (hft x) (hgt x)).mpr hx
          have coe_neq : (f x).toReal ≠ (g x).toReal := ne_of_lt ineq_coe
          exact λ neq ↦ coe_neq (congrArg ENNReal.toReal neq)
        | inr hx =>
          have ineq_coe := (toReal_lt_toReal (hgt x) (hft x)).mpr hx
          have coe_neq : (f x).toReal ≠ (g x).toReal := (ne_of_lt ineq_coe).symm
          exact λ neq ↦ coe_neq (congrArg ENNReal.toReal neq)
      intro hx
      rw [show A ∪ B = {x | f x < g x ∨ g x < f x} by rfl]
      rw [show x ∈ {x | f x < g x ∨ g x < f x} ↔ f x < g x ∨ g x < f x by rfl]
      by_contra h; push_neg at h
      rcases h with ⟨h1, h2⟩
      have h1_coe := (toReal_le_toReal (hgt x) (hft x)).mpr h1
      have h2_coe := (toReal_le_toReal (hft x) (hgt x)).mpr h2
      have eq_coe : (f x).toReal = (g x).toReal := by linarith
      have neq_coe : (f x).toReal ≠ (g x).toReal := by {
        by_contra hc
        exact hx ((toReal_eq_toReal_iff' (hft x) (hgt x)).mp hc)
      }
      exact neq_coe eq_coe
    }

    have m_union_eq_0 : μ (A ∪ B) = 0 := by {
      have mA_eq_0 : μ A = 0 := by {
        by_contra m_pos; push_neg at m_pos

        have lt_integral : ∫⁻ x in A, f x ∂μ < ∫⁻ x in A, g x ∂μ := set_lintegral_strict_mono hmA m_pos hgm (hfi A) (ae_of_all μ (λ x hx ↦ hx))

        rw [h hmA] at lt_integral
        have := toReal_strict_mono (hgi A) lt_integral
        linarith
      }

      have mB_eq_0 : μ B = 0 := by {
        by_contra m_pos; push_neg at m_pos

        have lt_integral : ∫⁻ x in B, g x ∂μ < ∫⁻ x in B, f x ∂μ := set_lintegral_strict_mono hmB m_pos hfm (hgi B) (ae_of_all μ (λ x hx ↦ hx))

        rw [h hmB] at lt_integral
        have := toReal_strict_mono (hgi B) lt_integral
        linarith
      }
      exact measure_union_null mA_eq_0 mB_eq_0
    }

    rwa [union_eq_neq] at m_union_eq_0

  intro h s hs
  exact set_lintegral_congr_fun hs (ae_eq_imp_set_ae_eq h s)

/--
TODO: Add to Mathlib
-/
lemma positive_measure_imp_positive_integral {μ : Measure α} {C : Set α} (hmC : MeasurableSet C) (hm : 0 < μ C) {h : α → ℝ≥0∞} (hneq : ∀ x ∈ C, h x ≠ 0) (hmm : Measurable h) : 0 < ∫⁻ x in C, h x ∂μ := by
  rw [show ∫⁻ x in C, h x ∂μ = ∫⁻ x, h x ∂μ.restrict C by rfl]
  have restrict_measure_support : μ.restrict C (Function.support h) = μ (Function.support h ∩ C) := Measure.restrict_apply' hmC

  have C_ss_support : C ⊆ Function.support h := λ x hC ↦ hneq x hC

  have inter_eq_C : Function.support h ∩ C = C := Set.inter_eq_self_of_subset_right hneq

  rw [congrArg (↑↑μ) inter_eq_C] at restrict_measure_support
  rw [←restrict_measure_support] at hm

  rw [lintegral_pos_iff_support hmm]
  exact hm

theorem ae_mul_fun {β : Type} [HMul β β β] {μ : Measure α} {f g h : α → β} (h_ae : f =ᵐ[μ] g) : ∀ᵐ x ∂μ, f x * h x = g x * h x := by

  have compl_ss : {x | f x * h x = g x * h x}ᶜ ⊆ {x | f x = g x}ᶜ := by {
    have mul_ss : {x | f x = g x} ⊆ {x | f x * h x = g x * h x} := by {
      intro x (hx : f x = g x)
      have rw_eq : f x * h x = g x * h x := by rw [hx]
      exact rw_eq
    }
    exact Set.compl_subset_compl_of_subset mul_ss
  }

  have leq_μ : μ {x | f x * h x ≠ g x * h x} <= μ {x | f x ≠ g x} := measure_mono compl_ss
  have  h_ae: μ {x | f x ≠ g x} = 0 := by exact h_ae
  rw [h_ae] at leq_μ

  exact nonpos_iff_eq_zero.mp leq_μ

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

instance instCoeFun : CoeFun (DensityMeasure α) λ _ => Set α → ℝ≥0∞ := ⟨fun m => m.toOuterMeasure⟩

theorem is_density (μ : DensityMeasure α) : ∀ ⦃s⦄, MeasurableSet s → μ.measureOf s = ∫⁻ x in s, μ.d x := by
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

theorem density_lintegration {μ : DensityMeasure α} (f : α → ℝ≥0∞) (hm : Measurable f) : ∫⁻ x, f x ∂μ.toMeasure = ∫⁻ x, μ.d x * f x :=
by
  rw [μ.lebesgue_density]
  rw [lintegral_withDensity_eq_lintegral_mul volume μ.d_measurable hm]
  simp_rw [show ∀ x, (μ.d * f) x = μ.d x * f x by simp]

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
theorem densities_ae_eq_iff_eq_measure {μ₁ μ₂ : DensityMeasure α} : μ₁.d =ᵐ[volume] μ₂.d ↔ μ₁.toMeasure = μ₂.toMeasure := by
  constructor
  · intro h
    apply coe_ext_measure
    intro s hs
    rw [μ₁.is_density hs, μ₂.is_density hs]
    exact set_lintegral_congr_fun hs (ae_eq_imp_set_ae_eq h s)

  intro h
  have eq_set_lintegral : ∀ s, MeasurableSet s → ∫⁻ x in s, μ₁.d x = ∫⁻ x in s, μ₂.d x := by {
    intro s hs
    rw [←μ₁.is_density hs, ←μ₂.is_density hs]
    exact congrFun (congrArg OuterMeasure.measureOf (congrArg Measure.toOuterMeasure h)) s
  }

  exact (set_lintegral_eq_iff_ae_eq μ₁.d_measurable μ₂.d_measurable μ₁.d_finite μ₂.d_finite μ₁.d_neq_top μ₂.d_neq_top).mp eq_set_lintegral


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
