import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

import GOSVGDProofs.PushForward

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open BigOperators Finset ENNReal NNReal MeasureTheory MeasureTheory.Measure IsROrC
open scoped RealInnerProductSpace

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 4000000

noncomputable def log (a : ℝ≥0∞) := Real.log (ENNReal.toReal a)

lemma nn_comp_exp_log (a : ℝ≥0∞) (ha : a ≠ 0) (ha2 : a ≠ ∞) : Real.exp (log a) = ENNReal.toReal a := by {
  by_cases ENNReal.toReal a = 0
  {
    exfalso
    have t : a = 0 ∨ a = ∞ := (toReal_eq_zero_iff a).mp h
    cases t with
    | inl hp => exact ha hp
    | inr hq => exact ha2 hq
  }
  {
    push_neg at h
    have t : ENNReal.toReal a ≠ 0 → ENNReal.toReal a < 0 ∨ 0 < ENNReal.toReal a := by {simp}
    specialize t h
    cases t with
    | inl hp => {
      have tt : 0 < ENNReal.toReal a := toReal_pos ha ha2
      linarith
    }
    | inr hq => exact Real.exp_log hq
  }
}

lemma cancel_log_exp (a : ℝ≥0∞) (ha : a ≠ 0) (ha2 : a ≠ ∞) (c : ℝ) : log a = c → a = ENNReal.ofReal (Real.exp c) :=
by
  intro h
  rw [←h, nn_comp_exp_log a ha ha2]
  exact Eq.symm (ofReal_toReal ha2)

variable [MeasurableSpace (Vector ℝ d)] (μ π ν : Measure (Vector ℝ d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure π] (dμ dπ : (Vector ℝ d) → ℝ≥0∞) (hμ : is_density μ ν dμ) (hπ : is_density π ν dπ) (mdμ : Measurable dμ) (mdπ : Measurable dπ) (hdμ : ∀x, dμ x ≠ 0 ∧ dμ x ≠ ∞) (hdπ : ∀x, dπ x ≠ 0 ∧ dπ x ≠ ∞) [MeasureSpace (Vector ℝ d)] [MeasureSpace ℝ]

variable (dπ' : ℕ → (Vector ℝ d) → ℝ) (d_log_π : ℕ → (Vector ℝ d) → ℝ) (hπ' : ∀x, ∀i, ENNReal.toReal (dπ x) * d_log_π i x = dπ' i x)

variable (d_log_μ_π : ℕ → (Vector ℝ d) → ℝ) (hd_log_μ_π : (∀x, ∀i, d_log_μ_π i x = 0) → (∃ c, ∀ x, log (dμ x / dπ x) = c))

variable (φ : ℕ → (Vector ℝ d) → ℝ) (dφ : ℕ → (Vector ℝ d) → ℝ)

/- The kernel function -/
variable (k : (Vector ℝ d) → (Vector ℝ d) → ℝ)

def positive_definite_kernel := ∀ (f : ℕ → Vector ℝ d → ℝ), (0 ≤ ∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), f i x * k x x' * f i x') ∂μ) ∂μ) ∧ (∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), f i x * k x x' * f i x') ∂μ) ∂μ = 0 ↔ ∀x, ∀i, f i x = 0)

variable (hk : positive_definite_kernel μ k)

def tends_to_infty {α : Type _} (f : α → ℝ) := ∀ c, ∃x, c < f x
variable [Norm (Vector ℝ d)]
/--
Unformal but highly pratical multivariate integration by parts
-/
lemma mv_integration_by_parts (f : Vector ℝ d → ℝ) (g grad_f dg : ℕ → (Vector ℝ d) → ℝ) (h : ∀ x, tends_to_infty (fun (x : Vector ℝ d) ↦ ‖x‖) → ∀i, f x * g i x = 0) : ∫ x in Set.univ, f x * (∑ i in range (d + 1), dg i x) ∂μ = - ∫ x in Set.univ, (∑ i in range (d + 1), grad_f i x * g i x) ∂μ := by sorry

def SteinClass (f : ℕ → (Vector ℝ d) → ℝ) (dμ : (Vector ℝ d) → ℝ≥0∞) := ∀ x, tends_to_infty (fun (x : Vector ℝ d) ↦ ‖x‖) → ∀i, ENNReal.toReal (dμ x) * f i x = 0

variable (is_integrable : ∀ (f : Vector ℝ d → ℝ), Integrable f μ)

/--
KSD(μ || π) = ⟪∇log μ/π, Pμ ∇log μ/π⟫_L²(μ). We assume here that KSD is also equal to ∫ x, ∑ l in range (d + 1), (d_log_π l x * φ l x + dφ l x) ∂μ
-/
lemma ksd : ∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), d_log_μ_π i x * k x x' * d_log_μ_π i x') ∂μ) ∂μ = ∫ (x : Vector ℝ d), ∑ l in range (d + 1), (d_log_π l x * φ l x + dφ l x) ∂μ := by sorry

/--
We show that KSD is a valid discrepancy measure i.e. μ = π ↔ KSD(μ || π) = 0
-/
lemma KSD_is_valid_discrepancy (hstein : SteinClass φ dπ) : μ = π ↔ ∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), d_log_μ_π i x * k x x' * d_log_μ_π i x') ∂μ) ∂μ = 0 :=
by
  constructor
  {
    intro h

    rw [ksd μ d_log_π d_log_μ_π φ dφ k]

    have split_sum : ∀x, ∑ l in range (d + 1), (d_log_π l x * φ l x + dφ l x) = (∑ l in range (d + 1), d_log_π l x * φ l x) + (∑ l in range (d + 1), dφ l x) := fun x ↦ sum_add_distrib
    simp_rw [split_sum]

    have h1 : Integrable (fun x ↦ (∑ l in range (d + 1), d_log_π l x * φ l x)) μ := is_integrable _
    have h2 : Integrable (fun x ↦ (∑ l in range (d + 1), dφ l x)) μ := is_integrable _
    rw [integral_add (h1) h2]

    have int_univ : ∫ a, ∑ l in range (d + 1), d_log_π l a * φ l a ∂μ = ∫ a in Set.univ, ∑ l in range (d + 1), d_log_π l a * φ l a ∂μ := by simp
    rw [int_univ]

    rw [h]

    rw [density_integration π ν dπ hπ (fun x ↦ (∑ l in range (d + 1), d_log_π l x * φ l x)) Set.univ]

    have mul_dist : ∀x, ENNReal.toReal (dπ x) * (∑ l in range (d + 1), (fun l ↦ d_log_π l x * φ l x) l) = ∑ l in range (d + 1), (fun l ↦ d_log_π l x * φ l x) l * ENNReal.toReal (dπ x) := by {
      have mul_dist_sum : ∀ (a : ℝ), ∀ (f : ℕ → ℝ), (∑ i in range (d + 1), f i) * a = ∑ i in range (d + 1), f i * a := fun a f ↦ Finset.sum_mul
      intro x
      rw [mul_comm]
      exact mul_dist_sum (ENNReal.toReal (dπ x)) (fun l ↦ d_log_π l x * φ l x)
    }
    simp_rw [mul_dist]

    have mul_comm : ∀x, ∀i, d_log_π i x * φ i x * ENNReal.toReal (dπ x) = ENNReal.toReal (dπ x) * d_log_π i x * φ i x := fun x i ↦ (mul_rotate (ENNReal.toReal (dπ x)) (d_log_π i x) (φ i x)).symm
    simp_rw [mul_comm, hπ']

    have int_univ : ∫ a, ∑ l in range (d + 1), dφ l a ∂π = ∫ a in Set.univ, ∑ l in range (d + 1), dφ l a ∂π := by simp
    rw [int_univ]
    rw [density_integration π ν dπ hπ (fun x ↦ (∑ l in range (d + 1), dφ l x)) Set.univ]

    rw [mv_integration_by_parts ν (fun x ↦ ENNReal.toReal (dπ x)) φ dπ' dφ (hstein)]
    simp
  }
  {
    intro h

    have d_log_μ_π_eq_0 := (hk d_log_μ_π).right.mp h
    specialize hd_log_μ_π d_log_μ_π_eq_0

    rcases hd_log_μ_π with ⟨c, h⟩
    have dμ_propor : ∀x, dμ x = ENNReal.ofReal (Real.exp c) * dπ x := by {
      intro x
      specialize h x
      have frac_neq_zero : dμ x / dπ x ≠ 0 := by {
        have frac_pos : 0 < dμ x / dπ x := ENNReal.div_pos_iff.mpr ⟨(hdμ x).left, (hdπ x).right⟩
        exact zero_lt_iff.mp frac_pos
      }

      have frac_finite : dμ x / dπ x ≠ ∞ := by {
        by_contra h
        rw [div_eq_top] at h
        cases h with
          | inl hp => {
            rcases hp with ⟨hpl, hpr⟩
            exact (hdπ x).left hpr
          }
          | inr hq => {
            rcases hq with ⟨hql, hqr⟩
            exact (hdμ x).right hql
          }
      }

      have cancel_log_exp : dμ x / dπ x = ENNReal.ofReal (Real.exp c) := cancel_log_exp (dμ x / dπ x) frac_neq_zero frac_finite c h
      simp [←cancel_log_exp, ENNReal.div_eq_inv_mul, mul_right_comm (dπ x)⁻¹ (dμ x) (dπ x), ENNReal.inv_mul_cancel (hdπ x).left (hdπ x).right]
    }

    have exp_c_eq_one : ENNReal.ofReal (Real.exp c) = 1 := by {
      by_cases hc : ENNReal.ofReal (Real.exp c) = 1
      {assumption}
      {
        push_neg at hc
        have univ_eq_one_μ : ∫⁻ x in Set.univ, 1 ∂μ = 1 := by simp
        have univ_eq_one_π : ∫⁻ x in Set.univ, 1 ∂π = 1 := by simp
        simp_rw [hc, fun x ↦ one_mul (dπ x)] at dμ_propor

        rw [density_lintegration μ ν dμ hμ (fun x ↦ 1) Set.univ] at univ_eq_one_μ
        simp_rw [dμ_propor] at univ_eq_one_μ
        simp_rw [mul_one] at univ_eq_one_μ

        have t : ∫⁻ x in Set.univ, ENNReal.ofReal (Real.exp c) * dπ x ∂ν =  ENNReal.ofReal (Real.exp c) * ∫⁻ x in Set.univ, dπ x ∂ν := lintegral_const_mul (ENNReal.ofReal (Real.exp c)) (mdπ)

        rw [density_lintegration π ν dπ hπ (fun x ↦ 1) Set.univ] at univ_eq_one_π
        simp_rw [mul_one] at univ_eq_one_π
        rw [t, univ_eq_one_π, mul_one] at univ_eq_one_μ
        exfalso
        exact hc univ_eq_one_μ
      }
    }

    simp_rw [exp_c_eq_one, one_mul] at dμ_propor
    ext s _hs
    rw [←set_lintegral_one s, ←set_lintegral_one s]
    rw [density_lintegration μ ν dμ hμ, density_lintegration π ν dπ hπ]
    simp_rw [mul_one, dμ_propor]
  }