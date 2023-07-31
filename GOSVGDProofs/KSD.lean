import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import GOSVGDProofs.PushForward

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open ENNReal NNReal MeasureTheory MeasureTheory.Measure

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 4000000

variable (α : Type _) [MeasurableSpace α] (μ π ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure π] (dμ dπ : α → ℝ≥0∞) (hμ : is_density μ ν dμ) (hπ : is_density π ν dπ) (mdμ : Measurable dμ) (mdπ : Measurable dπ)


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

example (hdμ : ∀x, dμ x ≠ 0 ∧ dμ x ≠ ∞) (hdπ : ∀x, dπ x ≠ 0 ∧ dπ x ≠ ∞) : (∃ c, ∀ x, log (dμ x / dπ x) = c) → μ = π :=
by
  intro h
  rcases h with ⟨c, h⟩
  have dμ_propor : ∀x, dμ x = ENNReal.ofReal (Real.exp c) * dπ x := by {
    intro x
    specialize h x
    have t : 0 < dμ x / dπ x := ENNReal.div_pos_iff.mpr ⟨(hdμ x).left, (hdπ x).right⟩
    have r : ∀ (x : ℝ≥0∞), 0 < x → x ≠ 0 := fun x h ↦ zero_lt_iff.mp h
    have rr : dμ x / dπ x ≠ ∞ := by {
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

    have cancel_log_exp : dμ x / dπ x = ENNReal.ofReal (Real.exp c) := cancel_log_exp (dμ x / dπ x) (r (dμ x / dπ x) t) rr c h
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

      rw [density_integration μ ν dμ hμ (fun x ↦ 1) Set.univ] at univ_eq_one_μ
      simp_rw [dμ_propor] at univ_eq_one_μ
      simp_rw [mul_one] at univ_eq_one_μ

      have t : ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (Real.exp c) * dπ x ∂ν =  ENNReal.ofReal (Real.exp c) * ∫⁻ (x : α) in Set.univ, dπ x ∂ν := lintegral_const_mul (ENNReal.ofReal (Real.exp c)) (mdπ)

      rw [density_integration π ν dπ hπ (fun x ↦ 1) Set.univ] at univ_eq_one_π
      simp_rw [mul_one] at univ_eq_one_π
      rw [t, univ_eq_one_π, mul_one] at univ_eq_one_μ
      exfalso
      exact hc univ_eq_one_μ
    }
  }

  simp_rw [exp_c_eq_one, one_mul] at dμ_propor
  ext s _hs
  rw [←set_lintegral_one s, ←set_lintegral_one s]
  rw [density_integration μ ν dμ hμ, density_integration π ν dπ hπ]
  simp_rw [mul_one, dμ_propor]