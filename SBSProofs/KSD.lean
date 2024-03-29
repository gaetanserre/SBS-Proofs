/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner

import SBSProofs.Utils
import SBSProofs.PushForward
import SBSProofs.SteepestDirection

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace
open BigOperators Finset ENNReal NNReal MeasureTheory

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 400000

/-
  We defined measures μ and π (ν is considered as the standard Lebesgue measure) along with their densities (finite and non-zero on the entire space)
-/
variable {d : ℕ}

variable [MeasurableSpace (Vector ℝ d)] [MeasureSpace (Vector ℝ d)] [MeasureSpace ℝ]

variable (μ π ν : Measure (Vector ℝ d)) (dμ dπ : (Vector ℝ d) → ℝ≥0∞)

/-
  μ << π << ν, they both admit density w.r.t. ν.
-/
variable (_h1 : absolutely_continuous μ π) (_h2 : absolutely_continuous π ν)
example : absolutely_continuous μ ν := absolutely_continuous_trans _h1 _h2

variable (hμ : is_density μ ν dμ) (hπ : is_density π ν dπ) (mdμ : Measurable dμ) (mdπ : Measurable dπ) (hdμ : ∀x, dμ x ≠ 0 ∧ dμ x ≠ ∞) (hdπ : ∀x, dπ x ≠ 0 ∧ dπ x ≠ ∞)


variable [IsProbabilityMeasure μ] [IsProbabilityMeasure π]

variable (h_m_set : ∀ (s : Set (Vector ℝ d)), MeasurableSet s)

/-
  We define a RKHS of ((Vector ℝ d) → ℝ) functions.
-/
variable (H₀ : Set ((Vector ℝ d) → ℝ)) [NormedAddCommGroup ((Vector ℝ d) → ℝ)] [InnerProductSpace ℝ ((Vector ℝ d) → ℝ)] [s : RKHS H₀]

def positive_definite_kernel := ∀ (f : ℕ → Vector ℝ d → ℝ), (0 ≤ ∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), f i x * s.k x x' * f i x') ∂μ) ∂μ) ∧ (∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), f i x * s.k x x' * f i x') ∂μ) ∂μ = 0 ↔ ∀x, ∀i, f i x = 0)

variable (h_kernel_positive : positive_definite_kernel μ H₀)

/- We define the product RKHS as a space of function on ℕ → (Vector ℝ d) to ℝ (vector-valued function in our Lean formalism). A function belongs to such a RKHS if f = (f_1, ..., f_d) and ∀ 1 ≤ i ≤ d, fᵢ ∈ H₀. -/
variable (H : Set (ℕ → (Vector ℝ d) → ℝ)) [NormedAddCommGroup (ℕ → (Vector ℝ d) → ℝ)] [InnerProductSpace ℝ (ℕ → (Vector ℝ d) → ℝ)]

/-===============================KERNEL STEIN DISCREPANCY===============================-/
/-
Here, we prove that KSD(μ | π) is a valid discrepancy measure and that π is the only fixed point of Φₜ(μ).
-/

/- dk : x ↦ i ↦ y ↦ ∂xⁱ k(x, y) -/
variable (dk : (Vector ℝ d) → ℕ → (Vector ℝ d) → ℝ)

/- d_ln_π : i ↦ x ↦ ∂xⁱ ln (μ(x) / π(x)) -/
variable (d_ln_π : ℕ → (Vector ℝ d) → ℝ)

/-
  Definition of the steepest direction ϕ
-/
variable (dϕ : ℕ → (Vector ℝ d) → ℝ)

/- We will use this assumption only when the function is trivially integrable (e.g. derivative of integrable functions). -/
variable (is_integrable_H₀ : ∀ (f : Vector ℝ d → ℝ), Integrable f μ)


/-
d_ln_π_μ : i ↦ x ↦ ∂xⁱ ln (π(x) / μ(x))
-/
variable (d_ln_π_μ : ℕ → (Vector ℝ d) → ℝ)

/-
Simple derivative rule: if the derivative is 0 ∀x, then the function is constant.
-/
variable (hd_ln_π_μ : (∀x, ∀i, d_ln_π_μ i x = 0) → (∃ c, ∀ x, log (dμ x / dπ x) = c))

/-
dπ' : i ↦ x ↦ ∂xⁱ π(x)
-/
variable (dπ' : ℕ → (Vector ℝ d) → ℝ)

/-
Simple derivative rule: ∂xⁱ ln (π(x)) * π(x) = ∂xⁱ π(x).
-/
variable (hπ' : ∀x, ∀i, ENNReal.toReal (dπ x) * d_ln_π i x = dπ' i x)


variable [Norm (Vector ℝ d)]
/--
  Stein class of measure. f is in the Stein class of μ if, ∀i ∈ range (d + 1), lim_(‖x‖ → ∞) μ(x) * ϕ(x)ⁱ = 0.
-/
def SteinClass (f : ℕ → (Vector ℝ d) → ℝ) (dμ : (Vector ℝ d) → ℝ≥0∞) := ∀ x, tends_to_infty (fun (x : Vector ℝ d) ↦ ‖x‖) → ∀i, ENNReal.toReal (dμ x) * f i x = 0


/-
  Kernel Stein Discrepancy
-/
variable (KSD : Measure (Vector ℝ d) → Measure (Vector ℝ d) → ℝ)

/--
KSD(μ | π) = ⟪∇ln π/μ, Pμ ∇ln π/μ⟫_L²(μ). We assume here that KSD is also equal to ∫ x, ∑ l in range (d + 1), (d_ln_π l x * ϕ l x + dϕ l x) ∂μ.
-/
def is_ksd := KSD μ π = (∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), d_ln_π_μ i x * s.k x x' * d_ln_π_μ i x') ∂μ) ∂μ) ∧ (KSD μ π = ∫ x, ∑ l in range (d + 1), (d_ln_π l x * (ϕ_ μ H₀ dk d_ln_π) l x + dϕ l x) ∂μ)

/-
  KSD(μ | π) is originally defined as ‖ϕ^⋆‖²_H, it is therefore non-negative.
-/
def is_ksd_norm := KSD μ π = ‖ϕ_ μ H₀ dk d_ln_π‖
variable (ksd_nn : 0 ≤ KSD μ π)

/-
  ϕ is in the Stein class of π
-/
variable (hstein : SteinClass (ϕ_ μ H₀ dk d_ln_π) dπ)

/--
  We show that, if ϕ is in the Stein class of π, KSD is a valid discrepancy measure i.e. μ = π ↔ KSD(μ | π) = 0.
-/
lemma KSD_is_valid_discrepancy (hksd : is_ksd μ π H₀ dk d_ln_π dϕ d_ln_π_μ KSD) : μ = π ↔ KSD μ π = 0 :=
by
  let ϕ := (ϕ_ μ H₀ dk d_ln_π)
  constructor
  {
    -- μ = π ↦ KSD(μ | π) = 0.
    intro h

    rw [hksd.right]

    -- ∑ i, f i + g i = ∑ i, f i + ∑ i, g i.
    have split_sum : ∀x, ∑ l in range (d + 1), (d_ln_π l x * ϕ l x + dϕ l x) = (∑ l in range (d + 1), d_ln_π l x * ϕ l x) + (∑ l in range (d + 1), dϕ l x) := fun x ↦ sum_add_distrib
    simp_rw [split_sum]

    -- Split the integral of sum into sum of integral.
    have h1 : Integrable (fun x ↦ (∑ l in range (d + 1), d_ln_π l x * ϕ l x)) μ := is_integrable_H₀ _
    have h2 : Integrable (fun x ↦ (∑ l in range (d + 1), dϕ l x)) μ := is_integrable_H₀ _
    rw [integral_add (h1) h2]

    -- Make the `Set.univ` appears for using the density later.
    have int_univ : ∫ a, ∑ l in range (d + 1), d_ln_π l a * ϕ l a ∂μ = ∫ a in Set.univ, ∑ l in range (d + 1), d_ln_π l a * ϕ l a ∂μ := by simp
    rw [int_univ]

    -- Replace μ by π in the integration.
    rw [h]

    -- Replace by its density.
    rw [density_integration π ν dπ hπ (fun x ↦ (∑ l in range (d + 1), d_ln_π l x * ϕ l x)) Set.univ]

    -- Get ENNReal.toReal (dπ x) in the sum (a * ∑ b = ∑ b * a).
    have mul_dist : ∀x, ENNReal.toReal (dπ x) * (∑ l in range (d + 1), (fun l ↦ d_ln_π l x * ϕ l x) l) = ∑ l in range (d + 1), (fun l ↦ d_ln_π l x * ϕ l x) l * ENNReal.toReal (dπ x) := by {
      have mul_dist_sum : ∀ (a : ℝ), ∀ (f : ℕ → ℝ), (∑ i in range (d + 1), f i) * a = ∑ i in range (d + 1), f i * a := λ a f ↦ sum_mul (range (d + 1)) (fun i ↦ f i) a
      intro x
      rw [mul_comm]
      exact mul_dist_sum (ENNReal.toReal (dπ x)) (fun l ↦ d_ln_π l x * ϕ l x)
    }
    simp_rw [mul_dist]

    -- Make the product ENNReal.toReal (dπ x) * d_ln_π i x appears to use the ln derivative rule.
    have mul_comm : ∀x, ∀i, d_ln_π i x * ϕ i x * ENNReal.toReal (dπ x) = ENNReal.toReal (dπ x) * d_ln_π i x * ϕ i x := fun x i ↦ (mul_rotate (ENNReal.toReal (dπ x)) (d_ln_π i x) (ϕ i x)).symm
    simp_rw [mul_comm, hπ']

    -- Make the `Set.univ` appears to use the density.
    have int_univ : ∫ a, ∑ l in range (d + 1), dϕ l a ∂π = ∫ a in Set.univ, ∑ l in range (d + 1), dϕ l a ∂π := by simp
    rw [int_univ]
    rw [density_integration π ν dπ hπ (fun x ↦ (∑ l in range (d + 1), dϕ l x)) Set.univ]

    -- Use the integration by parts on the right-hand side integral.
    rw [mv_integration_by_parts (Set.univ) (fun x ↦ ENNReal.toReal (dπ x)) ϕ dπ' dϕ (hstein)]
    simp
  }
  {
    -- KSD(μ | π) = 0 ↦ μ = π.
    intro h
    rw [hksd.left] at h

    -- We use the fact that the kernel is positive-definite that implies that d_ln_π_μ = 0.
    have d_ln_π_μ_eq_0 := (h_kernel_positive d_ln_π_μ).right.mp h

    -- Simple derivative rule: ∂x f x = 0 → f x = c
    specialize hd_ln_π_μ d_ln_π_μ_eq_0

    rcases hd_ln_π_μ with ⟨c, h⟩
    -- We show that, since dμ x / dπ x ≠ 0 and finite, dμ x = ENNReal.ofReal (Real.exp c) * dπ x.
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

      have cancel_ln_exp : dμ x / dπ x = ENNReal.ofReal (Real.exp c) := cancel_ln_exp (dμ x / dπ x) frac_neq_zero frac_finite c h
      simp [←cancel_ln_exp, ENNReal.div_eq_inv_mul, mul_right_comm (dπ x)⁻¹ (dμ x) (dπ x), ENNReal.inv_mul_cancel (hdπ x).left (hdπ x).right]
    }

    -- We show by cases that ENNReal.ofReal (Real.exp c) = 1. If it is ≠ 1, this implies a contradiction as dμ x = ENNReal.ofReal (Real.exp c) * dπ x and ∫⁻ x, dμ x ∂ν = 1.
    have exp_c_eq_one : ENNReal.ofReal (Real.exp c) = 1 := by {
      by_cases hc : ENNReal.ofReal (Real.exp c) = 1
      {assumption}
      {
        push_neg at hc
        have univ_eq_one_μ : ∫⁻ x in Set.univ, 1 ∂μ = 1 := by simp
        have univ_eq_one_π : ∫⁻ x in Set.univ, 1 ∂π = 1 := by simp

        rw [density_lintegration μ ν dμ hμ (fun x ↦ 1) Set.univ] at univ_eq_one_μ
        simp_rw [dμ_propor] at univ_eq_one_μ
        simp_rw [mul_one] at univ_eq_one_μ

        rw [density_lintegration π ν dπ hπ (fun x ↦ 1) Set.univ] at univ_eq_one_π
        simp_rw [mul_one] at univ_eq_one_π

        rw [lintegral_const_mul (ENNReal.ofReal (Real.exp c)) (mdπ), univ_eq_one_π, mul_one] at univ_eq_one_μ
        exfalso
        exact hc univ_eq_one_μ
      }
    }

    -- We rewrite μ = π as ∀s, ∫⁻ x in s, dμ ∂ν = ∀s, ∫⁻ x in s, dπ ∂ν and use dμ = 1 * dπ.
    simp_rw [exp_c_eq_one, one_mul] at dμ_propor
    ext s _hs
    rw [←set_lintegral_one s, ←set_lintegral_one s]
    rw [density_lintegration μ ν dμ hμ, density_lintegration π ν dπ hπ]
    simp_rw [mul_one, dμ_propor]
  }

/--
  π is the only fixed point of Φₜ(μ). We proved that by showing that, if μ = π, ϕ^* = 0 and ϕ^* ≠ 0 otherwise.
-/
lemma π_unique_fixed_point (hksd : is_ksd μ π H₀ dk d_ln_π dϕ d_ln_π_μ KSD) (ksd_norm : is_ksd_norm μ π H₀ dk d_ln_π KSD) : (μ = π → ϕ_ μ H₀ dk d_ln_π = 0) ∧ (μ ≠ π → ϕ_ μ H₀ dk d_ln_π ≠ 0) :=
by
  have KSD_discrepancy := KSD_is_valid_discrepancy μ π ν dμ dπ hμ hπ mdπ hdμ hdπ H₀ h_kernel_positive dk d_ln_π dϕ is_integrable_H₀ d_ln_π_μ hd_ln_π_μ dπ' hπ' KSD hstein hksd
  constructor
  {
    -- μ = π → ϕ^* = 0
    intro μ_eq_π
    rw [ksd_norm, norm_eq_zero_] at KSD_discrepancy
    exact KSD_discrepancy.mp μ_eq_π
  }
  {
    -- μ ≠ π → ϕ^* ≠ 0
    intro μ_neq_π
    by_contra h
    rw [←norm_eq_zero_, ← ksd_norm] at h
    exact μ_neq_π (KSD_discrepancy.mpr h)
  }
