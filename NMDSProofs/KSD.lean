import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner

import NMDSProofs.Utils
import NMDSProofs.RKHS
import NMDSProofs.PushForward
import NMDSProofs.SteepestDirection

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace
open BigOperators Finset ENNReal NNReal MeasureTheory

set_option trace.Meta.Tactic.simp.rewrite true

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
variable (H₀ : Set ((Vector ℝ d) → ℝ)) [NormedAddCommGroup ((Vector ℝ d) → ℝ)] [InnerProductSpace ℝ ((Vector ℝ d) → ℝ)]

/- The kernel function -/
variable (k : (Vector ℝ d) → (Vector ℝ d) → ℝ) (h_k : (∀ (x : (Vector ℝ d)), k x ∈ H₀) ∧ (∀ (x : (Vector ℝ d)), (fun y ↦ k y x) ∈ H₀))

variable (h_kernel : is_kernel H₀ k) (h_kernel_positive : positive_definite_kernel μ k)

/- We define the product RKHS as a space of function on ℕ → (Vector ℝ d) to ℝ (vector-valued function in our Lean formalism). A function belongs to such a RKHS if f = (f_1, ..., f_d) and ∀ 1 ≤ i ≤ d, fᵢ ∈ H₀. -/
variable {H : Set (ℕ → (Vector ℝ d) → ℝ)} [NormedAddCommGroup (ℕ → (Vector ℝ d) → ℝ)] [InnerProductSpace ℝ (ℕ → (Vector ℝ d) → ℝ)]

/-===============================KERNEL STEIN DISCREPANCY===============================-/
/-
Here, we prove that KSD(μ | π) is a valid discrepancy measure, that the Stein log Sobolev inequality holds, and the exponential convergence of SVGD.
-/

/- dk : x ↦ i ↦ y ↦ ∂xⁱ k(x, y) -/
variable (dk : (Vector ℝ d) → ℕ → (Vector ℝ d) → ℝ)

/- d_log_π : i ↦ x ↦ ∂xⁱ log (μ(x) / π(x)) -/
variable (d_log_π : ℕ → (Vector ℝ d) → ℝ)

/- Definition of the steepest direction ϕ -/
variable (ϕ : ℕ → (Vector ℝ d) → ℝ) (hϕ : ϕ ∈ H) (dϕ : ℕ → (Vector ℝ d) → ℝ) 

variable (h_is_ϕ : is_phi μ k dk d_log_π ϕ)

/- We will use this assumption only when the function is trivially integrable (e.g. derivative of integrable functions). -/
variable (is_integrable_H₀ : ∀ (f : Vector ℝ d → ℝ), Integrable f μ)

/-
d_log_μ_π : i ↦ c ↦ ∂xⁱ log (μ(x) / π(x))
-/
variable (d_log_μ_π : ℕ → (Vector ℝ d) → ℝ)

/-
Simple derivative rule: if the derivative is 0 ∀x, then the function is constant.
-/
variable (hd_log_μ_π : (∀x, ∀i, d_log_μ_π i x = 0) → (∃ c, ∀ x, log (dμ x / dπ x) = c))

/-
dπ' : i ↦ c ↦ ∂xⁱ π(x)
-/
variable (dπ' : ℕ → (Vector ℝ d) → ℝ)

/-
Simple derivative rule: ∂xⁱ log (π(x)) * π(x) = ∂xⁱ π(x).
-/
variable (hπ' : ∀x, ∀i, ENNReal.toReal (dπ x) * d_log_π i x = dπ' i x)


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
KSD(μ | π) = ⟪∇log μ/π, Pμ ∇log μ/π⟫_L²(μ). We assume here that KSD is also equal to ∫ x, ∑ l in range (d + 1), (d_log_π l x * ϕ l x + dϕ l x) ∂μ.
-/
def is_ksd := KSD μ π = (∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), d_log_μ_π i x * k x x' * d_log_μ_π i x') ∂μ) ∂μ) ∧ (KSD μ π = ∫ x, ∑ l in range (d + 1), (d_log_π l x * ϕ l x + dϕ l x) ∂μ)

/-
  KSD(μ | π) is originally defined as ‖Sμ ∇log μ/π‖²_H, it is therefore non-negative.
-/
variable (ksd_nn : 0 ≤ KSD μ π)

/-
  ϕ is in the Stein class of π
-/
variable (hstein : SteinClass ϕ dπ)

/--
  We show that, if ϕ is in the Stein class of π, KSD is a valid discrepancy measure i.e. μ = π ↔ KSD(μ | π) = 0.
-/
lemma KSD_is_valid_discrepancy (hksd : is_ksd μ π k d_log_π ϕ dϕ d_log_μ_π KSD) : μ = π ↔ KSD μ π = 0 :=
by
  constructor
  {
    -- μ = π ↦ KSD(μ | π) = 0.
    intro h

    rw [hksd.right]

    -- ∑ i, f i + g i = ∑ i, f i + ∑ i, g i.
    have split_sum : ∀x, ∑ l in range (d + 1), (d_log_π l x * ϕ l x + dϕ l x) = (∑ l in range (d + 1), d_log_π l x * ϕ l x) + (∑ l in range (d + 1), dϕ l x) := fun x ↦ sum_add_distrib
    simp_rw [split_sum]

    -- Split the integral of sum into sum of integral.
    have h1 : Integrable (fun x ↦ (∑ l in range (d + 1), d_log_π l x * ϕ l x)) μ := is_integrable_H₀ _
    have h2 : Integrable (fun x ↦ (∑ l in range (d + 1), dϕ l x)) μ := is_integrable_H₀ _
    rw [integral_add (h1) h2]

    -- Make the `Set.univ` appears for using the density later.
    have int_univ : ∫ a, ∑ l in range (d + 1), d_log_π l a * ϕ l a ∂μ = ∫ a in Set.univ, ∑ l in range (d + 1), d_log_π l a * ϕ l a ∂μ := by simp
    rw [int_univ]

    -- Replace μ by π in the integration.
    rw [h]

    -- Replace by its density.
    rw [density_integration π ν dπ hπ (fun x ↦ (∑ l in range (d + 1), d_log_π l x * ϕ l x)) Set.univ]

    -- Get ENNReal.toReal (dπ x) in the sum (a * ∑ b = ∑ b * a).
    have mul_dist : ∀x, ENNReal.toReal (dπ x) * (∑ l in range (d + 1), (fun l ↦ d_log_π l x * ϕ l x) l) = ∑ l in range (d + 1), (fun l ↦ d_log_π l x * ϕ l x) l * ENNReal.toReal (dπ x) := by {
      have mul_dist_sum : ∀ (a : ℝ), ∀ (f : ℕ → ℝ), (∑ i in range (d + 1), f i) * a = ∑ i in range (d + 1), f i * a := fun a f ↦ Finset.sum_mul
      intro x
      rw [mul_comm]
      exact mul_dist_sum (ENNReal.toReal (dπ x)) (fun l ↦ d_log_π l x * ϕ l x)
    }
    simp_rw [mul_dist]

    -- Make the product ENNReal.toReal (dπ x) * d_log_π i x appears to use the log derivative rule.
    have mul_comm : ∀x, ∀i, d_log_π i x * ϕ i x * ENNReal.toReal (dπ x) = ENNReal.toReal (dπ x) * d_log_π i x * ϕ i x := fun x i ↦ (mul_rotate (ENNReal.toReal (dπ x)) (d_log_π i x) (ϕ i x)).symm
    simp_rw [mul_comm, hπ']

    -- Make the `Set.univ` appears to use the density.
    have int_univ : ∫ a, ∑ l in range (d + 1), dϕ l a ∂π = ∫ a in Set.univ, ∑ l in range (d + 1), dϕ l a ∂π := by simp
    rw [int_univ]
    rw [density_integration π ν dπ hπ (fun x ↦ (∑ l in range (d + 1), dϕ l x)) Set.univ]

    -- Use the integration by parts on the right-hand side integral.
    rw [mv_integration_by_parts (fun x ↦ ENNReal.toReal (dπ x)) ϕ dπ' dϕ (hstein)]
    simp
  }
  {
    -- KSD(μ | π) = 0 ↦ μ = π.
    intro h
    rw [hksd.left] at h

    -- We use the fact that the kernel is positive-definite that implies that d_log_μ_π = 0.
    have d_log_μ_π_eq_0 := (h_kernel_positive d_log_μ_π).right.mp h

    -- Simple derivative rule: ∂x f x = 0 → f x = c
    specialize hd_log_μ_π d_log_μ_π_eq_0

    rcases hd_log_μ_π with ⟨c, h⟩
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

      have cancel_log_exp : dμ x / dπ x = ENNReal.ofReal (Real.exp c) := cancel_log_exp (dμ x / dπ x) frac_neq_zero frac_finite c h
      simp [←cancel_log_exp, ENNReal.div_eq_inv_mul, mul_right_comm (dπ x)⁻¹ (dμ x) (dπ x), ENNReal.inv_mul_cancel (hdπ x).left (hdπ x).right]
    }

    -- We show by cases that ENNReal.ofReal (Real.exp c) = 1. If it is ≠ 1, this implies a contradiction as dμ x = ENNReal.ofReal (Real.exp c) * dπ x and ∫⁻ x, dμ x ∂ν = 1.
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

/-
  Basic proprieties of KL.
-/
variable (hkl_eq : μ = π → KL μ dμ dπ = 0) (hkl_diff : μ ≠ π → 0 < KL μ dμ dπ)

/--
  We show that μ ≠ π → 0 < KSD μ π (trivial using *KSD_is_valid_discrepancy*).
-/
lemma μ_neq_π_imp_ksd_nn (hksd : is_ksd μ π k d_log_π ϕ dϕ d_log_μ_π KSD) : μ ≠ π → 0 < KSD μ π :=
by
  intro h
  by_contra h2
  push_neg at h2
  have split_le := LE.le.lt_or_eq h2
  cases split_le with
    |inl lt => { linarith }
    |inr eq => {
      have μ_eq_π := (KSD_is_valid_discrepancy μ π ν dμ dπ hμ hπ mdπ hdμ hdπ k h_kernel_positive d_log_π ϕ dϕ is_integrable_H₀ d_log_μ_π hd_log_μ_π dπ' hπ' KSD hstein hksd).mpr eq

      exact h μ_eq_π
    }

/--
  We show that it exists a finite and positive θ such that KL(μ || π) ≤ (1 / (2θ)) * KSD(μ | π)
-/
theorem Stein_log_Sobolev (hksd : is_ksd μ π k d_log_π ϕ dϕ d_log_μ_π KSD) : ∃ θ > 0, (θ ≠ ∞) ∧ (KL μ dμ dπ ≤ (1 / (2*θ)) * ENNReal.ofReal (KSD μ π)) :=
by
by_cases μ = π
{
  -- μ = π → KSD μ π = 0
  rw [(KSD_is_valid_discrepancy μ π ν dμ dπ hμ hπ mdπ hdμ hdπ k h_kernel_positive d_log_π ϕ dϕ is_integrable_H₀ d_log_μ_π hd_log_μ_π dπ' hπ' KSD hstein hksd).mp h]

  -- μ = π → KL μ π = 0
  rw [hkl_eq h]

  -- Use any θ > 0 ∧ θ ≠ ∞
  use 1
  constructor
  {simp}
  simp
}
{
  -- μ ≠ π
  push_neg at h
  -- Let θ = KSD(μ | π) / (2 KL(μ || π)
  use ENNReal.ofReal (KSD μ π) / (2 * KL μ dμ dπ)
  constructor
  {
    -- We show that 0 < KSD(μ | π) / (2 KL(μ || π) by showing that 0 < KSD(μ | π) and 2 KL(μ || π) ≠ ∞ (as both are non-negative).
    have imp_lt : (0 < KSD μ π) ∧ ((2 * KL μ dμ dπ) ≠ ∞) → 0 < ENNReal.ofReal (KSD μ π) / (2 * KL μ dμ dπ) := by simp
    apply imp_lt

    constructor
    {
      -- We use *μ_neq_π_imp_ksd_nn* as μ ≠ π.
      exact μ_neq_π_imp_ksd_nn μ π ν dμ dπ hμ hπ mdπ hdμ hdπ k h_kernel_positive d_log_π ϕ dϕ is_integrable_H₀ d_log_μ_π hd_log_μ_π dπ' hπ' KSD ksd_nn hstein hksd h
    }
    {
      -- KL is finite (in our framework, as μ << π << ν).
      exact mul_ne_top (by simp) (ofReal_ne_top)
    }
  }

  {
    -- μ ≠ π → KL(μ || π) ≠ 0
    have KL_neq_0 : KL μ dμ dπ ≠ 0 := Iff.mp zero_lt_iff (hkl_diff h)
    constructor
    {
      -- We show that KSD(μ | π) / (2 KL(μ || π) ≠ ∞ by showing that KSD(μ | π) ≠ ∞ and 2 (KL(μ || π))⁻¹ ≠ ∞ (as both are non-negative).
      have div_as_inv : ENNReal.ofReal (KSD μ π) / (2 * KL μ dμ dπ) = ENNReal.ofReal (KSD μ π) * (2 * KL μ dμ dπ)⁻¹ := rfl
      rw [div_as_inv]
      have enn_KSD_finite : ENNReal.ofReal (KSD μ π) ≠ ∞ := ofReal_ne_top

      -- We show that (KL(μ || π))⁻¹ ≠ ∞ as KL(μ || π) ≠ 0
      have inv_KL_finite : (2 * KL μ dμ dπ)⁻¹ ≠ ∞ := by {
        have neq_zero : 2 * KL μ dμ dπ ≠ 0 := by {simp; exact KL_neq_0}
        exact inv_ne_top.mpr neq_zero
      }

      exact mul_ne_top enn_KSD_finite inv_KL_finite
    }
    {
      -- We show that, under non-zero and finite conditions, a ≤ (1 / (2 * (b / (2 * a)))) * b (in fact, a = (1 / (2 * (b / (2 * a)))) * b).
      have calculation : ∀ (a b : ℝ≥0∞), a ≠ 0 → a ≠ ∞ → b ≠ 0 → b ≠ ∞ → a ≤ (1 / (2 * (b / (2 * a)))) * b := by {
        intros a b h0a hta h0b htb

        have simpl : 1 / (2 * (b / (2 * a))) = (2 * (b / (2 * a)))⁻¹ := by simp
        rw [simpl]

        have eq : (2 * (b / (2 * a)))⁻¹ * b = a := by {
          calc (2 * (b / (2 * a)))⁻¹ * b = (2 * (b / (2 * a)))⁻¹ * b := by ring
              _ = (2 * (b * (2 * a)⁻¹))⁻¹ * b := by exact rfl
              _ = (2 * b * (2 * a)⁻¹)⁻¹ * b := by ring
              _ = (2 * 2⁻¹ * a⁻¹ * b)⁻¹ * b := by {
                rw [ENNReal.mul_inv (by simp) (Or.inr h0a)]
                ring
              }

              _ = (a⁻¹ * b)⁻¹ * b := by {
                rw [ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
              }

              _ = a * b⁻¹ * b := by {
                have t : a⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hta
                rw [ENNReal.mul_inv (Or.inl t) (Or.inr h0b)]
                simp
              }

              _ = a * (b⁻¹ * b) := by ring

              _ = a := by {
                rw [ENNReal.inv_mul_cancel (h0b) (htb), mul_one]
              }
        }

        rw [eq]
      }

      -- As μ ≠ π, 0 < KSD(μ | π) and thus, KSD(μ | π) ≠ 0.
      have enn_KSD_neq_0 : ENNReal.ofReal (KSD μ π) ≠ 0 := by {
        have KSD_ge_0 := μ_neq_π_imp_ksd_nn μ π ν dμ dπ hμ hπ mdπ hdμ hdπ k h_kernel_positive d_log_π ϕ dϕ is_integrable_H₀ d_log_μ_π hd_log_μ_π dπ' hπ' KSD ksd_nn hstein hksd h

        have enn_KSD_ge_0 := Iff.mpr ofReal_pos KSD_ge_0

        exact Iff.mp zero_lt_iff enn_KSD_ge_0
      }

      -- Use the previous calculation with a := KL(μ || π), b := KSD(μ | π).
      exact calculation (KL μ dμ dπ) (ENNReal.ofReal (KSD μ π)) (KL_neq_0) (ofReal_ne_top) (enn_KSD_neq_0) (ofReal_ne_top)
    }
  }
}

/-
  In this sub-section, we define the flow of measures μ_t:
  μ_t : ℝ≥0 → Measure (Vector ℝ d)
        t ↦ T_t#μ, where T_t is the trajectories associated with ϕ(μ_t t), the steepest direction to update μ_t t for minimizing ∂t KL(μ_t t || π).
  We also define everything that we need to use previous results with each measures given by μ_t. 
-/
variable (μ_t : ℝ≥0 → Measure (Vector ℝ d)) (dμ_t : ℝ≥0 → (Vector ℝ d → ℝ≥0∞)) (hμ_t : ∀ t, is_density (μ_t t) ν (dμ_t t)) (h_prob : ∀ t, IsProbabilityMeasure (μ_t t))
variable (hdμ_t :∀t, ∀ (x : Vector ℝ d), dμ_t t x ≠ 0 ∧ dμ_t t x ≠ ⊤)

/-
  d_KL_t : t ↦ ∂t KL(μ_t t || π)
-/
variable (d_KL_t : ℝ≥0 → ℝ)
variable (d_log_μ_t_π : ℝ≥0 → ℕ → (Vector ℝ d) → ℝ)
variable (hd_log_μ_t_π : ∀t, (∀x, ∀i, d_log_μ_t_π t i x = 0) → (∃ c, ∀ x, log (dμ_t t x / dπ x) = c))
variable (hkl_eq_t : ∀t, μ_t t = π → KL (μ_t t) (dμ_t t) dπ = 0) (hkl_diff_t : ∀t, μ_t t ≠ π → 0 < KL (μ_t t) (dμ_t t) dπ)

variable (h_kernel_positive_t : ∀t, positive_definite_kernel (μ_t t) k)
variable (is_integrable_H₀_t : ∀t, ∀ (f : Vector ℝ d → ℝ), Integrable f (μ_t t))
variable (ksd_nn_t : ∀t, 0 ≤ KSD (μ_t t) π)

/-
  Our definition of the Gronwall's lemma.
-/
variable [MeasureSpace ℝ≥0] [NormedAddCommGroup ℝ≥0∞] [NormedSpace ℝ ℝ≥0∞] [LocallyFiniteOrder ℝ≥0]
variable (gronwall : ∀ (ψ : ℝ≥0 → ℝ), ∀ t > 0, d_KL_t t ≤ ψ t * ENNReal.toReal (KL (μ_t t) (dμ_t t) dπ) → KL (μ_t t) (dμ_t t) dπ ≤ KL (μ_t 0) (dμ_t 0) dπ * exp (∫ s in Icc 0 t, ψ s))

/-
  We assume here that ∂t KL(μ_t t || π) = - KSD(μ_t t | π) (showed in the paper).
-/
variable (dkl_ksd : ∀t, d_KL_t t ≤ - KSD (μ_t t) π)

/-
  As showed in the paper (and reminded above), t ↦ KL(μ_t t || π) is decreasing.
-/
variable (kl_decreasing : ∀t, ∀t', t < t' → KL (μ_t t') (dμ_t t') dπ ≤ KL (μ_t t) (dμ_t t) dπ) (kl_finite : ∀t, KL (μ_t t) (dμ_t t) dπ ≠ ∞)

/--
If t ↦ KL(μ_t t || π) is bounded from below by a strictly positive constant, it means that μ_t cannot be made arbitrary close to π and thus that t ↦ KSD(μ_t | π) can be bounded by a striclty positive constant. Admitted here; we plan on formally show it in the future.
-/
lemma KL_bounded_imp_bounded_KSD (α : ℝ≥0∞) (hα : 0 < α) (hkl : ∀t, α < KL (μ_t t) (dμ_t t) dπ) : ∃ (β : ℝ≥0∞), (∀t, β < ENNReal.ofReal (KSD (μ_t t) π)) ∧ (0 < β) ∧ (β ≠ ∞) := by sorry

/--
Squeeze theorem: ∀t, 0 ≤ KL(μ_t t || π) ≤ f(t) ∧ lim_(t → ∞) f(t) = 0 → lim_(t → ∞) KL(μ_t t || π) = 0.
-/
lemma squeeze_th_KL (f : ℝ≥0 → ℝ≥0∞) (h : limit f 0) : (∀t>0, KL (μ_t t) (dμ_t t) dπ ≤ f t) → limit (fun t ↦ KL (μ_t t) (dμ_t t) dπ) 0 := by sorry

/--
  We show the convergence of SVGD i.e. lim_(t → ∞) KL (μ_t || π) = 0.
-/
theorem convergence_SVGD (log_sobolev : ∀t, KL (μ_t t) (dμ_t t) dπ ≤ (1/(2 * (ENNReal.ofReal (KSD (μ_t t) π) / (2 * (KL (μ_t t) (dμ_t t) dπ)) ) )) * ENNReal.ofReal (KSD (μ_t t) π) ) : limit (fun t ↦ KL (μ_t t) (dμ_t t) dπ) 0 :=
by

  -- As t ↦ KL (μ_t || π) is decreasing and bound from below, it admits a limit l ≥ 0.
  have admits_limit := decreasing_bounded_function_limit (fun t ↦ KL (μ_t t) (dμ_t t) dπ) 0 (by simp) kl_decreasing
  rcases admits_limit with ⟨l, lim, _lim_pos, KL_bounded⟩

  -- We proceed by cases on the value of l. If l = 0, the proof is finished. Otherwise, we proceed by contradiction by showing that l ≠ 0 → l = 0.  
  by_cases hl : 0 = l
  {
    rwa [hl]
  }
  {
    exfalso
    push_neg at hl
    have lim_nn : 0 < l := Iff.mpr zero_lt_iff (Ne.symm hl)

    -- We use the *KL_bounded_imp_bounded_KSD* to extract 0 < γ < KSD(μ_t | π)
    have KSD_bounded := KL_bounded_imp_bounded_KSD π dπ KSD μ_t dμ_t l lim_nn KL_bounded
    rcases KSD_bounded with ⟨γ, KSD_bounded, γ_nn, γ_finite⟩

    -- We prove that γ/2KL(μ_0 || π) < KSD(μ_t | π) / 2KL(μ_t | π) (we plan on using it with the Stein log-Sobolev inequality).
    have gamma_star := decrease_bound (fun t ↦ KL (μ_t t) (dμ_t t) dπ) (fun t ↦ ENNReal.ofReal (KSD (μ_t t) π)) kl_decreasing (fun x ↦ Iff.mp zero_lt_iff (gt_trans (KL_bounded x) lim_nn)) kl_finite γ KSD_bounded

    -- γ/2KL(μ_0 || π) ≠ 0
    have gamma_star_neq : γ / (2 * KL (μ_t 0) (dμ_t 0) dπ) ≠ 0 := by {
        have two_KL_finite : (2 * KL (μ_t 0) (dμ_t 0) dπ) ≠ ∞ := by {
          rw [two_mul]
          exact add_ne_top.mpr ⟨kl_finite 0, kl_finite 0⟩
        }
        have inv_two_KL_neq : (2 * KL (μ_t 0) (dμ_t 0) dπ)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr two_KL_finite

        have γ_neq : γ ≠ 0 := Iff.mp zero_lt_iff γ_nn 


        rw [ENNReal.div_eq_inv_mul]
        exact mul_ne_zero inv_two_KL_neq γ_neq
    }

    -- γ/2KL(μ_0 || π) ≠ ∞
    have gamma_star_finite : γ / (2 * KL (μ_t 0) (dμ_t 0) dπ) ≠ ∞ := by {
        rw [ENNReal.div_eq_inv_mul]
        have KL_finite : (2 * KL (μ_t 0) (dμ_t 0) dπ)⁻¹ ≠ ∞ := by {
          have tmp : (2 * KL (μ_t 0) (dμ_t 0) dπ) ≠ 0 := by {
            rw [two_mul]
            simp
            exact Iff.mp zero_lt_iff (gt_trans (KL_bounded 0) lim_nn)
          }
          exact inv_ne_top.mpr tmp
        }
        exact mul_ne_top KL_finite γ_finite
      }

    -- Using the Stein log-Sobolev and the gamma_star inequality, we are able to show that, ∀t, KL(μ_t || π) < 1/(2*γ/2KL(μ_0 || π)) * KSD(μ_t | π).
    have bounded_log_sobolev : ∀t, KL (μ_t t) (dμ_t t) dπ < (1/(2 * (γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0)) )) * ENNReal.ofReal (KSD (μ_t t) π) := by
    {
      intro t
      specialize log_sobolev t
      specialize gamma_star t

      have le_quotient : ∀(a b : ℝ≥0∞), a ≠ 0 → a < b → 1/(2*b) < 1/(2*a) :=
      by
      {
        intro a b _ha h
        rw[one_div (2*a), one_div (2*b)]
        
        have h : 2*a < 2*b := by {
          repeat rw[two_mul]
          simp
          exact ENNReal.add_lt_add h h
        }

        exact Iff.mpr ENNReal.inv_lt_inv h
      }

      specialize le_quotient (γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0)) ((fun t => ENNReal.ofReal (KSD (μ_t t) π)) t / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) t)) gamma_star_neq gamma_star 

      have le_prod : ∀(a b c : ℝ≥0∞), c ≠ 0 → c ≠ ∞ → a < b → a * c < b * c :=
      by
      {
        intro a b c hc_nn hc_finite ha
        exact Iff.mpr (ENNReal.mul_lt_mul_right hc_nn hc_finite) ha
      }

      have enn_KSD_neq : ENNReal.ofReal (KSD (μ_t t) π) ≠ 0 := by {
        exact Iff.mp zero_lt_iff (gt_trans (KSD_bounded t) γ_nn)
      }
      have enn_KSD_finite : ENNReal.ofReal (KSD (μ_t t) π) ≠ ∞ := by simp

      specialize le_prod (1/(2*((fun t => ENNReal.ofReal (KSD (μ_t t) π)) t / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) t)))) (1/(2*(γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0)))) (ENNReal.ofReal (KSD (μ_t t) π)) enn_KSD_neq enn_KSD_finite le_quotient 

      calc KL (μ_t t) (dμ_t t) dπ ≤ 1 / (2 * (ENNReal.ofReal (KSD (μ_t t) π) / (2 * KL (μ_t t) (dμ_t t) dπ))) * ENNReal.ofReal (KSD (μ_t t) π) := log_sobolev
      _ <  1 / (2 * (γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0))) * ENNReal.ofReal (KSD (μ_t t) π) := le_prod
    }

    -- We use the previous inequality and the Gronwall's lemma to show that ∀t, KL(μ_t || π) ≤ KL (μ_0 || π) * exp(-2t γ/2KL(μ_0 || π)).
    have bound_gronwall : ∀t>0, (KL (μ_t t) (dμ_t t) dπ ≤ KL (μ_t 0) (dμ_t 0) dπ * exp (-2 * ENNReal.toReal (γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0)) * t)) := by 
    {
      -- We show that, under some non-zero and finite conditions, a ≤ (1 / (2 * c)) * b → - (b : ℝ) ≤ -2 * (c : ℝ) * (a : ℝ)
      have calculation : ∀ (a b c : ℝ≥0∞), b ≠ ∞ → c ≠ 0 → c ≠ ∞ → a ≤ (1 / (2 * c)) * b → - ENNReal.toReal b ≤ -2 * ENNReal.toReal c * ENNReal.toReal a := by {
        intros a b c htb h0c htc h
        have t : 1 / (2 * c) * b = (2 * c)⁻¹ * b := by simp
        rw [t] at h

        have finite : (2 * c) ≠ ∞ := ENNReal.mul_ne_top (by simp) (htc)
        have n_zero : (2 * c) ≠ 0 := mul_ne_zero (by simp) (h0c)
        have tt : a * (2 * c) ≤ (2 * c)⁻¹ * b * (2 * c) := by {
          exact (ENNReal.mul_le_mul_right n_zero finite).mpr h
        }

        have ttt : (2 * c)⁻¹ * b * (2 * c) = b * ((2 * c)⁻¹ * (2 * c)) := by ring
        have t : (2 * c)⁻¹ * (2 * c) = 1 := by exact ENNReal.inv_mul_cancel n_zero finite
        rw [ttt, t, mul_one] at tt
        have t : ENNReal.toReal (a * (2 * c)) ≤ ENNReal.toReal b := by {
          exact toReal_mono htb tt
        }
        have tt : ENNReal.toReal (a * (2 * c)) = ENNReal.toReal a * ENNReal.toReal (2 * c) := by simp
        rw [tt] at t
        have tt : ENNReal.toReal (2 * c) = ENNReal.toReal 2 * ENNReal.toReal c := by simp
        rw [tt] at t
        have tt : ENNReal.toReal a * (ENNReal.toReal 2 * ENNReal.toReal c) = ENNReal.toReal a * ENNReal.toReal 2 * ENNReal.toReal c := by ring
        rw [tt] at t
        have tt := neg_le_neg t
        have t : -(ENNReal.toReal a * ENNReal.toReal 2 * ENNReal.toReal c) = - ENNReal.toReal 2 * ENNReal.toReal c * ENNReal.toReal a := by ring
        rw [t] at tt
        exact tt
      }

      intro t pos_t

      -- This calculation allows us to transform the inequality KL(μ_t || π) < 1/(2*γ/2KL(μ_0 || π)) * KSD(μ_t | π) into -KSD(μ_t | π) ≤ -2 * γ/2KL(μ_0 || π) * KL(μ_t || π)
      have compute_ineq := calculation (KL (μ_t t) (dμ_t t) dπ) (ENNReal.ofReal (KSD (μ_t t) π)) ((γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0))) (by simp) gamma_star_neq gamma_star_finite (le_of_lt (bounded_log_sobolev t))

      rw [toReal_ofReal (ksd_nn_t t)] at compute_ineq

      -- As d_KL_t t ≤ -KSD (μ_t t | π) and -KSD (μ_t t | π) ≤ -2 * γ/2KL(μ_0 || π) * KL(μ_t t || π), then d_KL_t t ≤ -2 * γ/2KL(μ_0 || π) * KL(μ_t t || π).
      have dkl_ineq : d_KL_t t ≤ -2 * ENNReal.toReal ((γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0))) * ENNReal.toReal (KL (μ_t t) (dμ_t t) dπ) := ge_trans compute_ineq (dkl_ksd t)

      -- We finally can use the Gronwall's lemma with ψ := t ↦ -2 * γ/2KL(μ_0 || π).
      specialize gronwall (fun t ↦ -2 * ENNReal.toReal ((γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0)))) t pos_t dkl_ineq

      -- We rewrite ∫ s ∈ [0, t], -2 * γ/2KL(μ_0 || π) dt as -2t γ/2KL(μ_0 || π).
      rwa [integral_of_constant] at gronwall
    }

    have minus_gamma_star_neg : -2 * ENNReal.toReal (γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0)) < 0 := by {
      have gamma_star_nn : 0 < (γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0)) := Iff.mpr zero_lt_iff gamma_star_neq
      simp
      exact toReal_pos_iff.mpr ⟨gamma_star_nn, Ne.lt_top gamma_star_finite⟩
    }

    -- As -2 γ/2KL(μ_0 || π) < 0, lim_(t → ∞) exp(-2 γ/2KL(μ_0 || π) t) = 0.
    have exp_limit := exp_tends_to_zero (-2 * ENNReal.toReal ((γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0)))) (KL (μ_t 0) (dμ_t 0) dπ) minus_gamma_star_neg

    -- Using the squeeze theorem and the previous result, we prove that lim_(t → ∞) KL(μ_0 || π) t) = 0.
    have contradiction_limit := squeeze_th_KL dπ μ_t dμ_t (fun t ↦ KL (μ_t 0) (dμ_t 0) dπ * exp (-2 * ENNReal.toReal (γ / (2 * (fun t => KL (μ_t t) (dμ_t t) dπ) 0)) * t)) exp_limit bound_gronwall

    -- The last result implies that l = 0 which is a contradiction as we supposed l ≠ 0.
    have lim_eq_zero := limit_equiv (fun t => KL (μ_t t) (dμ_t t) dπ) l 0 ⟨lim, contradiction_limit⟩

    exact hl.symm lim_eq_zero
    
  }