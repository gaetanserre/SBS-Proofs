import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner

import GOSVGDProofs.Utils
import GOSVGDProofs.RKHS
import GOSVGDProofs.PushForward
import GOSVGDProofs.SteepestDirection

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
Here, we prove that KSD(μ | π) is a valid discrepancy measure, i.e. KSD(μ | π) = 0 ↔ μ = π.
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
    have imp_lt :  (0 < KSD μ π) ∧ ((2 * KL μ dμ dπ) ≠ ∞) → 0 < ENNReal.ofReal (KSD μ π) / (2 * KL μ dμ dπ) := by simp
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
    /-
      μ ≠ π → KL(μ || π) ≠ 0
    -/
    have KL_neq_0 : KL μ dμ dπ ≠ 0 := Iff.mp zero_lt_iff (hkl_diff h)
    constructor
    {
      -- We show that KSD(μ | π) / (2 KL(μ || π) ≠ ∞ by showing that KSD(μ | π) ≠ ∞ and 2 (KL(μ || π))⁻¹ ≠ ∞ (as both are non-negative).
      have div_as_inv : ENNReal.ofReal (KSD μ π) / (2 * KL μ dμ dπ) = ENNReal.ofReal (KSD μ π) * (2 * KL μ dμ dπ)⁻¹ := rfl
      rw [div_as_inv]
      have enn_KSD_finite : ENNReal.ofReal (KSD μ π) ≠ ∞ := ofReal_ne_top

      /-
        We show that (KL(μ || π))⁻¹ ≠ ∞ as KL(μ || π) ≠ 0
      -/
      have inv_KL_finite : (2 * KL μ dμ dπ)⁻¹ ≠ ∞ := by {
        have neq_zero : 2 * KL μ dμ dπ ≠ 0 := by {simp; exact KL_neq_0}
        exact inv_ne_top.mpr neq_zero
      }

      exact mul_ne_top enn_KSD_finite inv_KL_finite
    }
    {
      /-
        We show that, under non-zero and finite conditions, a ≤ (1 / (2 * (b / (2 * a)))) * b (in fact, a = (1 / (2 * (b / (2 * a)))) * b).
      -/
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

example (a : ℝ) : 0 < a → 0 ≤ a := by exact?

/-
  We show the exponential convergence of SVGD i.e. it exists Λ : ℝ⁺* → ℝ⁺* such that, ∀ t > 0, KL(μ_t t || π) ≤ exp(-2Λ t) KL(μ_t 0 || π).

-/
theorem exponential_convergence_of_SVGD (hksd_t : ∀t, is_ksd (μ_t t) π k d_log_π ϕ dϕ (d_log_μ_t_π t) KSD) : ∃ (Λ : ℝ≥0 → ℝ), ∀ (t : ℝ≥0), 0 < t → (0 < Λ t) ∧ (KL (μ_t t) (dμ_t t) dπ ≤ KL (μ_t 0) (dμ_t 0) dπ * exp (-2 * Λ t)) :=
by
  -- We use *stein_log_sobolev* to extract a 0 < θ such that KL(μ_t t || π) ≤ 1 / (2 θ) * KSD(μ_t t | π), ∀ t.
  have stein_log_sobolev := fun t ↦ Stein_log_Sobolev (μ_t t) π ν (dμ_t t) dπ (hμ_t t) hπ mdπ (hdμ_t t) hdπ k (h_kernel_positive_t t) d_log_π ϕ dϕ (is_integrable_H₀_t t) (d_log_μ_t_π t) (hd_log_μ_t_π t) dπ' hπ' KSD (ksd_nn_t t) hstein (hkl_eq_t t) (hkl_diff_t t) (hksd_t t)

  -- Axiom of choive in type theory that gives a function θ : ℝ≥0 ↦ ℝ≥0∞ such that KL(μ_t t || π) ≤ 1 / (2 θ t) * KSD(μ_t t | π).
  choose θ stein_log_sobolev using stein_log_sobolev

  -- Let Λ : t ↦ ∫ s in Icc 0 t, θ s
  use (fun t ↦ ENNReal.toReal (∫ s in Icc 0 t, θ s))

  intros t pos_t
  constructor
  {
    -- We show that ∀ 0 < t, 0 < ∫ s in Icc 0 t, θ s by showing that 0 ≤ ∫ s in Icc 0 t, θ s and ∫ s in Icc 0 t, θ s ≠ 0.
    apply (lt_eq_le_and_neq _).mp
    constructor
    {simp}
    {
      -- We show that ∫ s in Icc 0 t, θ s is neither null nor infinite as it is a bounded integral of a stricly positive and finite function.
      have θ_nneg : ∀ s, 0 < θ s := fun s ↦ (stein_log_sobolev s).left

      have θ_finite : ∀ s, θ s ≠ ∞ := fun s ↦ (stein_log_sobolev s).right.left

      have int_ne_zero : ∫ s in Icc 0 t, θ s ≠ 0 := by {
        have pos_int := pos_integral θ t pos_t θ_nneg
        exact ne_of_gt pos_int
      }

      have int_finite := finite_integral θ t θ_finite

      exact ENNReal.toReal_ne_zero.mpr ⟨int_ne_zero, int_finite⟩
    }
  }
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
    
    -- Using the Stein log Sobolev inequality, we extract the fact that 0 < θ t and θ t ≠ ∞.
    specialize stein_log_sobolev t
    rcases stein_log_sobolev with ⟨pos_θ, finite_θ, stein_log_sobolev⟩
    
    -- We use the previous calculation along with the previously extracted proprieties on θ t.
    have compute_ineq := calculation (KL (μ_t t) (dμ_t t) dπ) (ENNReal.ofReal (KSD (μ_t t) π)) (θ t) (by simp) (ne_of_gt pos_θ) (finite_θ) stein_log_sobolev

    -- ENNReal.toReal (ENNReal.ofReal a) = a.
    rw [toReal_ofReal (ksd_nn_t t)] at compute_ineq

    -- As d_KL_t t ≤ -KSD (μ_t t | π) and -KSD (μ_t t | π) ≤ -2 (θ t) KL (μ_t t || π), then d_KL_t t ≤ -2 (θ t) KL (μ_t t || π).
    have dkl_ineq : d_KL_t t ≤ -2 * ENNReal.toReal (θ t) * ENNReal.toReal (KL (μ_t t) (dμ_t t) dπ) := ge_trans compute_ineq (dkl_ksd t)

    -- We finally can use the Gronwall's lemma with ψ := t ↦ -2 (θ t).
    specialize gronwall (fun t ↦ -2 * ENNReal.toReal (θ t)) t pos_t dkl_ineq
    
    -- We get -2 out of the integral.
    rw [integral_mul_left (-2) fun a => ENNReal.toReal (θ a)] at gronwall
    
    -- Trivial coercion when integration positive function.
    rwa [coe_integral] at gronwall
  }