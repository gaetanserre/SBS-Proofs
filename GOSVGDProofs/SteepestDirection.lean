import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner

import GOSVGDProofs.Utils
import GOSVGDProofs.RKHS
import GOSVGDProofs.PushForward

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace
open BigOperators Finset ENNReal NNReal MeasureTheory IsROrC

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 4000000

variable {d : ℕ}

variable [MeasurableSpace (Vector ℝ d)] [MeasureSpace (Vector ℝ d)] [MeasureSpace ℝ]

variable (μ : Measure (Vector ℝ d))

variable [IsProbabilityMeasure μ]

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


/-==============================STEEPEST DIRECTION SECTION==============================-/

/-
  We prove that x ↦ ϕ i x / ‖ϕ‖ is the steepest direction to update the distribution for minimizing the KL derivative.
-/

/-
  From here, as the derivative of multivariate function are hard to define and to manipulate (defining the gradient, the divergence...), we define the gradient of *f* as follows:
  f  : Vector ℝ d → ℝ
  df : ℕ → Vector ℝ d → ℝ
       i ↦ x ↦ ∂xⁱ f(x)
  
  For vector-valued function, we defined them as follows:
  f  : ℕ → Vector ℝ d → ℝ
       i ↦ x ↦ f(x)ⁱ
  df : ℕ → Vector ℝ d → ℝ
       i ↦ x ↦ ∂xⁱ f(x)ⁱ

  Also, we assume some simple lemmas using the above formalism. Sometimes, these lemmas are not rigorously defined but, in our framework, it is more than enough. 
-/

/- dk : x ↦ i ↦ y ↦ ∂xⁱ k(x, y) -/
variable (dk : (Vector ℝ d) → ℕ → (Vector ℝ d) → ℝ)

/- d_log_π : i ↦ x ↦ ∂xⁱ log (μ(x) / π(x)) -/
variable (d_log_π : ℕ → (Vector ℝ d) → ℝ)

/- Definition of the steepest direction ϕ -/
variable (ϕ : ℕ → (Vector ℝ d) → ℝ) (hϕ : ϕ ∈ H) (dϕ : ℕ → (Vector ℝ d) → ℝ) 

def is_phi (ϕ : ℕ → (Vector ℝ d) → ℝ) := ∀ i, ϕ i = (fun x ↦ ∫ y, (d_log_π i y) * (k y x) + (dk y i x) ∂μ)

variable (h_is_ϕ : is_phi μ k dk d_log_π ϕ)

/- We allow ourselve to assume that for easier writing. We will use this only when f is trivially finite (e.g. product of finite functions) and well-defined. -/
variable (is_integrable_H : ∀ (f : ℕ → Vector ℝ d → ℝ), ∀ i ∈ range (d + 1), Integrable (f i) μ)

/--
We show that ⟪f, ϕ⟫ = 𝔼 x ∼ μ [∑ l in range (d + 1), ((d_log_π l x) * (f l x) + df l x)], where ϕ i x = ∫ y, (d_log_π i y) * (k y x) + (dk y i x) ∂μ.
-/
lemma inner_product_eq_dKL (h1 : product_RKHS H H₀) (h2 : inner_product_H H) (f : ℕ → (Vector ℝ d) → ℝ) (hf : f ∈ H) (df : ℕ → (Vector ℝ d) → ℝ) : ⟪f, ϕ⟫ = ∫ x, ∑ l in range (d + 1), ((d_log_π l x) * (f l x) + df l x) ∂μ :=
by
  rw [h2 f hf ϕ hϕ]
  unfold is_phi at h_is_ϕ
  simp_rw [h_is_ϕ]

  -- First, we get the integral out of the inner product.
  have invert_inner_integral : ∀i, ⟪(f i), (fun x ↦ (∫ y, d_log_π i y * k y x + dk y i x ∂μ))⟫ = ∫ y, ⟪(f i), (fun y x ↦ d_log_π i y * k y x + dk y i x) y⟫ ∂μ := fun i ↦ inter_inner_integral_right μ (f i) (fun y x ↦ d_log_π i y * k y x + dk y i x)
  simp_rw [invert_inner_integral]

  -- Then, we switch the integral with the finite sum using *is_integrable_H* assumption.
  have invert_sum_integral : ∑ i in range (d + 1), ∫ (y : Vector ℝ d), (fun i y ↦ ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫) i y ∂μ = ∫ (y : Vector ℝ d), ∑ i in range (d + 1), (fun i y ↦ ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫) i y ∂μ := by {
    symm
    exact integral_finset_sum (range (d + 1)) (by {
      intros i iin
      exact is_integrable_H ((fun i y ↦ ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫)) i iin
    })
  }
  simp_rw [invert_sum_integral]

  -- We use the linearity of inner product to develop it and get the constant d_log_π i y out.
  have linear_inner : ∀y, ∀i, ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫ = d_log_π i y * ⟪f i, fun x ↦ k y x⟫ + ⟪f i, fun x ↦ dk y i x⟫ := fun y i ↦ inner_linear_left (f i) (k y) (dk y i) (d_log_π i y)
  simp_rw [linear_inner]

  -- We use reproducing properties of H₀ to rewrite ⟪f i, k y⟫ as f i y and ⟪f i, dk y i⟫ as df i y.
  have sum_reproducing : ∀ y, ∑ i in range (d + 1), (d_log_π i y * ⟪f i, fun x => k y x⟫ + ⟪f i, fun x => dk y i x⟫) = ∑ i in range (d + 1), (d_log_π i y * (f i y) + df i y) := by {
    intro y
    have reproducing : ∀ x, ∀ i ∈ range (d + 1), ⟪f i, fun y ↦ k x y⟫ = f i x := by {
      intros x i iin
      symm
      apply h_kernel (f i)
      exact h1 f hf i iin
    }
    apply sum_congr (Eq.refl _)
    intros i iin

    have d_reproducing : ⟪f i, fun x => dk y i x⟫ = df i y := reproducing_derivative H₀ dk (f i) (df) (h1 f hf i iin) y i iin

    rw [reproducing y i iin, d_reproducing]
  }
  simp_rw [sum_reproducing]

/--
  We show that the derivative of the KL is bounded by ‖ϕ‖.
-/
lemma bound_direction (h1 : product_RKHS H H₀) (h2 : inner_product_H H) (f : ℕ → (Vector ℝ d) → ℝ) (hf : f ∈ H) (hfb : ‖f‖ = 1) (df : ℕ → (Vector ℝ d) → ℝ) : ∫ x, ∑ l in range (d + 1), ((d_log_π l x) * (f l x) + df l x) ∂μ ≤ ‖ϕ‖ :=
by
  -- We rewrite ∫ x, ∑ l in range (d + 1), ((d_log_π l x) * (f l x) + df l x) as ⟪f, ϕ⟫.
  rw [←inner_product_eq_dKL μ H₀ k h_kernel dk d_log_π ϕ hϕ h_is_ϕ is_integrable_H h1 h2 f hf df]

  -- We use Cauchy-Schwarz inequality.
  calc ⟪f, ϕ⟫ ≤ ‖⟪f, ϕ⟫‖ := le_abs_self ⟪f, ϕ⟫
  _ ≤ ‖f‖ * ‖ϕ‖ := norm_inner_le_norm f ϕ
  _ = ‖ϕ‖ := by {
    rw [hfb]
    simp
  }

/--
We prove that x ↦ ϕ i x / ‖ϕ‖ is the steepest direction for updating the distribution, using ∫ x, ∑ l in range (d + 1), ((d_log_π l x) * (f l x) + df l x) ∂μ = ⟪f, ϕ⟫ ≤ ‖ϕ‖.
-/
theorem steepest_descent_trajectory (h1 : product_RKHS H H₀) (h2 : inner_product_H H) (hϕs : (fun i x ↦ ϕ i x / ‖ϕ‖) ∈ H) : ∫ x, ∑ l in range (d + 1), ((d_log_π l x) * ((fun i x ↦ ϕ i x / ‖ϕ‖) l x) + dϕ l x) ∂μ = ‖ϕ‖ :=
by
  rw [←inner_product_eq_dKL μ H₀ k h_kernel dk d_log_π ϕ hϕ h_is_ϕ is_integrable_H h1 h2 (fun i x ↦ ϕ i x / ‖ϕ‖) hϕs dϕ]

  -- We rewrite the division as a product of inverse.
  have div_to_mul : ∀i, ∀x, ϕ i x / ‖ϕ‖ = ϕ i x * (1 / ‖ϕ‖) := fun i x ↦ div_eq_mul_one_div (ϕ i x) ‖ϕ‖
  simp_rw [div_to_mul]

  -- We use the linearity of the scalar product to get 1 / ‖ϕ‖ out.
  have linear_inner : ⟪(fun i x => ϕ i x * (1 / ‖ϕ‖)), ϕ⟫ = 1 / ‖ϕ‖ * ⟪(fun i x => ϕ i x), ϕ⟫ + ⟪(fun i x => 0), ϕ⟫ := by {
    have comm : ∀i, ∀x, (1 / ‖ϕ‖) * (ϕ i x) = (ϕ i x) * (1 / ‖ϕ‖) := fun i x ↦ mul_comm (1 / ‖ϕ‖) (ϕ i x)
    simp_rw [←comm]
    have add_zero : ⟪fun i x => 1 / ‖ϕ‖ * ϕ i x, ϕ⟫ = ⟪fun i x => 1 / ‖ϕ‖ * ϕ i x + 0, ϕ⟫ := by {simp}
    rw [add_zero]
    exact inner_linear_right ϕ ϕ (fun i x ↦ 0) (1 / ‖ϕ‖)
  }
  rw [linear_inner]

  -- We use the fact that ⟪0, f⟫ = 0.
  have inner_prod_zero : ⟪fun i x ↦ 0, ϕ⟫ = 0 := by {
    exact inner_zero ϕ
  }
  rw[inner_prod_zero, add_zero]

  -- We use the theorem *inner_self_eq_norm_mul_norm* stating that re ⟪a, a⟫ = ‖a‖ * ‖a‖.
  have eq_re : ⟪fun i x ↦ ϕ i x, ϕ⟫ = re ⟪ϕ, ϕ⟫ := by simp
  rw [eq_re]
  rw [inner_self_eq_norm_mul_norm]
  rw [Mathlib.Tactic.RingNF.mul_assoc_rev (1 / ‖ϕ‖) ‖ϕ‖ ‖ϕ‖]
  simp