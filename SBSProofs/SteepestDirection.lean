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
import SBSProofs.RKHS

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
variable (H₀ : Set ((Vector ℝ d) → ℝ)) [NormedAddCommGroup ((Vector ℝ d) → ℝ)] [InnerProductSpace ℝ ((Vector ℝ d) → ℝ)] [s : RKHS H₀]

/- We define the product RKHS as a space of function on ℕ → (Vector ℝ d) to ℝ (vector-valued function in our Lean formalism). A function belongs to such a RKHS if f = (f_1, ..., f_d) and ∀ 1 ≤ i ≤ d, fᵢ ∈ H₀. -/
variable (H : Set (ℕ → (Vector ℝ d) → ℝ)) [NormedAddCommGroup (ℕ → (Vector ℝ d) → ℝ)] [InnerProductSpace ℝ (ℕ → (Vector ℝ d) → ℝ)]

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

/- d_ln_π : i ↦ x ↦ ∂xⁱ ln (μ(x) / π(x)) -/
variable (d_ln_π : ℕ → (Vector ℝ d) → ℝ)

/--
  Definition of the steepest direction ϕ
-/
noncomputable def ϕ_ (i : ℕ) (x : Vector ℝ d) : ℝ := ∫ y, (d_ln_π i y) * (s.k y x) + (dk y i x) ∂μ

variable (dϕ : ℕ → (Vector ℝ d) → ℝ)

/-
d_ln_π_μ : i ↦ x ↦ ∂xⁱ ln (π(x) / μ(x))
-/
variable (d_ln_π_μ : ℕ → (Vector ℝ d) → ℝ)

/--
ϕ i = Tk ∂_x(ln π(⬝) - ln μ(⬝)). Trivial using the fact that ϕ is in the Stein class of k and integration by parts. Very heavy in Lean, so we assume it.
-/
lemma ϕ_eq : ∀ i ∈ range (d + 1), (ϕ_ μ H₀ dk d_ln_π) i = int_operator H₀ μ (d_ln_π_μ i) := by sorry

/--
ϕ ∈ H
-/
lemma ϕ_in_H (h : product_RKHS H H₀) : (ϕ_ μ H₀ dk d_ln_π) ∈ H :=
by
  rw [h (ϕ_ μ H₀ dk d_ln_π)]
  intro i iInRange
  rw [ϕ_eq μ H₀ dk d_ln_π d_ln_π_μ i iInRange]
  let g := λ i ↦ int_operator H₀ μ (d_ln_π_μ i)
  have g_i_in_H0 : ∀ i ∈ range (d + 1), g i ∈ H₀ := by {
    intro i _
    exact op_inclusion H₀ (d_ln_π_μ i)
  }
  exact g_i_in_H0 i iInRange

/- We allow ourselve to assume that for easier writing. We will use this only when f is trivially finite (e.g. product of finite functions) and well-defined. -/
variable (is_integrable_H : ∀ (f : ℕ → Vector ℝ d → ℝ), ∀ i ∈ range (d + 1), Integrable (f i) μ)

/--
We show that ⟪f, ϕ⟫ = 𝔼 x ∼ μ [∑ l in range (d + 1), ((d_ln_π l x) * (f l x) + df l x)], where ϕ i x = ∫ y, (d_ln_π i y) * (k y x) + (dk y i x) ∂μ.
-/
lemma inner_product_eq_dKL (h1 : product_RKHS H H₀) (h2 : inner_product_H H) (f : ℕ → (Vector ℝ d) → ℝ) (hf : f ∈ H) (df : ℕ → (Vector ℝ d) → ℝ) : ⟪f, ϕ_ μ H₀ dk d_ln_π⟫ = ∫ x, ∑ l in range (d + 1), ((d_ln_π l x) * (f l x) + df l x) ∂μ :=
by
  let ϕ := ϕ_ μ H₀ dk d_ln_π
  let hϕ := ϕ_in_H μ H₀ H dk d_ln_π d_ln_π_μ h1
  rw [h2 f hf ϕ hϕ]

  -- First, we get the integral out of the inner product.
  have invert_inner_integral : ∀i, ⟪(f i), (fun x ↦ (ϕ i x))⟫ = ∫ y, ⟪(f i), (fun y x ↦ d_ln_π i y * s.k y x + dk y i x) y⟫ ∂μ := fun i ↦ inter_inner_integral_right μ (f i) (fun y x ↦ d_ln_π i y * s.k y x + dk y i x)
  simp_rw [invert_inner_integral]

  -- Then, we switch the integral with the finite sum using *is_integrable_H* assumption.
  have invert_sum_integral : ∑ i in range (d + 1), ∫ (y : Vector ℝ d), (fun i y ↦ ⟪f i, fun x ↦ d_ln_π i y * s.k y x + dk y i x⟫) i y ∂μ = ∫ (y : Vector ℝ d), ∑ i in range (d + 1), (fun i y ↦ ⟪f i, fun x ↦ d_ln_π i y * s.k y x + dk y i x⟫) i y ∂μ := by {
    symm
    exact integral_finset_sum (range (d + 1)) (by {
      intros i iin
      exact is_integrable_H ((fun i y ↦ ⟪f i, fun x ↦ d_ln_π i y * s.k y x + dk y i x⟫)) i iin
    })
  }
  simp_rw [invert_sum_integral]

  -- We use the linearity of inner product to develop it and get the constant d_ln_π i y out.
  have linear_inner : ∀y, ∀i, ⟪f i, fun x ↦ d_ln_π i y * s.k y x + dk y i x⟫ = d_ln_π i y * ⟪f i, fun x ↦ s.k y x⟫ + ⟪f i, fun x ↦ dk y i x⟫ := fun y i ↦ inner_linear_left (f i) (s.k y) (dk y i) (d_ln_π i y)
  simp_rw [linear_inner]

  -- We use reproducing properties of H₀ to rewrite ⟪f i, k y⟫ as f i y and ⟪f i, dk y i⟫ as df i y.
  have sum_reproducing : ∀ y, ∑ i in range (d + 1), (d_ln_π i y * ⟪f i, fun x => s.k y x⟫ + ⟪f i, fun x => dk y i x⟫) = ∑ i in range (d + 1), (d_ln_π i y * (f i y) + df i y) := by {
    intro y
    have reproducing : ∀ x, ∀ i ∈ range (d + 1), ⟪f i, fun y ↦ s.k x y⟫ = f i x := by {
      intros x i iin
      symm
      apply s.reproducing (f i)
      exact (h1 f).mp hf i iin
    }
    apply sum_congr (Eq.refl _)
    intros i iin

    have d_reproducing : ⟪f i, fun x => dk y i x⟫ = df i y := reproducing_derivative H₀ dk (f i) (df) ((h1 f).mp hf i iin) y i iin

    rw [reproducing y i iin, d_reproducing]
  }
  simp_rw [sum_reproducing]

/--
  We show that the derivative of the KL is bounded by ‖ϕ‖.
-/
lemma bound_direction (h1 : product_RKHS H H₀) (h2 : inner_product_H H) (f : ℕ → (Vector ℝ d) → ℝ) (hf : f ∈ H) (hfb : ‖f‖ = 1) (df : ℕ → (Vector ℝ d) → ℝ) : ∫ x, ∑ l in range (d + 1), ((d_ln_π l x) * (f l x) + df l x) ∂μ ≤ ‖ϕ_ μ H₀ dk d_ln_π‖ :=
by
  let ϕ := ϕ_ μ H₀ dk d_ln_π
  -- We rewrite ∫ x, ∑ l in range (d + 1), ((d_ln_π l x) * (f l x) + df l x) as ⟪f, ϕ⟫.
  rw [←inner_product_eq_dKL μ H₀ H dk d_ln_π d_ln_π_μ is_integrable_H h1 h2 f hf df]

  -- We use Cauchy-Schwarz inequality.
  calc ⟪f, ϕ⟫ ≤ ‖⟪f, ϕ⟫‖ := le_abs_self ⟪f, ϕ⟫
  _ ≤ ‖f‖ * ‖ϕ‖ := norm_inner_le_norm f ϕ
  _ = ‖ϕ‖ := by {
    rw [hfb]
    simp
  }

/--
We prove that x ↦ ϕ i x / ‖ϕ‖ is the steepest direction for updating the distribution, using ∫ x, ∑ l in range (d + 1), ((d_ln_π l x) * (f l x) + df l x) ∂μ = ⟪f, ϕ⟫ ≤ ‖ϕ‖.
-/
theorem steepest_descent_trajectory (h1 : product_RKHS H H₀) (h2 : inner_product_H H) (hϕs : (fun i x ↦ (ϕ_ μ H₀ dk d_ln_π) i x / ‖(ϕ_ μ H₀ dk d_ln_π)‖) ∈ H) : ∫ x, ∑ l in range (d + 1), ((d_ln_π l x) * ((fun i x ↦ (ϕ_ μ H₀ dk d_ln_π) i x / ‖(ϕ_ μ H₀ dk d_ln_π)‖) l x) + dϕ l x) ∂μ = ‖(ϕ_ μ H₀ dk d_ln_π)‖ :=
by
  let ϕ := ϕ_ μ H₀ dk d_ln_π
  rw [←inner_product_eq_dKL μ H₀ H dk d_ln_π d_ln_π_μ is_integrable_H h1 h2 (fun i x ↦ ϕ i x / ‖ϕ‖) hϕs dϕ]

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
