import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import GOSVGDProofs.RKHS
import GOSVGDProofs.PushForward

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace 
open BigOperators Finset ENNReal NNReal MeasureTheory MeasureTheory.Measure

set_option trace.Meta.Tactic.simp.rewrite true

variable (d : ℕ)
/-
  We define a RKHS of ((Vector ℝ d) → ℝ) functions.
-/
variable (H₀ : Set ((Vector ℝ d) → ℝ)) [NormedAddCommGroup ((Vector ℝ d) → ℝ)] [InnerProductSpace ℝ ((Vector ℝ d) → ℝ)] [CompleteSpace ((Vector ℝ d) → ℝ)] [MeasurableSpace (Vector ℝ d)] [PosMulStrictMono ℝ≥0∞] [MulPosStrictMono ℝ≥0∞]

/- The kernel function -/
variable (k : (Vector ℝ d) → (Vector ℝ d) → ℝ) (h_k : (∀ (x : (Vector ℝ d)), k x ∈ H₀) ∧ (∀ (x : (Vector ℝ d)), (fun y ↦ k y x) ∈ H₀))

/-
  Reproducing propriety
-/
variable (h_kernel : is_kernel d H₀ k)

/- We define the product RKHS as a space of function on (ℕ → (Vector ℝ d) → ℝ). A function belongs to such a RKHS if f = (f_1, ..., f_d) and ∀ 1 ≤ i ≤ d, fᵢ ∈ H₀. -/
variable {H : Set (ℕ → (Vector ℝ d) → ℝ)} [NormedAddCommGroup (ℕ → (Vector ℝ d) → ℝ)] [InnerProductSpace ℝ (ℕ → (Vector ℝ d) → ℝ)] [CompleteSpace (ℕ → (Vector ℝ d) → ℝ)]


variable [NormedAddCommGroup (Vector ℝ d)] [InnerProductSpace ℝ (Vector ℝ d)] [CompleteSpace (Vector ℝ d)]
example (a b d : (Vector ℝ d)) (c : ℝ) : ⟪c • a, b + d⟫ = c * (⟪a, b⟫ + ⟪a, d⟫) :=
by
  have key : ⟪c • a, b + d⟫ = c * ⟪a, b + d⟫ := real_inner_smul_left a (b + d) c
  have key2 : ⟪a, b + d⟫ = ⟪a, b⟫ + ⟪a, d⟫ := inner_add_right a b d
  rw [key, key2]

/- Steepest direction -/

/--
  Linearity of inner product applied to integral
-/
lemma inter_inner_integral_right (μ : Measure (Vector ℝ d)) (g : (Vector ℝ d) → ℝ) (f : (Vector ℝ d) → (Vector ℝ d) → ℝ) : ⟪g, (fun x ↦ (∫ y, f y x ∂μ))⟫ = ∫ y, ⟪g, f y⟫ ∂μ :=
by
sorry

/--
  Linearity of inner product for function
-/
lemma inner_linear (f a b : Vector ℝ d → ℝ) (c : ℝ) : ⟪f, fun x ↦ c * a x + b x⟫ = c * ⟪f, fun x ↦ a x⟫ + ⟪f, fun x ↦ b x⟫ := by sorry

/-
dk x i = y ↦ (∂x k(x, y))ⁱ

f : (Vector ℝ d) → ℝ
df : ℕ → (Vector ℝ d) → ℝ 
      x ↦ (∂xⁱ f(x))
-/
variable (dk : (Vector ℝ d) → ℕ → (Vector ℝ d) → ℝ) (hdk : ∀ x, ∀ i, dk x i ∈ H₀)

theorem reproducing_derivative (f : (Vector ℝ d) → ℝ) (df' : ℕ → (Vector ℝ d) → ℝ) (hf : f ∈ H₀) : ∀x, ∀ i ∈ range (d + 1), ⟪f, dk x i⟫ = df' i x :=
by
  -- See Theorem 1 of *Derivative reproducing properties for kernel methods in learning theory*
  sorry


variable (φ : ℕ → (Vector ℝ d) → ℝ) (hφ : φ ∈ H) (μ π ν : Measure (Vector ℝ d)) (dμ dπ : (Vector ℝ d) → ℝ≥0∞) (h_dpμ : is_density μ ν dμ) (h_dpπ : is_density π ν dπ) (d_log_π : ℕ → (Vector ℝ d) → ℝ) [MeasureSpace (Vector ℝ d)] [MeasureSpace ℝ]

def is_phi (φ : ℕ → (Vector ℝ d) → ℝ) := ∀ i, φ i = (fun x ↦ ∫ y, (d_log_π i y) * (k y x) + (dk y i x) ∂μ)

variable (h_is_φ : is_phi d k dk μ d_log_π φ)

/- We allow ourselve to assume that for easier writing. We will use this lemma only when f is trivially finite and well-defined. -/
variable (is_integrable : ∀ (f : ℕ → Vector ℝ d → ℝ), ∀ i ∈ range (d + 1), Integrable (f i) μ)

/--
We show that ⟪f, φ⟫ = 𝔼 x ∼ μ [∑ l in range (d + 1), ((d_log_π l x) * (f l x) + df l x)], where φ i x = ∫ y, (d_log_π i y) * (k y x) + (dk y i x) ∂μ
-/
lemma steepest_descent_trajectory (h1 : product_RKHS d H H₀) (h2 : inner_product_H d H) (f : ℕ → (Vector ℝ d) → ℝ) (hf : f ∈ H) (df : ℕ → (Vector ℝ d) → ℝ) : ⟪f, φ⟫ = ∫ x, ∑ l in range (d + 1), ((d_log_π l x) * (f l x) + df l x) ∂μ :=
by
  rw [h2 f hf φ hφ]
  unfold is_phi at h_is_φ
  simp_rw [h_is_φ]

  /- First, we get the integral out of the inner product -/
  have invert_inner_integral : ∀i, ⟪(f i), (fun x ↦ (∫ y, d_log_π i y * k y x + dk y i x ∂μ))⟫ = ∫ y, ⟪(f i), (fun y x ↦ d_log_π i y * k y x + dk y i x) y⟫ ∂μ := fun i ↦ inter_inner_integral_right d μ (f i) (fun y x ↦ d_log_π i y * k y x + dk y i x)
  simp_rw [invert_inner_integral]

  /- Then, we switch the integral with the finite sum using *is_integrable* assumption -/
  have invert_sum_integral : ∑ i in range (d + 1), ∫ (y : Vector ℝ d), (fun i y ↦ ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫) i y ∂μ = ∫ (y : Vector ℝ d), ∑ i in range (d + 1), (fun i y ↦ ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫) i y ∂μ := by {
    symm
    exact integral_finset_sum (range (d + 1)) (by {
      intros i iin
      exact is_integrable ((fun i y ↦ ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫)) i iin
    })
  }
  simp_rw [invert_sum_integral]

  /- We use the linearity of inner product to develop it and get the constant d_log_π i y out and -/
  have linear_inner : ∀y, ∀i, ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫ = d_log_π i y * ⟪f i, fun x ↦ k y x⟫ + ⟪f i, fun x ↦ dk y i x⟫ := fun y i ↦ inner_linear d (f i) (k y) (dk y i) (d_log_π i y)
  simp_rw [linear_inner]

  /- We use reproducing properties of H₀ to rewrite ⟪f i, k y⟫ as f i y and ⟪f i, dk y i⟫ as df i y -/
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

    have d_reproducing : ⟪f i, fun x => dk y i x⟫ = df i y := reproducing_derivative d H₀ dk (f i) (df) (h1 f hf i iin) y i iin

    rw [reproducing y i iin, d_reproducing]
  }
  simp_rw [sum_reproducing]