import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import GOSVGDProofs.RKHS

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

lemma inter_inner_integral_right (μ : Measure (Vector ℝ d)) (f : (Vector ℝ d) → (Vector ℝ d) → ℝ) (g : (Vector ℝ d) → ℝ) (hg : g ∈ H₀) (hf : (∀ (x : (Vector ℝ d)), f x ∈ H₀) ∧ (∀ (x : (Vector ℝ d)), (fun y ↦ f y x) ∈ H₀)) : ⟪g, (fun x ↦ ENNReal.toReal (∫⁻ y in Set.univ, ENNReal.ofReal (f y x) ∂μ))⟫ = ENNReal.toReal (∫⁻ y in Set.univ, ENNReal.ofReal ⟪g, f y⟫ ∂μ) :=
by
sorry

/-
dk x i = y ↦ (∂x k(x, y))ⁱ

f : (Vector ℝ d) → ℝ
df' : ℕ → (Vector ℝ d) → ℝ 
      x ↦ (∂xⁱ f(x))
-/
variable (dk : (Vector ℝ d) → ℕ → (Vector ℝ d) → ℝ) (hdk : ∀ x, ∀ i, dk x i ∈ H₀)

theorem reproducing_derivative (f : (Vector ℝ d) → ℝ) (df' : ℕ → (Vector ℝ d) → ℝ) (hf : f ∈ H₀) : ∀x, ∀ i ∈ range (d + 1), ⟪f, dk x i⟫ = df' i x :=
by
  sorry



noncomputable def divergence (f' : ℕ → (Vector ℝ d) → ℝ) (x : Vector ℝ d) := ∑ i in range (d + 1), f' i x