/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib

import SBSProofs.Utils

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace
open BigOperators Finset ENNReal NNReal MeasureTheory

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 4000000

/-=====================================RKHS SECTION=====================================-/

/-
  Here we define the product RKHS and we prove that H ⊆ L²(μ)
-/

/-
  We provide a class definition for a generic RKHS
-/

class RKHS {E F : Type*} [RCLike F] (H : Set (E → F)) [NormedAddCommGroup H] [InnerProductSpace F H] where
  k : E → E → F
  memb : ∀ (x : E), k x ∈ H
  repro : ∀ (hf : f ∈ H), ∀ (x : E), f x = inner (⟨f, hf⟩ : H) ⟨k x, memb x⟩

namespace RKHS
variable {E F : Type*} [RCLike F] {H : Set (E → F)} [NormedAddCommGroup H] [InnerProductSpace F H] [s : RKHS H]
def kx (x : E) : H := ⟨s.k x, s.memb x⟩
end RKHS

variable {d : ℕ} {Ω : Set (Vector ℝ d)}

/-
  We define a RKHS of (Ω → ℝ) functions.
-/
variable (H₀ : Set (Ω → ℝ)) [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [s : RKHS H₀]

/- We define the product RKHS as a space of function on ℕ → Ω to ℝ (vector-valued function in our Lean formalism). A function belongs to such a RKHS if f = (f_1, ..., f_d) and ∀ 1 ≤ i ≤ d, fᵢ ∈ H₀. -/
def product_RKHS {α β : Type*} [RCLike β] (H : Set (α → β)) [NormedAddCommGroup H] [InnerProductSpace β H] [RKHS H] := ℕ → H
def H := product_RKHS H₀

variable [Inner ℝ (H H₀)]

instance : Inner ℝ (H H₀) where
  inner := λ f g ↦ ∑ i ∈ range (d + 1), ⟪f i, g i⟫

variable [NormedAddCommGroup (ℕ → ℝ)]
/--
  The euclidean norm.
-/
def norm_H := ∀ (f : H H₀), ∀x, (‖fun i ↦ (f i).1 x‖₊ : ℝ≥0∞) = sqrt (∑ i ∈ range (d + 1), ‖(f i).1 x‖₊^2)

variable [MeasurableSpace Ω]

/--
We define the integral operator Tkf.
-/
noncomputable def int_operator (μ : Measure Ω) (f : Ω → ℝ) : Ω → ℝ := λ y ↦ ∫ x, s.k y x * f x ∂μ

/--
TODO. Define L².
-/
lemma op_inclusion (f : Ω → ℝ) : int_operator H₀ μ f ∈ H₀ := by sorry

def integral_is_finite (μ : Measure Ω) (f : Ω → ℝ) := ∃ (C : ℝ≥0), ∫⁻ x in Set.univ, ENNReal.ofReal |f x| ∂μ < C

/-
For simplicity, we will use this assumption to prove that some trivial functions are mesurable.
-/
variable (h_m_set : ∀ (s : Set Ω), MeasurableSet s)
/--
  H ⊆ L2(μ) i.e., ∀ f ∈ H, ∫⁻ Ω ||f x||^2 ∂μ < ∞. Please note that (x : Ω) ∈ Set.univ represent the same statement as (x : Vector ℝ d) ∈ Ω. However, the Lean system handles subtypes better than subsets.
-/
theorem H_subset_of_L2 (μ : Measure Ω) (h1 : integral_is_finite μ (fun x ↦ s.k x x)) (h2 : norm_H H₀) : ∀ (f : H H₀), ∫⁻ x in Set.univ, ENNReal.ofReal ‖fun i ↦ (f i).1 x‖^2 ∂μ < ∞ :=
by
  intro f

  -- We rewrite the absolute value of a norm as positive norm.
  have abs_to_nnorm : ∀ x, ENNReal.ofReal ‖fun i ↦ (f i).1 x‖ = ‖fun i ↦ (f i).1 x‖₊ := fun x ↦ ofReal_norm_eq_coe_nnnorm fun i ↦ (f i).1 x
  simp_rw [abs_to_nnorm]

  -- We use the property of H to rewrite the norm as a sum of norm of function in H₀
  have H_norm : ∀ x, (‖fun i ↦ (f i).1 x‖₊ : ℝ≥0∞)^2 = ∑ i ∈ range (d + 1), (‖(f i).1 x‖₊ : ℝ≥0∞)^2 := by {
    intro x
    rw [h2 f x]
    have sq_coe : (sqrt (∑ i ∈ range (d + 1), ‖(f i).1 x‖₊ ^ 2) : ℝ≥0∞)^2 = ((sqrt (∑ i ∈ range (d + 1), ‖(f i).1 x‖₊ ^ 2))^2 : ℝ≥0∞) := rfl
    rw [sq_coe]
    simp
  }
  simp_rw [H_norm]

  -- We use the reproducing propriety of H₀ to rewrite f i x as ⟪f i, k x⟫.
  have rkhs : ∀ (x : Ω), ∑ i ∈ range (d + 1), (‖(f i).1 x‖₊ : ℝ≥0∞)^2 = ∑ i ∈ range (d + 1), (‖⟪(f i), s.kx x⟫‖₊ : ℝ≥0∞)^2 := by {
    have temp : ∀ (x : Ω), ∀ (i : ℕ), i ∈ range (d + 1) → (f i).1 x = ⟪f i, s.kx x⟫ := by
    {
      intro x i iInRange
      rw (config := {occs := .pos [2]}) [show f i = ⟨(f i).1, (f i).2⟩ by rfl]
      exact s.repro (f i).2 x
    }
    intro x
    apply sum_congr (Eq.refl _)
    intro i iInRange
    rw [temp x i iInRange]
  }
  simp_rw [rkhs]

  -- Coersive squared Cauchy-Schwarz inequality : (↑‖⟪f i, k x⟫‖₊)² ≤ (↑‖f i‖₊)² (↑‖f x‖₊)².
  have cauchy_schwarz_sq : ∀x, ∀i ∈ range (d + 1), (‖⟪(f i), s.kx x⟫‖₊ : ℝ≥0∞)^2 ≤ (‖f i‖₊ : ℝ≥0∞)^2 * (‖s.kx x‖₊ : ℝ≥0∞)^2 := by {
    intro x i _iInRange
    rw [(distrib_sq (‖f i‖₊ : ℝ≥0∞) (‖s.kx x‖₊ : ℝ≥0∞))]
    apply le_square
    have nn_cauchy := nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f i) (s.kx x)
    exact coe_nnreal_le nn_cauchy
  }

  -- If f ≤ g, ∑ i ∈ s, f ≤ ∑ i ∈ s, g. Thus, ∑ i ∈ range (d + 1), (↑‖⟪f i, k x⟫‖₊)² ≤ ∑ i ∈ range (d + 1), (↑‖f i‖)² * (↑‖k x‖₊)².
  have sum_le : (fun x ↦ ∑ i ∈ range (d + 1), (‖⟪f i, s.kx x⟫‖₊ : ℝ≥0∞)^2) ≤ (fun x ↦ ∑ i ∈ range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖s.kx x‖₊ : ℝ≥0∞)^2) := fun x ↦ sum_le_sum (cauchy_schwarz_sq x)

  -- A lower-Lebesgue integral of a finite sum is equal to a finite sum of lower-Lebesgue integral.
  have inverse_sum_int : ∫⁻ x in Set.univ, ∑ i ∈ range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖s.kx x‖₊ : ℝ≥0∞)^2 ∂μ = ∑ i ∈ range (d + 1), ∫⁻ x in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖s.kx x‖₊ : ℝ≥0∞)^2 ∂μ := by {
    have is_measurable : ∀ i ∈ range (d + 1), Measurable ((fun i ↦ fun x ↦ (‖f i‖₊ : ℝ≥0∞)^2 * (‖s.kx x‖₊ : ℝ≥0∞)^2) i) := by
    {
      intro i _InRange s _h
      exact h_m_set _
    }
    exact lintegral_finset_sum (range (d + 1)) is_measurable
  }

  -- Retrieve the majorant of the finite sum : ∑ i ∈ range (d + 1), (↑‖f i‖₊)².
  have finite_sum : ∃ (C : ℝ≥0), ∑ i ∈ range (d + 1), (‖f i‖₊^2 : ℝ≥0∞) < C := finite_sum (fun i ↦ ‖f i‖₊^2)
  rcases finite_sum with ⟨C1, finite_sum⟩

  -- Retrieve the majorant of the integral ∫⁻ x ∈ Ω, ↑|k x x| ∂μ, supposed finite.
  rcases h1 with ⟨C2, h1⟩

  -- Rewrite ↑|k x x| as  ↑‖k x x‖₊.
  have abs_to_nnorm : ∀ x, ENNReal.ofReal (|s.k x x|) = ‖s.k x x‖₊ := fun x ↦ (Real.ennnorm_eq_ofReal_abs (s.k x x)).symm
  simp_rw [abs_to_nnorm] at h1

  -- 1. ∀ f ≤ g, ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ. We use this lemma with *sum_le*.
  calc ∫⁻ (x : Ω) in Set.univ, ∑ i ∈ range (d + 1), (‖⟪f i, s.kx x⟫‖₊ : ℝ≥0∞)^2 ∂μ ≤ ∫⁻ (x : Ω) in Set.univ, ∑ i ∈ range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖s.kx x‖₊ : ℝ≥0∞)^2 ∂μ := lintegral_mono sum_le

  -- 2. Inversion sum integral.
  _ = ∑ i ∈ range (d + 1), ∫⁻ (x : Ω) in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖s.kx x‖₊ : ℝ≥0∞)^2 ∂μ := inverse_sum_int

  -- 3. As (↑‖f i‖₊)² is a constant in the integral, get it out.
  _ = ∑ i ∈ range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : Ω) in Set.univ, (‖s.kx x‖₊ : ℝ≥0∞)^2 ∂μ := by {
    have is_measurable : Measurable (fun x ↦ (‖s.kx x‖₊ : ℝ≥0∞)^2) := by {
      intro s _hs
      exact h_m_set _
    }
    have const_int : ∀ i, ∫⁻ (x : Ω) in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖s.kx x‖₊ : ℝ≥0∞)^2 ∂μ = (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : Ω) in Set.univ, (‖s.kx x‖₊ : ℝ≥0∞)^2 ∂μ := by {
      intro i
      exact lintegral_const_mul ((‖f i‖₊ : ℝ≥0∞)^2) is_measurable
    }
    simp_rw [const_int]
  }

  -- Rewrite  (↑‖k x‖₊)² as ↑‖⟪k x, k x⟫‖₊ (lot of coercions).
  _ = ∑ i ∈ range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : Ω) in Set.univ, (‖⟪s.kx x, s.kx x⟫‖₊ : ℝ≥0∞) ∂μ := by {

    simp_rw [fun x ↦ nn_norm_eq_norm (s.kx x)]

    simp_rw [fun x ↦ enn_square (norm_nonneg (s.kx x))]

    have norm_sq_eq_inner : ∀ x, ⟪s.kx x, s.kx x⟫ = ‖s.kx x‖ ^ 2 := by {
      intro x
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (s.kx x)]
      simp
    }
    simp_rw [norm_sq_eq_inner]

    have coe : ∀x, ENNReal.ofReal (‖s.kx x‖ ^ 2) = ↑‖‖s.kx x‖ ^ 2‖₊ := by {
      intro x
      rw [nn_norm_eq_norm_re (‖s.kx x‖ ^ 2)]
      simp
    }
    simp_rw [coe]
  }

  -- Use the reproducing propriety of H₀ to write ⟪k x, k x⟫ as k x x.
  _ = ∑ i ∈ range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : Ω) in Set.univ, (‖s.k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have reproducing_prop : ∀ x, ⟪s.kx x, s.kx x⟫ = s.k x x := by {
      intro x
      rw [s.repro (s.memb x) x, show s.kx x = ⟨s.k x, s.memb x⟩ by rfl]
    }
    simp_rw [reproducing_prop]
  }

  -- As the integral is a constant in the sum, write ∑ i ∈ ... * ∫⁻ ... as (∑ i ∈ ...) * ∫⁻ ...
  _ = (∑ i ∈ range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2) * ∫⁻ (x : Ω) in Set.univ, (‖s.k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have sum_mul : (∑ i ∈ range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2) * (∫⁻ (x : Ω) in Set.univ, (‖s.k x x‖₊ : ℝ≥0∞) ∂μ) = ∑ i ∈ range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (∫⁻ (x : Ω) in Set.univ, (‖s.k x x‖₊ : ℝ≥0∞) ∂μ) := by exact sum_mul (range (d + 1)) (fun i ↦ (‖f i‖₊ : ℝ≥0∞)^2) (∫⁻ (x : Ω) in Set.univ, (‖s.k x x‖₊ : ℝ≥0∞) ∂μ)
    rw [←sum_mul]
  }

  -- Bound the product from above using the two previously retrieved majorants.
  _ < C1 * C2 := ENNReal.mul_lt_mul finite_sum h1

  -- C1 C2 ∈ ℝ≥0
  _ < ∞ := by {
    have h1 : C1 < ∞ := ENNReal.coe_lt_top
    have h2 : C2 < ∞ := ENNReal.coe_lt_top
    exact ENNReal.mul_lt_mul h1 h2
  }
