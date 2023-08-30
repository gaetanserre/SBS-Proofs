import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner

import NMDSProofs.Utils

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace
open BigOperators Finset ENNReal NNReal MeasureTheory

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 4000000

variable {d : ℕ}

variable [MeasurableSpace (Vector ℝ d)] [MeasureSpace (Vector ℝ d)] [MeasureSpace ℝ]

variable (μ : Measure (Vector ℝ d))

variable [IsProbabilityMeasure μ]

variable (h_m_set : ∀ (s : Set (Vector ℝ d)), MeasurableSet s)

/-=====================================RKHS SECTION=====================================-/

/-
  Here we define the product RKHS and we prove that H ⊆ L²(μ)
-/

/-
  We define a RKHS of ((Vector ℝ d) → ℝ) functions.
-/
variable (H₀ : Set ((Vector ℝ d) → ℝ)) [NormedAddCommGroup ((Vector ℝ d) → ℝ)] [InnerProductSpace ℝ ((Vector ℝ d) → ℝ)]

/- The kernel function -/
variable (k : (Vector ℝ d) → (Vector ℝ d) → ℝ) (h_k : (∀ (x : (Vector ℝ d)), k x ∈ H₀) ∧ (∀ (x : (Vector ℝ d)), (fun y ↦ k y x) ∈ H₀))

/--
  Reproducing propriety
-/
def is_kernel := ∀ (f : (Vector ℝ d) → ℝ), f ∈ H₀ → ∀ (x : (Vector ℝ d)), f x = ⟪f, k x⟫

/--
  Positive definite kernel

  For simplicity in the Lean formalism, we define vector-valued function as follows:
  Let f be a function on ℝᵈ to ℝᵈ. The same function in our Lean formalism writes:
  f' : ℕ → Vector ℝ d → ℝ
       i ↦ x ↦ f(x)ⁱ
-/
def positive_definite_kernel := ∀ (f : ℕ → Vector ℝ d → ℝ), (0 ≤ ∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), f i x * k x x' * f i x') ∂μ) ∂μ) ∧ (∫ x in Set.univ, (∫ x' in Set.univ, (∑ i in range (d + 1), f i x * k x x' * f i x') ∂μ) ∂μ = 0 ↔ ∀x, ∀i, f i x = 0)

variable (h_kernel : is_kernel H₀ k) (h_kernel_positive : positive_definite_kernel μ k)

/- We define the product RKHS as a space of function on ℕ → (Vector ℝ d) to ℝ (vector-valued function in our Lean formalism). A function belongs to such a RKHS if f = (f_1, ..., f_d) and ∀ 1 ≤ i ≤ d, fᵢ ∈ H₀. -/
variable {H : Set (ℕ → (Vector ℝ d) → ℝ)} [NormedAddCommGroup (ℕ → (Vector ℝ d) → ℝ)] [InnerProductSpace ℝ (ℕ → (Vector ℝ d) → ℝ)]

def product_RKHS (H : Set (ℕ → (Vector ℝ d) → ℝ)) (H₀ : Set ((Vector ℝ d) → ℝ)) := ∀ f ∈ H, ∀ (i : ℕ), i ∈ range (d + 1) → f i ∈ H₀

def inner_product_H (H : Set (ℕ → (Vector ℝ d) → ℝ)) := ∀ f ∈ H, ∀ g ∈ H, ⟪f, g⟫ = ∑ i in range (d + 1), ⟪f i, g i⟫

variable [NormedAddCommGroup (ℕ → ℝ)] [InnerProductSpace ℝ (ℕ → ℝ)] [CompleteSpace (ℕ → ℝ)]
/--
  The simple vector norm
-/
def norm_H (H : Set (ℕ → (Vector ℝ d) → ℝ)) := ∀ f ∈ H, ∀x, (‖fun i ↦ f i x‖₊ : ℝ≥0∞) = sqrt (∑ i in range (d + 1), ‖f i x‖₊^2)


def integral_is_finite (μ : Measure (Vector ℝ d)) (f : (Vector ℝ d) → ℝ) := ∃ (C : ℝ≥0), ∫⁻ x in Set.univ, ENNReal.ofReal |f x| ∂μ < C

/--
  H ⊆ L2(μ) i.e., ∀ f ∈ H ∫⁻ x in Set.univ, ∑ i in range (d + 1), ENNReal.ofReal (|f i x|)^2 ∂μ < ∞.
-/
theorem H_subset_of_L2 (μ : Measure (Vector ℝ d)) (h1 : product_RKHS H H₀) (h2 : integral_is_finite μ (fun x ↦ k x x)) (h3 : norm_H H) : ∀ f ∈ H, ∫⁻ x in Set.univ, ENNReal.ofReal ‖fun i ↦ f i x‖^2 ∂μ < ∞ :=
by
  intros f finH

  -- We rewrite the absolute value of a norm as positive norm.
  have abs_to_nnorm : ∀ x, ENNReal.ofReal ‖fun i ↦ f i x‖ = ‖fun i ↦ f i x‖₊ := fun x ↦ ofReal_norm_eq_coe_nnnorm fun i => f i x
  simp_rw [abs_to_nnorm]

  -- We use the property of H to rewrite the norm as a sum of norm of function in H₀
  have H_norm : ∀ x, (‖fun i ↦ f i x‖₊ : ℝ≥0∞)^2 = ∑ i in range (d + 1), (‖f i x‖₊ : ℝ≥0∞)^2 := by {
    intro x
    rw [h3 f finH x]
    have sq_coe : ENNReal.some (sqrt (∑ i in range (d + 1), ‖f i x‖₊ ^ 2))^2 = ENNReal.some ((sqrt (∑ i in range (d + 1), ‖f i x‖₊ ^ 2))^2) := nn_square
    rw [sq_coe]
    simp
  }
  simp_rw [H_norm]

  -- We use the reproducing propriety of H₀ to rewrite f i x as ⟪f i, k x⟫.
  have rkhs : ∀ (x : (Vector ℝ d)), ∑ i in range (d + 1), (‖f i x‖₊ : ℝ≥0∞)^2 = ∑ i in range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 := by {
    have temp : ∀ (x : (Vector ℝ d)), ∀ (i : ℕ), i ∈ range (d + 1) → f i x = ⟪f i, k x⟫ := by
    {
      intros x i iInRange
      apply h_kernel
      exact h1 f finH i iInRange
    }
    intro x
    apply sum_congr (Eq.refl _)
    intros i iInRange
    rw [temp x i iInRange]
  }
  simp_rw [rkhs]

  -- Coersive squared Cauchy-Schwarz inequality : (↑‖⟪f i, k x⟫‖₊)² ≤ (↑‖f i‖₊)² (↑‖f x‖₊)².
  have cauchy_schwarz_sq : ∀x, ∀i ∈ range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 ≤ (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 := by {
    intros x i _iInRange
    have distrib : ENNReal.some (‖f i‖₊ * ‖k x‖₊) = (‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞) := coe_distrib ‖f i‖₊ ‖k x‖₊
    rw [(distrib_sq (‖f i‖₊ : ℝ≥0∞) (‖k x‖₊ : ℝ≥0∞))]
    rw [←distrib]
    apply le_square
    have nn_cauchy := nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f i) (k x)
    exact coe_nnreal_le nn_cauchy
  }

  -- If f ≤ g, ∑ i in s, f ≤ ∑ i in s, g. Thus, ∑ i in range (d + 1), (↑‖⟪f i, k x⟫‖₊)² ≤ ∑ i in range (d + 1), (↑‖f i‖)² * (↑‖k x‖₊)².
  have sum_le : (fun x ↦ ∑ i in range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2) ≤ (fun x ↦ ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2) := fun x ↦ sum_le_sum (cauchy_schwarz_sq x)

  -- A lower-Lebesgue integral of a finite sum is equal to a finite sum of lower-Lebesgue integral.
  have inverse_sum_int : ∫⁻ x in Set.univ, ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ = ∑ i in range (d + 1), ∫⁻ x in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := by {
    have is_measurable : ∀ i ∈ range (d + 1), Measurable ((fun i ↦ fun x ↦ (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2) i) := by
    {
      intros i _InRange s _h
      exact h_m_set _
    }
    exact lintegral_finset_sum (range (d + 1)) is_measurable
  }

  -- Retrieve the majorant of the finite sum : ∑ i in range (d + 1), (↑‖f i‖₊)².
  have finite_sum : ∃ (C : ℝ≥0), ∑ i in range (d + 1), (‖f i‖₊^2 : ℝ≥0∞) < C := finite_sum (fun i ↦ ‖f i‖₊^2)
  rcases finite_sum with ⟨C1, finite_sum⟩

  -- Retrieve the majorant of the integral ∫⁻ (x : (Vector ℝ d)) in Set.univ, ↑|k x x| ∂μ, supposed finite.
  rcases h2 with ⟨C2, h2⟩

  -- Rewrite ↑|k x x| as  ↑‖k x x‖₊.
  have abs_to_nnorm : ∀ x, ENNReal.ofReal (|k x x|) = ‖k x x‖₊ := fun x ↦ (Real.ennnorm_eq_ofReal_abs (k x x)).symm
  simp_rw [abs_to_nnorm] at h2

  -- 1. ∀ f ≤ g, ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ. We use this lemma with *sum_le*.
  calc ∫⁻ (x : (Vector ℝ d)) in Set.univ, ∑ i in range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 ∂μ ≤ ∫⁻ (x : (Vector ℝ d)) in Set.univ, ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := lintegral_mono sum_le

  -- 2. Inversion sum integral.
  _ = ∑ i in range (d + 1), ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := inverse_sum_int

  -- 3. As (↑‖f i‖₊)² is a constant in the integral, get it out.
  _ = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := by {
    have is_measurable : Measurable (fun x ↦ (‖k x‖₊ : ℝ≥0∞)^2) := by {
      intros s _hs
      exact h_m_set _
    }
    have const_int : ∀ i, ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ = (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := by {
      intro i
      exact lintegral_const_mul ((‖f i‖₊ : ℝ≥0∞)^2) is_measurable
    }
    simp_rw [const_int]
  }

  -- Rewrite  (↑‖k x‖₊)² as ↑‖⟪k x, k x⟫‖₊ (lot of coercions).
  _ = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖⟪k x, k x⟫‖₊ : ℝ≥0∞) ∂μ := by {
    
    simp_rw [fun x ↦ nn_norm_eq_norm (k x)]

    simp_rw [fun x ↦ enn_square (norm_nonneg (k x))]

    have norm_sq_eq_inner : ∀ x, ⟪k x, k x⟫ = ‖k x‖ ^ 2 := by {
      intro x
      rw [inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (k x)]
      simp
    }
    simp_rw [norm_sq_eq_inner]

    have coe : ∀x, ENNReal.ofReal (‖k x‖ ^ 2) = ↑‖‖k x‖ ^ 2‖₊ := by {
      intro x
      rw [nn_norm_eq_norm_re (‖k x‖ ^ 2)]
      simp
    }
    simp_rw [coe]
  }
  
  -- Use the reproducing propriety of H₀ to write ⟪k x, k x⟫ as k x x.
  _ = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have reproducing_prop : ∀ x, ⟪k x, k x⟫ = k x x := by {
    intro x
    rw [h_kernel (k x) (h_k.left x) x]
    }
    simp_rw [reproducing_prop]
  }

  -- As the integral is a constant in the sum, write ∑ i in ... * ∫⁻ ... as (∑ i in ...) * ∫⁻ ...
  _ = (∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2) * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have sum_mul : (∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2) * (∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ) = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ) := by exact sum_mul
    rw [←sum_mul]
  }

  -- Rewrite (↑‖f i‖₊)² as ↑(‖f i‖₊²) to use the *finite_sum* lemma.
  _ = (∑ i in range (d + 1), (‖f i‖₊^2 : ℝ≥0∞)) * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have coe_sq : ∀ i, (‖f i‖₊ : ℝ≥0∞)^2 = (‖f i‖₊^2 : ℝ≥0∞) := fun i ↦ nn_square
    simp_rw [coe_sq]
  }

  -- Bound the product from above using the two previously retrieved majorants.
  _ < C1 * C2 := ENNReal.mul_lt_mul finite_sum h2

  -- C1 C2 ∈ ℝ≥0
  _ < ∞ := by {
    have h1 : C1 < ∞ := ENNReal.coe_lt_top
    have h2 : C2 < ∞ := ENNReal.coe_lt_top
    exact ENNReal.mul_lt_mul h1 h2
  }