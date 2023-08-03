import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Calculus.FDeriv.Basic

import GOSVGDProofs.PushForward

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace 
open BigOperators Finset ENNReal NNReal MeasureTheory MeasureTheory.Measure IsROrC

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 4000000

/-
  We defined measures μ and π (ν is considered as the standard Lebesgue measure) along with their densities (finite and non-zero on the entire space)
-/
variable {d : ℕ}

variable [MeasurableSpace (Vector ℝ d)] [MeasureSpace (Vector ℝ d)] [MeasureSpace ℝ]

variable (μ π ν : Measure (Vector ℝ d)) (dμ dπ : (Vector ℝ d) → ℝ≥0∞) (hμ : is_density μ ν dμ) (hπ : is_density π ν dπ) (mdμ : Measurable dμ) (mdπ : Measurable dπ) (hdμ : ∀x, dμ x ≠ 0 ∧ dμ x ≠ ∞) (hdπ : ∀x, dπ x ≠ 0 ∧ dπ x ≠ ∞)

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure π]

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

/--
  For all non-empty finite set s, ∃ e ∈ s, ∀ a ∈ s, a ≤ e.
-/
theorem exist_max_finset {ι : Type _} [LinearOrder ι] (s : Finset ι) (h : Finset.Nonempty s) : ∃ e ∈ s, ∀ a ∈ s, a ≤ e :=
by
  use (Finset.max' s h)
  constructor
  {exact max'_mem s h}
  {
    intros a ains
    exact le_max' s a ains
  }

/--
  Given a non-empty finite set s and a function f on elements of s, ∃ j ∈ s, ∀ i ∈ s, f i ≤ f j.
-/
theorem exist_max_image_finset {ι E : Type _} [LinearOrder E] (s : Finset ι) (h : Finset.Nonempty s) (f : ι → E) : ∃ j ∈ s, ∀ i ∈ s, f i ≤ f j :=
by 
  let sf := Finset.image f s
  have hf : Finset.Nonempty sf := Nonempty.image h f

  have max : ∃ e ∈ sf, ∀ a ∈ sf, a ≤ e := exist_max_finset sf hf

  rcases max with ⟨c, cin, max⟩
  rw [Finset.mem_image] at cin
  rcases cin with ⟨j, jin, fj⟩

  use j
  constructor
  {exact jin}
  intros i iin
  specialize max (f i)
  rw [fj]
  exact max (mem_image_of_mem f iin)

/--
  a*a = a²
-/
theorem square {M : Type _} [Monoid M] (a : M) : a * a = a^2 := (sq a).symm

/--
  a² * b² = (a * b)²
-/
theorem distrib_sq {M : Type _} [CommMonoid M] (a b : M) : a^2 * b^2 = (a * b)^2 := (mul_pow a b 2).symm
/--
  ∀ a b ∈ ℝ⁺ ∪ {∞}, a ≤ b → a² ≤ b²
-/
theorem le_square {a b : ℝ≥0∞} (h : a ≤ b) : a^2 ≤ b^2 :=
by
  have k := mul_le_mul h h (by simp) (by simp)
  rwa [←square a, ←square b]

/- Coercion theorems -/

theorem le_coe (a : ℝ) (b : NNReal) (h1 : 0 ≤ a) : ‖a‖₊ ≤ b → ENNReal.ofReal a ≤ ENNReal.ofReal b :=
by
  intro h
  have k := Real.ennnorm_eq_ofReal h1
  rw [←k]
  rwa [ENNReal.ofReal_coe_nnreal, ENNReal.coe_le_coe]

theorem coe_nnreal_le {a b : ℝ≥0} (h : a ≤ b) : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := Iff.mpr coe_le_coe h

theorem coe_distrib (a b : ℝ≥0) : ENNReal.some (a * b) = (a : ℝ≥0∞) * (b : ℝ≥0∞) := ENNReal.coe_mul

theorem nn_norm_eq_norm (a : (Vector ℝ d) → ℝ) : ‖a‖₊ = ENNReal.ofReal ‖a‖ := (ofReal_norm_eq_coe_nnnorm a).symm

theorem nn_norm_eq_norm_re (a : ℝ) : ‖a‖₊ = ENNReal.ofReal ‖a‖ := (ofReal_norm_eq_coe_nnnorm a).symm

theorem enn_square {a : ℝ} (h : 0 ≤ a) : ENNReal.ofReal (a) ^ 2 = ENNReal.ofReal (a ^ 2) :=
by
  rw [←square (ENNReal.ofReal (a)), ←square a]
  exact (ofReal_mul h).symm

theorem nn_square {a : ℝ≥0} : (a : ℝ≥0∞) ^ 2 = (a ^ 2 : ℝ≥0∞) := (ENNReal.coe_pow 2).symm

/--
  A finite sum of finite elements is finite.
-/
theorem finite_sum (f : ℕ → ℝ≥0) : ∃ (C : ℝ≥0), ∑ i in range (d + 1), (f i : ℝ≥0∞) < ENNReal.some C :=
by
  /- We begin to show that each element of the sum is bounded from above. -/
  have sup_el : ∀ i ∈ range (d + 1), ∃ c, (f i) < c := fun i _ ↦ exists_gt (f i)

  /- We find the argmax of the set {f i | ∀ i ∈ range (d + 1)} using the *exist_max_image_finset* lemma. -/
  have max : ∃ j ∈ range (d+1), ∀ i ∈ range (d+1), f i ≤ f j := by {
    have non_empty : ∀ (n : ℕ), Finset.Nonempty (range (n+1)) := fun n ↦ nonempty_range_succ
    have max := exist_max_image_finset (range (d+1)) (non_empty d) (fun i ↦ f i)
    rcases max with ⟨j, jin, max⟩
    use j
  }

  /- We show that the majorant of the biggest element majors every element of the sum  -/
  have sup : ∃ c, ∀ i ∈ range (d + 1), f i < c := by {
    rcases max with ⟨j, jin, max⟩
    choose C sup_el using sup_el
    use (C j jin)
    intros i iin
    specialize max i iin
    specialize sup_el j jin
    calc (f i) ≤ (f j) := max
    _ < C j jin := sup_el
  }

  /- Same as above, with coercion -/
  have sup_coe : ∃ (c:ℝ≥0), ∀ (i : ℕ), i ∈ range (d + 1) → (f i : ℝ≥0∞) < c := by {
    rcases sup with ⟨C, sup⟩
    use C
    intros i iin
    specialize sup i iin
    have coe_lt : ∀ (a b : ℝ≥0), (a < b) → ENNReal.some a < ENNReal.some b := by {
      intros a b h
      exact Iff.mpr coe_lt_coe h
    }
    exact coe_lt (f i) C sup
  }

  rcases sup_coe with ⟨c, sup_coe⟩

  /- The sum is bounded from above by the sum of the majorant -/
  have sum_le : ∑ i in range (d + 1), (f i : ℝ≥0∞) < ∑ i in range (d + 1), (c : ℝ≥0∞) := sum_lt_sum_of_nonempty (by simp) sup_coe

  /- Same as above, with coercion -/
  have sum_coe : ∑ i in range (d + 1), (c : ℝ≥0∞) = ENNReal.some (∑ i in range (d + 1), c) := coe_finset_sum.symm

  /- Sum of constant = constant -/
  have sum_simpl : ∑ i in range (d + 1), c = (d+1) • c := (nsmul_eq_sum_const c (d + 1)).symm

  use ((d+1) • c)

  calc ∑ i in range (d + 1), (f i: ℝ≥0∞) < ∑ i in range (d + 1), (c : ℝ≥0∞) := sum_le
  _ = ENNReal.some (∑ i in range (d + 1), c) := sum_coe
  _ = ENNReal.some ((d+1) • c) := by rw [sum_simpl]

def integral_is_finite (μ : Measure (Vector ℝ d)) (f : (Vector ℝ d) → ℝ) := ∃ (C : ℝ≥0), ∫⁻ x in Set.univ, ENNReal.ofReal |f x| ∂μ < C

/--
  H ⊆ L2(μ) i.e., ∀ f ∈ H ∫⁻ x in Set.univ, ∑ i in range (d + 1), ENNReal.ofReal (|f i x|)^2 ∂μ < ∞.
-/
theorem H_subset_of_L2 (μ : Measure (Vector ℝ d)) (h1 : product_RKHS H H₀) (h2 : integral_is_finite μ (fun x ↦ k x x)) (h3 : norm_H H) : ∀ f ∈ H, ∫⁻ x in Set.univ, ENNReal.ofReal ‖fun i ↦ f i x‖^2 ∂μ < ∞ :=
by
  intros f finH

  /- We rewrite the absolute value of a norm as positive norm. -/
  have abs_to_nnorm : ∀ x, ENNReal.ofReal ‖fun i ↦ f i x‖ = ‖fun i ↦ f i x‖₊ := fun x ↦ ofReal_norm_eq_coe_nnnorm fun i => f i x
  simp_rw [abs_to_nnorm]

  /- We use the property of H to rewrite the norm as a sum of norm of function in H₀ -/
  have H_norm : ∀ x, (‖fun i ↦ f i x‖₊ : ℝ≥0∞)^2 = ∑ i in range (d + 1), (‖f i x‖₊ : ℝ≥0∞)^2 := by {
    intro x
    rw [h3 f finH x]
    have sq_coe : ENNReal.some (sqrt (∑ i in range (d + 1), ‖f i x‖₊ ^ 2))^2 = ENNReal.some ((sqrt (∑ i in range (d + 1), ‖f i x‖₊ ^ 2))^2) := nn_square
    rw [sq_coe]
    simp
  }
  simp_rw [H_norm]

  /- We use the reproducing propriety of H₀ to rewrite f i x as ⟪f i, k x⟫. -/
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

  /- Coersive Cauchy-Schwarz inequality : ↑‖⟪f i, k x⟫‖₊ ≤ ↑‖f i‖₊ ↑‖f x‖₊. -/
  have cauchy_schwarz : ∀x, ∀i ∈ range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞) ≤ (‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞) := by {
    intros x i _iInRange
    have nn_cauchy := nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f i) (k x)
    have distrib : ENNReal.some (‖f i‖₊ * ‖k x‖₊) = (‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞) := coe_distrib ‖f i‖₊ ‖k x‖₊
    rw [←distrib]
    exact coe_nnreal_le nn_cauchy
  }

  /- Coersive "square" Cauchy-Schwarz inequality : (↑‖⟪f i, k x⟫‖₊)² ≤ (↑‖f i‖₊)² (↑‖f x‖₊)². -/
  have cauchy_schwarz_sq : ∀x, ∀i ∈ range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 ≤ (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 := by {
    intros x i iInRange
    have sq_dist : ((‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞))^2 = (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 := (distrib_sq (‖f i‖₊ : ℝ≥0∞) (‖k x‖₊ : ℝ≥0∞)).symm
    rw [←sq_dist]
    exact le_square (cauchy_schwarz x i iInRange)
  }

  /- If f ≤ g, ∑ i in s, f ≤ ∑ i in s, g. Thus, ∑ i in range (d + 1), (↑‖⟪f i, k x⟫‖₊)² ≤ ∑ i in range (d + 1), (↑‖f i‖)² * (↑‖k x‖₊)². -/
  have sum_le : (fun x ↦ ∑ i in range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2) ≤ (fun x ↦ ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2) := fun x ↦ sum_le_sum (cauchy_schwarz_sq x)

  /- A lower-Lebesgue integral of a finite sum is equal to a finite sum of lower-Lebesgue integral. -/
  have inverse_sum_int : ∫⁻ x in Set.univ, ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ = ∑ i in range (d + 1), ∫⁻ x in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := by {
    have is_measurable : ∀ i ∈ range (d + 1), Measurable ((fun i ↦ fun x ↦ (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2) i) := by
    {
      intros i _InRange s _h
      exact h_m_set _
    }
    exact lintegral_finset_sum (range (d + 1)) is_measurable
  }

  /- Retrieve the majorant of the finite sum : ∑ i in range (d + 1), (↑‖f i‖₊)². -/
  rcases finite_sum (fun i ↦ ‖f i‖₊^2) with ⟨C1, finite_sum⟩

  /- Retrieve the majorant of the integral ∫⁻ (x : (Vector ℝ d)) in Set.univ, ↑|k x x| ∂μ, supposed finite. -/
  rcases h2 with ⟨C2, h2⟩
  /- Rewrite ↑|k x x| as  ↑‖k x x‖₊. -/
  have abs_to_nnorm : ∀ x, ENNReal.ofReal (|k x x|) = ‖k x x‖₊ := fun x ↦ (Real.ennnorm_eq_ofReal_abs (k x x)).symm
  simp_rw [abs_to_nnorm] at h2

  /- 1. ∀ f ≤ g, ∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ. We use this lemma with *sum_le*. -/
  calc ∫⁻ (x : (Vector ℝ d)) in Set.univ, ∑ i in range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 ∂μ ≤ ∫⁻ (x : (Vector ℝ d)) in Set.univ, ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := lintegral_mono sum_le

  /- 2. Inversion sum integral. -/
  _ = ∑ i in range (d + 1), ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := inverse_sum_int

  /- 3. As (↑‖f i‖₊)² is a constant in the integral, get it out. -/
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

  /- Rewrite  (↑‖k x‖₊)² as ↑‖⟪k x, k x⟫‖₊ (lot of coercions). -/
  _ = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖⟪k x, k x⟫‖₊ : ℝ≥0∞) ∂μ := by {
    
    simp_rw [fun x ↦ nn_norm_eq_norm (k x)]

    simp_rw [fun x ↦ enn_square (norm_nonneg (k x))]

    have norm_sq_eq_inner : ∀ x, ⟪k x, k x⟫ = ‖k x‖ ^ 2 := by {
      intro x
      have tt := inner_self_eq_norm_sq_to_K (𝕜 := ℝ) (k x)
      rw [tt]
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
  
  /- Use the reproducing propriety of H₀ to write ⟪k x, k x⟫ as k x x. -/
  _ = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have reproducing_prop : ∀ x, ⟪k x, k x⟫ = k x x := by {
    intro x
    rw [h_kernel (k x) (h_k.left x) x]
    }
    simp_rw [reproducing_prop]
  }

  /- As the integral is a constant in the sum, write ∑ i in ... * ∫⁻ ... as (∑ i in ...) * ∫⁻ ... -/
  _ = (∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2) * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have sum_mul : (∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2) * (∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ) = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ) := by exact sum_mul
    rw [←sum_mul]
  }

  /- Rewrite (↑‖f i‖₊)² as ↑(‖f i‖₊²) to use the *finite_sum* lemma. -/
  _ = (∑ i in range (d + 1), (‖f i‖₊^2 : ℝ≥0∞)) * ∫⁻ (x : (Vector ℝ d)) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have coe_sq : ∀ i, (‖f i‖₊ : ℝ≥0∞)^2 = (‖f i‖₊^2 : ℝ≥0∞) := fun i ↦ nn_square
    simp_rw [coe_sq]
  }

  /- Bound the product from above using the two previously retrieved majorants. -/
  _ < C1 * C2 := ENNReal.mul_lt_mul finite_sum h2

  /- C1 C2 ∈ ℝ≥0 -/
  _ < ∞ := by {
    have h1 : C1 < ∞ := ENNReal.coe_lt_top
    have h2 : C2 < ∞ := ENNReal.coe_lt_top
    exact ENNReal.mul_lt_mul h1 h2
  }

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

/-ASSUMED LEMMAS-/
/--
  Linearity of inner product applied to integral
-/
theorem inter_inner_integral_right (μ : Measure (Vector ℝ d)) (g : (Vector ℝ d) → ℝ) (f : (Vector ℝ d) → (Vector ℝ d) → ℝ) : ⟪g, (fun x ↦ (∫ y, f y x ∂μ))⟫ = ∫ y, ⟪g, f y⟫ ∂μ :=
by
sorry

/--
  Linearity of inner product for function
-/
theorem inner_linear_left (f a b : Vector ℝ d → ℝ) (c : ℝ) : ⟪f, fun x ↦ c * a x + b x⟫ = c * ⟪f, fun x ↦ a x⟫ + ⟪f, fun x ↦ b x⟫ := by sorry

/--
⟪f, ∇k(x, ̇)⟫ = ∇f(x)
-/
theorem reproducing_derivative (f : (Vector ℝ d) → ℝ) (df' : ℕ → (Vector ℝ d) → ℝ) (hf : f ∈ H₀) : ∀x, ∀ i ∈ range (d + 1), ⟪f, dk x i⟫ = df' i x :=
by
  -- See Theorem 1 of *Derivative reproducing properties for kernel methods in learning theory*
  sorry

/--
  Linearity of inner product for function
-/
theorem inner_linear_right (f a b : ℕ → Vector ℝ d → ℝ) (c : ℝ) : ⟪fun i x ↦ c * a i x + b i x, f⟫ = c * ⟪fun i x ↦ a i x, f⟫ + ⟪fun i x ↦ b i x, f⟫ := by sorry

theorem inner_zero (a : ℕ → Vector ℝ d → ℝ) : ⟪0, a⟫ = 0 := by sorry

/-==============-/

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

  /- First, we get the integral out of the inner product. -/
  have invert_inner_integral : ∀i, ⟪(f i), (fun x ↦ (∫ y, d_log_π i y * k y x + dk y i x ∂μ))⟫ = ∫ y, ⟪(f i), (fun y x ↦ d_log_π i y * k y x + dk y i x) y⟫ ∂μ := fun i ↦ inter_inner_integral_right μ (f i) (fun y x ↦ d_log_π i y * k y x + dk y i x)
  simp_rw [invert_inner_integral]

  /- Then, we switch the integral with the finite sum using *is_integrable_H* assumption. -/
  have invert_sum_integral : ∑ i in range (d + 1), ∫ (y : Vector ℝ d), (fun i y ↦ ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫) i y ∂μ = ∫ (y : Vector ℝ d), ∑ i in range (d + 1), (fun i y ↦ ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫) i y ∂μ := by {
    symm
    exact integral_finset_sum (range (d + 1)) (by {
      intros i iin
      exact is_integrable_H ((fun i y ↦ ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫)) i iin
    })
  }
  simp_rw [invert_sum_integral]

  /- We use the linearity of inner product to develop it and get the constant d_log_π i y out. -/
  have linear_inner : ∀y, ∀i, ⟪f i, fun x ↦ d_log_π i y * k y x + dk y i x⟫ = d_log_π i y * ⟪f i, fun x ↦ k y x⟫ + ⟪f i, fun x ↦ dk y i x⟫ := fun y i ↦ inner_linear_left (f i) (k y) (dk y i) (d_log_π i y)
  simp_rw [linear_inner]

  /- We use reproducing properties of H₀ to rewrite ⟪f i, k y⟫ as f i y and ⟪f i, dk y i⟫ as df i y. -/
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
  /- We rewrite ∫ x, ∑ l in range (d + 1), ((d_log_π l x) * (f l x) + df l x) as ⟪f, ϕ⟫. -/
  rw [←inner_product_eq_dKL μ H₀ k h_kernel dk d_log_π ϕ hϕ h_is_ϕ is_integrable_H h1 h2 f hf df]

  /- We use Cauchy-Schwarz inequality. -/
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

  /- We rewrite the division as a product of inverse. -/
  have div_to_mul : ∀i, ∀x, ϕ i x / ‖ϕ‖ = ϕ i x * (1 / ‖ϕ‖) := fun i x ↦ div_eq_mul_one_div (ϕ i x) ‖ϕ‖
  simp_rw [div_to_mul]

  /- We use the linearity of the scalar product to get 1 / ‖ϕ‖ out. -/
  have linear_inner : ⟪(fun i x => ϕ i x * (1 / ‖ϕ‖)), ϕ⟫ = 1 / ‖ϕ‖ * ⟪(fun i x => ϕ i x), ϕ⟫ + ⟪(fun i x => 0), ϕ⟫ := by {
    have comm : ∀i, ∀x, (1 / ‖ϕ‖) * (ϕ i x) = (ϕ i x) * (1 / ‖ϕ‖) := fun i x ↦ mul_comm (1 / ‖ϕ‖) (ϕ i x)
    simp_rw [←comm]
    have add_zero : ⟪fun i x => 1 / ‖ϕ‖ * ϕ i x, ϕ⟫ = ⟪fun i x => 1 / ‖ϕ‖ * ϕ i x + 0, ϕ⟫ := by {simp}
    rw [add_zero]
    exact inner_linear_right ϕ ϕ (fun i x ↦ 0) (1 / ‖ϕ‖)
  }
  rw [linear_inner]

  /- We use the fact that ⟪0, f⟫ = 0. -/
  have inner_prod_zero : ⟪fun i x ↦ 0, ϕ⟫ = 0 := by {
    exact inner_zero ϕ
  }
  rw[inner_prod_zero, add_zero]

  /- We use the theorem *inner_self_eq_norm_mul_norm* stating that re ⟪a, a⟫ = ‖a‖ * ‖a‖. -/
  have eq_re : ⟪fun i x ↦ ϕ i x, ϕ⟫ = re ⟪ϕ, ϕ⟫ := by simp
  rw [eq_re]
  rw [inner_self_eq_norm_mul_norm]
  rw [Mathlib.Tactic.RingNF.mul_assoc_rev (1 / ‖ϕ‖) ‖ϕ‖ ‖ϕ‖]
  simp

/-===============================KERNEL STEIN DISCREPANCY===============================-/
/-
Here, we prove that KSD(μ | π) is a valid discrepancy measure, i.e. KSD(μ | π) = 0 ↔ μ = π.
-/

/- Def of ℝ≥0∞ coerced log. -/
noncomputable def log (a : ℝ≥0∞) := Real.log (ENNReal.toReal a)

/--
 ∀ a ∈ ]0, ∞[, exp (log a) = (a : ℝ).
-/
theorem enn_comp_exp_log (a : ℝ≥0∞) (ha : a ≠ 0) (ha2 : a ≠ ∞) : Real.exp (log a) = ENNReal.toReal a := by
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

/--
 ∀ a ∈ ]0, ∞[, log a = (c : ℝ) → a = (exp c : ℝ≥0∞).
-/
theorem cancel_log_exp (a : ℝ≥0∞) (ha : a ≠ 0) (ha2 : a ≠ ∞) (c : ℝ) : log a = c → a = ENNReal.ofReal (Real.exp c) :=
by
  intro h
  rw [←h, enn_comp_exp_log a ha ha2]
  exact Eq.symm (ofReal_toReal ha2)

/--
Definition of infinite limit at infinity for vector-valued function (we use the order of real numbers on the norm of vectors as an order on ℝᵈ).
-/
def tends_to_infty {α : Type _} [Norm α] (f : α → ℝ) := ∀ c > 0, ∃ (x : α), ∀ (x':α), ‖x‖ ≤ ‖x'‖ → c < f x
variable [Norm (Vector ℝ d)]
/--
Unformal but highly pratical multivariate integration by parts.
-/
theorem mv_integration_by_parts (f : Vector ℝ d → ℝ) (g grad_f dg : ℕ → (Vector ℝ d) → ℝ) (h : ∀ x, tends_to_infty (fun (x : Vector ℝ d) ↦ ‖x‖) → ∀i, f x * g i x = 0) : ∫ x in Set.univ, f x * (∑ i in range (d + 1), dg i x) ∂μ = - ∫ x in Set.univ, (∑ i in range (d + 1), grad_f i x * g i x) ∂μ := by sorry

/- Same as before, we will use this assumption only when the function is trivially integrable (e.g. derivative of integrable functions). -/
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

/-
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
    /- μ = π ↦ KSD(μ | π) = 0. -/
    intro h

    rw [hksd.right]

    -- /- ∑ i, f i + g i = ∑ i, f i + ∑ i, g i. -/
    have split_sum : ∀x, ∑ l in range (d + 1), (d_log_π l x * ϕ l x + dϕ l x) = (∑ l in range (d + 1), d_log_π l x * ϕ l x) + (∑ l in range (d + 1), dϕ l x) := fun x ↦ sum_add_distrib
    simp_rw [split_sum]

    /- Split the integral of sum into sum of integral. -/
    have h1 : Integrable (fun x ↦ (∑ l in range (d + 1), d_log_π l x * ϕ l x)) μ := is_integrable_H₀ _
    have h2 : Integrable (fun x ↦ (∑ l in range (d + 1), dϕ l x)) μ := is_integrable_H₀ _
    rw [integral_add (h1) h2]

    /- Make the `Set.univ` appears for using the density later. -/
    have int_univ : ∫ a, ∑ l in range (d + 1), d_log_π l a * ϕ l a ∂μ = ∫ a in Set.univ, ∑ l in range (d + 1), d_log_π l a * ϕ l a ∂μ := by simp
    rw [int_univ]

    /- Replace μ by π in the integration. -/
    rw [h]

    /- Replace by its density. -/
    rw [density_integration π ν dπ hπ (fun x ↦ (∑ l in range (d + 1), d_log_π l x * ϕ l x)) Set.univ]

    /- Get ENNReal.toReal (dπ x) in the sum (a * ∑ b = ∑ b * a). -/
    have mul_dist : ∀x, ENNReal.toReal (dπ x) * (∑ l in range (d + 1), (fun l ↦ d_log_π l x * ϕ l x) l) = ∑ l in range (d + 1), (fun l ↦ d_log_π l x * ϕ l x) l * ENNReal.toReal (dπ x) := by {
      have mul_dist_sum : ∀ (a : ℝ), ∀ (f : ℕ → ℝ), (∑ i in range (d + 1), f i) * a = ∑ i in range (d + 1), f i * a := fun a f ↦ Finset.sum_mul
      intro x
      rw [mul_comm]
      exact mul_dist_sum (ENNReal.toReal (dπ x)) (fun l ↦ d_log_π l x * ϕ l x)
    }
    simp_rw [mul_dist]

    /- Make the product ENNReal.toReal (dπ x) * d_log_π i x appears to use the log derivative rule. -/
    have mul_comm : ∀x, ∀i, d_log_π i x * ϕ i x * ENNReal.toReal (dπ x) = ENNReal.toReal (dπ x) * d_log_π i x * ϕ i x := fun x i ↦ (mul_rotate (ENNReal.toReal (dπ x)) (d_log_π i x) (ϕ i x)).symm
    simp_rw [mul_comm, hπ']

    /- Make the `Set.univ` appears to use the density. -/
    have int_univ : ∫ a, ∑ l in range (d + 1), dϕ l a ∂π = ∫ a in Set.univ, ∑ l in range (d + 1), dϕ l a ∂π := by simp
    rw [int_univ]
    rw [density_integration π ν dπ hπ (fun x ↦ (∑ l in range (d + 1), dϕ l x)) Set.univ]

    /- Use the integration by parts on the right-hand side integral. -/
    rw [mv_integration_by_parts ν (fun x ↦ ENNReal.toReal (dπ x)) ϕ dπ' dϕ (hstein)]
    simp
  }
  {
    /- KSD(μ | π) = 0 ↦ μ = π. -/
    intro h
    rw [hksd.left] at h

    /- We use the fact that the kernel is positive-definite that implies that d_log_μ_π = 0. -/
    have d_log_μ_π_eq_0 := (h_kernel_positive d_log_μ_π).right.mp h

    /- Simple derivative rule: ∂x f x = 0 → f x = c -/
    specialize hd_log_μ_π d_log_μ_π_eq_0

    rcases hd_log_μ_π with ⟨c, h⟩
    /- We show that, since dμ x / dπ x ≠ 0 and finite, dμ x = ENNReal.ofReal (Real.exp c) * dπ x. -/
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

    /- We show by cases that ENNReal.ofReal (Real.exp c) = 1. If it is ≠ 1, this implies a contradiction as dμ x = ENNReal.ofReal (Real.exp c) and ∫⁻ x, dμ x ∂ν = 1. -/
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

    /- We rewrite μ = π as ∀s, ∫⁻ x in s, dμ ∂ν = ∀s, ∫⁻ x in s, dπ ∂ν and use dμ = 1 * dπ. -/
    simp_rw [exp_c_eq_one, one_mul] at dμ_propor
    ext s _hs
    rw [←set_lintegral_one s, ←set_lintegral_one s]
    rw [density_lintegration μ ν dμ hμ, density_lintegration π ν dπ hπ]
    simp_rw [mul_one, dμ_propor]
  }




noncomputable def KL := ENNReal.ofReal (∫ x in Set.univ, log ((dμ x) / (dπ x)) ∂μ)

variable (hkl_eq : μ = π → KL μ dμ dπ = 0) (hkl_diff : μ ≠ π → 0 < KL μ dμ dπ)

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

theorem Stein_log_Sobolev (hksd : is_ksd μ π k d_log_π ϕ dϕ d_log_μ_π KSD) : ∃ θ > 0, (θ ≠ ∞) ∧ (KL μ dμ dπ ≤ (1 / (2*θ)) * ENNReal.ofReal (KSD μ π)) :=
by
by_cases μ = π
{
  rw [(KSD_is_valid_discrepancy μ π ν dμ dπ hμ hπ mdπ hdμ hdπ k h_kernel_positive d_log_π ϕ dϕ is_integrable_H₀ d_log_μ_π hd_log_μ_π dπ' hπ' KSD hstein hksd).mp h]

  rw [hkl_eq h]

  use 1
  constructor
  {simp}
  simp
}
{
  push_neg at h
  use ENNReal.ofReal (KSD μ π) / (2 * KL μ dμ dπ)
  constructor
  {

    simp

    constructor
    {
      exact μ_neq_π_imp_ksd_nn μ π ν dμ dπ hμ hπ mdπ hdμ hdπ k h_kernel_positive d_log_π ϕ dϕ is_integrable_H₀ d_log_μ_π hd_log_μ_π dπ' hπ' KSD ksd_nn hstein hksd h
    }
    {
      push_neg
      exact mul_ne_top (by simp) (ofReal_ne_top)
    }
  }

  {
    
    have KL_neq_0 : KL μ dμ dπ ≠ 0 := Iff.mp zero_lt_iff (hkl_diff h)
    constructor
    {
      have t : ENNReal.ofReal (KSD μ π) / (2 * KL μ dμ dπ) = ENNReal.ofReal (KSD μ π) * (2 * KL μ dμ dπ)⁻¹ := rfl
      rw [t]
      have enn_KSD_finite : ENNReal.ofReal (KSD μ π) ≠ ∞ := ofReal_ne_top
      have inv_KL_finite : (2 * KL μ dμ dπ)⁻¹ ≠ ∞ := by {
        have neq_zero : 2 * KL μ dμ dπ ≠ 0 := by {simp; exact KL_neq_0}
        exact inv_ne_top.mpr neq_zero
      }

      exact mul_ne_top enn_KSD_finite inv_KL_finite
    }
    {
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

      have enn_KSD_neq_0 : ENNReal.ofReal (KSD μ π) ≠ 0 := by {
        have KSD_ge_0 := μ_neq_π_imp_ksd_nn μ π ν dμ dπ hμ hπ mdπ hdμ hdπ k h_kernel_positive d_log_π ϕ dϕ is_integrable_H₀ d_log_μ_π hd_log_μ_π dπ' hπ' KSD ksd_nn hstein hksd h

        have enn_KSD_ge_0 := Iff.mpr ofReal_pos KSD_ge_0

        exact Iff.mp zero_lt_iff enn_KSD_ge_0
      }

      exact calculation (KL μ dμ dπ) (ENNReal.ofReal (KSD μ π)) (KL_neq_0) (ofReal_ne_top) (enn_KSD_neq_0) (ofReal_ne_top)
    }
  }
}

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

noncomputable def exp (a : ℝ) := ENNReal.ofReal (Real.exp a)

variable [MeasureSpace ℝ≥0] [NormedAddCommGroup ℝ≥0∞] [NormedSpace ℝ ℝ≥0∞] [LocallyFiniteOrder ℝ≥0]
variable (gronwall : ∀ (f : ℝ≥0 → ℝ), ∀ t > 0, d_KL_t t ≤ f t * ENNReal.toReal (KL (μ_t t) (dμ_t t) dπ) → KL (μ_t t) (dμ_t t) dπ ≤ KL (μ_t 0) (dμ_t 0) dπ * exp (∫ s in Icc 0 t, f s))

variable (dkl_ksd : ∀t, d_KL_t t ≤ - KSD (μ_t t) π)

lemma pos_integral (f : ℝ≥0 → ℝ≥0∞) : ∀ (t : ℝ≥0), 0 < t → 0 < ∫ s in Icc 0 t, f s := by sorry

lemma finite_integral (f : ℝ≥0 → ℝ≥0∞) : ∀ (t : ℝ≥0), ∫ s in Icc 0 t, f s ≠ ∞ := by sorry

lemma coe_integral (f : ℝ≥0 → ℝ≥0∞) : ∀ (t : ℝ≥0), ∫ s in Icc 0 t, ENNReal.toReal (f s) = ENNReal.toReal (∫ s in Icc 0 t, f s) := by sorry

lemma decomp : ∀ (a : ℝ), 0 ≤ a ∧ a ≠ 0 → 0 < a :=
by
  intros a ha
  rcases ha with ⟨pos, nneg⟩
  by_contra ht
  push_neg at ht
  have eq_zero : a = 0 := by linarith
  exact nneg eq_zero

theorem exponential_convergence_of_SVGD (hksd_t : ∀t, is_ksd (μ_t t) π k d_log_π ϕ dϕ (d_log_μ_t_π t) KSD) : ∃ (Λ : ℝ≥0 → ℝ), ∀ (t : ℝ≥0), 0 < t → (0 < Λ t) ∧ (KL (μ_t t) (dμ_t t) dπ ≤ KL (μ_t 0) (dμ_t 0) dπ * exp (-2 * Λ t)) :=
by
  have stein_log_sobolev := fun t ↦ Stein_log_Sobolev (μ_t t) π ν (dμ_t t) dπ (hμ_t t) hπ mdπ (hdμ_t t) hdπ k (h_kernel_positive_t t) d_log_π ϕ dϕ (is_integrable_H₀_t t) (d_log_μ_t_π t) (hd_log_μ_t_π t) dπ' hπ' KSD (ksd_nn_t t) hstein (hkl_eq_t t) (hkl_diff_t t) (hksd_t t)

  choose θ stein_log_sobolev using stein_log_sobolev

  use (fun t ↦ ENNReal.toReal (∫ s in Icc 0 t, θ s))

  intros t pos_t
  constructor
  {
    apply decomp _
    constructor
    {simp}
    {
      have int_ne_zero : ∫ s in Icc 0 t, θ s ≠ 0 := by {
        have pos_int := pos_integral θ t pos_t
        exact ne_of_gt pos_int
      }

      have int_finite := finite_integral θ t

      exact ENNReal.toReal_ne_zero.mpr ⟨int_ne_zero, int_finite⟩
    }
  }
  {

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

    specialize stein_log_sobolev t
    rcases stein_log_sobolev with ⟨pos_θ, finite_θ, stein_log_sobolev⟩ 

    have compute_ineq := calculation (KL (μ_t t) (dμ_t t) dπ) (ENNReal.ofReal (KSD (μ_t t) π)) (θ t) (by simp) (ne_of_gt pos_θ) (finite_θ) stein_log_sobolev

    rw [toReal_ofReal (ksd_nn_t t)] at compute_ineq

    have dkl_ineq : d_KL_t t ≤ -2 * ENNReal.toReal (θ t) * ENNReal.toReal (KL (μ_t t) (dμ_t t) dπ) := ge_trans compute_ineq (dkl_ksd t)

    specialize gronwall (fun t ↦ -2 * ENNReal.toReal (θ t)) t pos_t dkl_ineq

    rw [integral_mul_left (-2) fun a => ENNReal.toReal (θ a)] at gronwall
    
    rwa [coe_integral] at gronwall
  }