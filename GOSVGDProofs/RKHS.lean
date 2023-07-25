import Mathlib
namespace MeasureTheory

open scoped RealInnerProductSpace 
open BigOperators Finset ENNReal

set_option trace.Meta.Tactic.simp.rewrite true

variable {α : Type _} (H₀ : Set (α → ℝ)) (hn : NormedAddCommGroup (α → ℝ)) (hr : isRorC ℝ) (hi : InnerProductSpace ℝ (α → ℝ)) [CompleteSpace (α → ℝ)] [Inner ℝ (α → ℝ)] [MeasurableSpace α] [PosMulStrictMono ℝ≥0∞] [MulPosStrictMono ℝ≥0∞]

variable (k : α → α → ℝ) (h_k : (∀ (x : α), k x ∈ H₀) ∧ (∀ (x : α), (fun y => k y x) ∈ H₀))

def is_kernel := ∀ (f : α → ℝ), f ∈ H₀ → ∀ (x : α), f x = ⟪f, k x⟫

variable (h_kernel : is_kernel H₀ k)

variable {H : Set (ℕ → α → ℝ)} (d : ℕ) (h_d : coe d ≠ (0 : ℝ)) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Inner ℝ (ℕ → α → ℝ)]

def product_RKHS (H₀ : Set (α → ℝ)) (f : ℕ → α → ℝ) (_h : f ∈ H) := ∀ (i : ℕ), i ∈ range d → f i ∈ H₀

def inner_product_H (f g : ℕ → α → ℝ) (_h : f ∈ H ∧ g ∈ H) := ⟪f, g⟫ = ∑ i in range d, ⟪f i, g i⟫

def integral_is_finite (μ : Measure α) := ∃ C, ∫⁻ x in Set.univ, ENNReal.ofReal (k x x) ∂μ ≤ C ∧ C < ∞

lemma finite_sum (f : ℕ → NNReal) : ∃ C, ∑ i in range d, ENNReal.ofReal (f i^2) ≤ C ∧ C < ∞ := by sorry


variable (h_m_set : ∀ (s : Set α), MeasurableSet s)

lemma H_subset_of_L2 (μ : Measure α) (f : ℕ → α → ℝ) (h1 : f ∈ H) (h2 : inner_product_H d f f ⟨h1, h1⟩) (h3 : product_RKHS d H₀ f h1) (h4 : integral_is_finite k μ) : ∫⁻ x in Set.univ, ∑ i in range d, ENNReal.ofReal (f i x)^2 ∂μ < ∞ :=
by

have rkhs : ∀ (x : α), ∑ i in range d, ENNReal.ofReal (f i x)^2 = ∑ i in range d, ENNReal.ofReal ⟪f i, k x⟫^2 := by {
  have temp : ∀ (x : α), ∀ (i : ℕ), i ∈ range d → f i x = ⟪f i, k x⟫ := by
  {
    intros x i iInRange
    apply h_kernel
    exact h3 i iInRange
  }
  intro x
  apply sum_congr (Eq.refl _)
  intros i iInRange
  rw [temp x i iInRange]
}

simp_rw [rkhs]

have sum_le : (fun x => ∑ i in range d, ENNReal.ofReal ⟪f i, k x⟫^2) ≤ (fun x => ∑ i in range d, ENNReal.ofReal (‖f i‖₊^2 * ‖k x‖₊^2)) := by
{
  have smaller_el : ∀ (x : α), ∀ (i : ℕ), i ∈ range d → ENNReal.ofReal ⟪f i, k x⟫^2 ≤ ENNReal.ofReal (‖f i‖₊^2 * ‖k x‖₊^2) := by
  {
    intros x i iInRange
    exact norm_inner_le_norm hr hn hi (f i) (k x)
  }

  intro x
  exact sum_le_sum (smaller_el x)
}

have inverse_sum_int : ∫⁻ x in Set.univ, ∑ i in range d, ENNReal.ofReal (‖f i‖₊^2 * ‖k x‖₊^2) ∂μ = ∑ i in range d, ∫⁻ x in Set.univ, ENNReal.ofReal (‖f i‖₊^2 * ‖k x‖₊^2) ∂μ := by
{
  have is_measurable : ∀ i ∈ range d, Measurable ((fun i => fun x => ENNReal.ofReal (‖f i‖₊^2 * ‖k x‖₊^2)) i) := by
  {
    intros i InRange s _h
    exact h_m_set _
  }

  exact lintegral_finset_sum (range d) is_measurable
}

rcases finite_sum d (fun i => ‖f i‖₊)  with ⟨C1, finite_sum⟩
rcases h4 with ⟨C2, h4⟩

calc ∫⁻ (x : α) in Set.univ, ∑ i in range d, ENNReal.ofReal (inner (f i) (k x))^2 ∂μ ≤ ∫⁻ (x : α) in Set.univ, ∑ i in range d, ENNReal.ofReal (‖f i‖₊^2 * ‖k x‖₊^2) ∂μ := lintegral_mono sum_le
_ = ∑ i in range d, ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖f i‖₊^2 * ‖k x‖₊^2) ∂μ := inverse_sum_int
_ = ∑ i in range d, ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖f i‖₊^2) * ENNReal.ofReal (‖k x‖₊^2) ∂μ := by {
  have f_pos : ∀ i, 0 ≤ NNReal.toReal ‖f i‖₊^2 := by simp
  have coercion : ∀ i, ∀ x, ENNReal.ofReal (‖f i‖₊^2 * ‖k x‖₊^2) = ENNReal.ofReal (‖f i‖₊^2) * ENNReal.ofReal (‖k x‖₊^2) := by {
    intros i x
    exact ofReal_mul (f_pos i)
  }
  simp_rw [coercion]
}
_ = ∑ i in range d, ENNReal.ofReal (‖f i‖₊^2) * ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖k x‖₊^2) ∂μ := by {
  have is_measurable : Measurable (fun x => ENNReal.ofReal (‖k x‖₊^2)) := by {
    intros s _hs
    exact h_m_set _
  }
  have const_int : ∀ i, ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖f i‖₊^2) * ENNReal.ofReal (‖k x‖₊^2) ∂μ = ENNReal.ofReal (‖f i‖₊^2) * ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖k x‖₊^2) ∂μ := by {
    intro i
    exact lintegral_const_mul (ENNReal.ofReal (‖f i‖₊^2)) is_measurable
  }
  simp_rw [const_int]
}
_ = ∑ i in range d, ENNReal.ofReal (‖f i‖₊^2) * ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (⟪k x, k x⟫) ∂μ := by {
  have norm_sq_eq_inner : ∀ x, ‖k x‖₊^2 = ⟪k x, k x⟫ := by {
    intro x
    exact inner_self_eq_norm_sq_to_K hr hn hi (k x)
  }
  simp_rw [norm_sq_eq_inner]
}
_ = ∑ i in range d, ENNReal.ofReal (‖f i‖₊^2) * ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (k x x) ∂μ := by {
  have reproducing_prop : ∀ x, ⟪k x, k x⟫ = k x x := by {
    intro x
    rw [h_kernel (k x) (h_k.left x) x]
  }
  simp_rw [reproducing_prop]
}
_ =  (∑ i in range d, ENNReal.ofReal (‖f i‖₊^2)) * (∫⁻ (x : α) in Set.univ, ENNReal.ofReal (k x x) ∂μ)  := by 
{
  have sum_mul : (∑ i in range d, ENNReal.ofReal (‖f i‖₊^2)) * (∫⁻ (x : α) in Set.univ, ENNReal.ofReal (k x x) ∂μ) = ∑ i in range d, (ENNReal.ofReal (‖f i‖₊^2)) * (∫⁻ (x : α) in Set.univ, ENNReal.ofReal (k x x) ∂μ) := by exact sum_mul
  rw [←sum_mul]
}
_ ≤ C1 * C2 := mul_le_mul finite_sum.left h4.left (by simp) (by simp)

_ < ∞ := by {
  have infty_mul_infty : ∞ * ∞ = ∞ := by simp
  rw [←infty_mul_infty]
  exact mul_lt_mul_of_nonneg_of_pos finite_sum.right ((le_not_le_of_lt h4.right).left) (by simp) (by simp)
}