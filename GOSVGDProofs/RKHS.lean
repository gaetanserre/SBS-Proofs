import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner
namespace MeasureTheory

open scoped RealInnerProductSpace 
open BigOperators Finset ENNReal NNReal

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 5000000

variable {α : Type _} (H₀ : Set (α → ℝ)) [NormedAddCommGroup (α → ℝ)] [InnerProductSpace ℝ (α → ℝ)] [CompleteSpace (α → ℝ)] [MeasurableSpace α] [PosMulStrictMono ℝ≥0∞] [MulPosStrictMono ℝ≥0∞]

variable (k : α → α → ℝ) (h_k : (∀ (x : α), k x ∈ H₀) ∧ (∀ (x : α), (fun y => k y x) ∈ H₀))

def is_kernel := ∀ (f : α → ℝ), f ∈ H₀ → ∀ (x : α), f x = ⟪f, k x⟫

variable (h_kernel : is_kernel H₀ k)

variable {H : Set (ℕ → α → ℝ)} (d : ℕ) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Inner ℝ (ℕ → α → ℝ)]

def product_RKHS (H₀ : Set (α → ℝ)) (f : ℕ → α → ℝ) (_h : f ∈ H) := ∀ (i : ℕ), i ∈ range d → f i ∈ H₀

def inner_product_H (f g : ℕ → α → ℝ) (_h : f ∈ H ∧ g ∈ H) := ⟪f, g⟫ = ∑ i in range d, ⟪f i, g i⟫

def integral_is_finite (μ : Measure α) := ∃ C, ∫⁻ x in Set.univ, ENNReal.ofReal (k x x) ∂μ ≤ C ∧ C < ∞

lemma finite_sum (f : ℕ → ℝ) : ∃ C, ∑ i in range d, ENNReal.ofReal (f i^2) ≤ C ∧ C < ∞ := by
--ofReal_sum_of_nonneg
sorry

lemma le_coe (a : ℝ) (b : NNReal) (h1 : 0 ≤ a) : ‖a‖₊ ≤ b → ENNReal.ofReal a ≤ ENNReal.ofReal b :=
by
intro h
have k := Real.ennnorm_eq_ofReal h1
rw [←k]
simp
exact h

example (a : ℝ) : ‖a‖₊ = |a| :=
by
simp

lemma square (a : ℝ≥0∞) : a * a = a^2 :=
by
symm
exact sq a

lemma le_square {a b : ℝ≥0∞} (h : a ≤ b) : a^2 ≤ b^2 :=
by
have k := mul_le_mul h h (by simp) (by simp)
rwa [←square a, ←square b]

lemma distrib_sq (a b : ℝ≥0∞) : a^2 * b^2 = (a * b)^2 := by {
  exact Eq.symm (mul_pow a b 2)
}

lemma coe_nnreal_le {a b : ℝ≥0} (h : a ≤ b) : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := Iff.mpr coe_le_coe h

lemma coe_distrib (a b : ℝ≥0) : ENNReal.some (a * b) = (a : ℝ≥0∞) * (b : ℝ≥0∞) := ENNReal.coe_mul

lemma pos_integral (C : ℝ) (f : α → ℝ) (h : ∀x, 0 ≤ f x) (s : Set α) : ∫⁻ x in s, ENNReal.ofReal (f x) ∂μ < ENNReal.ofReal C → ∫ x in s, f x ∂μ < C := by sorry


/- lemma test (f : ℕ → ℝ) (h : ∀ i, 0 ≤ f i) (s : Finset ℕ) : 0 ≤ ∑ i in s, f i := by
exact sum_nonneg' h

lemma dist_sq (a b : ℝ) : (a * b)^2 = a^2 * b^2 := by
{
  sorry
} -/


example (a : NNReal) : a^2 = 0 := by

sorry

variable (h_m_set : ∀ (s : Set α), MeasurableSet s)

lemma H_subset_of_L2 (μ : Measure α) (f : ℕ → α → ℝ) (h1 : f ∈ H) (h2 : inner_product_H d f f ⟨h1, h1⟩) (h3 : product_RKHS d H₀ f h1) (h4 : integral_is_finite k μ) : ∫⁻ x in Set.univ, ∑ i in range d, (‖(f i x)‖₊ : ℝ≥0∞)^2 ∂μ < ∞ := by
{ 

  have rkhs : ∀ (x : α), ∑ i in range d, (‖(f i x)‖₊ : ℝ≥0∞)^2 = ∑ i in range d, (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 := by {
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

  have cauchy_schwarz : ∀x, ∀i ∈ range d, (‖⟪f i, k x⟫‖₊ : ℝ≥0∞) ≤ (‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞) := by {
    intros x i iInRange
    have nn_cauchy := nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f i) (k x)
    have distrib : ENNReal.some (‖f i‖₊ * ‖k x‖₊) = (‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞) := coe_distrib ‖f i‖₊ ‖k x‖₊
    rw [←distrib]
    exact coe_nnreal_le nn_cauchy
  }

  have cauchy_schwarz_sq : ∀x, ∀i ∈ range d, (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 ≤ (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 := by {
    intros x i iInRange
    have sq_dist : ((‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞))^2 = (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 := by {
      symm
      exact distrib_sq (‖f i‖₊ : ℝ≥0∞) (‖k x‖₊ : ℝ≥0∞)
    }
    rw [←sq_dist]
    exact le_square (cauchy_schwarz x i iInRange)
  }

  have sum_le : (fun x => ∑ i in range d, (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2) ≤ (fun x => ∑ i in range d, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2) := by {
    intro x
    exact sum_le_sum (cauchy_schwarz_sq x)
  }

  have inverse_sum_int : ∫⁻ x in Set.univ, ∑ i in range d, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ = ∑ i in range d, ∫⁻ x in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := by {
    have is_measurable : ∀ i ∈ range d, Measurable ((fun i => fun x => (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2) i) := by
    {
      intros i InRange s _h
      exact h_m_set _
    }
    exact lintegral_finset_sum (range d) is_measurable
  }

  sorry
}



/- lemma H_subset_of_L2 (μ : Measure α) (f : ℕ → α → ℝ) (h1 : f ∈ H) (h2 : inner_product_H d f f ⟨h1, h1⟩) (h3 : product_RKHS d H₀ f h1) (h4 : integral_is_finite k μ) : ∫ x in Set.univ, ∑ i in range d, |(f i x)|^2 ∂μ < ENNReal.toReal ∞ :=
by

have rkhs : ∀ (x : α), ∑ i in range d, |(f i x)|^2 = ∑ i in range d, |⟪f i, k x⟫|^2 := by {
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

have sum_le : (fun x => ∑ i in range d, |⟪f i, k x⟫|^2) ≤ (fun x => ∑ i in range d, NNReal.toReal (‖f i‖₊) ^ 2 * NNReal.toReal (↑‖k x‖₊) ^ 2) := by
{
  have cauchy_schwarz :  ∀ (x : α), ∀ (i : ℕ), i ∈ range d → ‖⟪f i, k x⟫‖₊ ≤ ‖f i‖₊ * ‖k x‖₊ := by {intros x i iInRange; exact nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f i) (k x)}

  have coercion : ∀ x, ∀ i, ‖⟪f i, k x⟫‖₊ = |⟪f i, k x⟫| := by {
    intros x i
    simp
  }
  simp_rw [←coercion]

  have coercion_le : ∀ (x : α), ∀ (i : ℕ), i ∈ range d → NNReal.toReal ‖⟪f i, k x⟫‖₊^2 ≤ NNReal.toReal (‖f i‖₊)^2 *  NNReal.toReal (‖k x‖₊)^2 := by {
    have temp : ∀ (a b : NNReal), a ≤ b → NNReal.toReal a ≤ NNReal.toReal b := by simp
    intros x i iInRange
    have test := le_square (NNReal.toReal ‖⟪f i, k x⟫‖₊) (NNReal.toReal (‖f i‖₊) * NNReal.toReal (‖k x‖₊)) (by simp) (NNReal.coe_nonneg (‖f i‖₊ * ‖k x‖₊)) (cauchy_schwarz x i iInRange)
    rwa [←dist_sq (NNReal.toReal (‖f i‖₊)) (NNReal.toReal (‖k x‖₊))]
  }

  intro x
  
  exact sum_le_sum (coercion_le x)

  /- have smaller_el : ∀ (x : α), ∀ (i : ℕ), i ∈ range d → ENNReal.ofReal |⟪f i, k x⟫|^2 ≤ ENNReal.ofReal (‖f i‖^2 * ‖k x‖^2) := by
  {
    intros x i iInRange
    have kk : ‖ ⟪f i, k x⟫ ‖₊ ≤ ‖f i‖₊ * ‖k x‖₊ := nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f i) (k x)
    have kkk : ‖ ⟪f i, k x⟫ ‖₊ = ‖ |⟪f i, k x⟫| ‖₊ := by simp
    rw [kkk] at kk
    have kkkk := le_coe |⟪f i, k x⟫| (‖f i‖₊ * ‖k x‖₊) (by simp) kk
    have t := le_square (ENNReal.ofReal |inner (f i) (k x)|) (ENNReal.ofReal (‖f i‖₊ * ‖k x‖₊)) (by simp) (by simp) kkkk
    sorry
  }

  intro x
  exact sum_le_sum (smaller_el x) -/
}

apply pos_integral
{
  intro x
  have pos : ∀i, 0 ≤ |⟪f i, k x⟫|^2 := by {
    intro i
    rw [←square |⟪f i, k x⟫|]
    exact mul_self_nonneg _
  }
  exact sum_nonneg' pos
}

have ennreal_compose : ENNReal.ofReal (ENNReal.toReal ∞) = ∞ := by sorry
rw [ennreal_compose]

have inverse_sum_int : ∫⁻ x in Set.univ, ∑ i in range d, ENNReal.ofReal (‖f i‖^2 * ‖k x‖^2) ∂μ = ∑ i in range d, ∫⁻ x in Set.univ, ENNReal.ofReal (‖f i‖^2 * ‖k x‖^2) ∂μ := by
{
  have is_measurable : ∀ i ∈ range d, Measurable ((fun i => fun x => ENNReal.ofReal (‖f i‖^2 * ‖k x‖^2)) i) := by
  {
    intros i InRange s _h
    exact h_m_set _
  }

  exact lintegral_finset_sum (range d) is_measurable
}

rcases finite_sum d (fun i => ‖f i‖)  with ⟨C1, finite_sum⟩
rcases h4 with ⟨C2, h4⟩


have test {a b : ℝ} : a ≤ b → ENNReal.ofReal a ≤ ENNReal.ofReal a := by {
  intros hab
  exact Eq.ge rfl
}

have test2 : ∀ x, ∑ i in range d, ENNReal.ofReal (|inner (f i) (k x)| ^ 2) = ENNReal.ofReal (∑ i in range d, |inner (f i) (k x)| ^ 2) := by {
  intro x
  have pos : ∀ i ∈ range d, 0 ≤ |⟪f i, k x⟫| ^ 2 := by {
    intro i iInRange
    rw [←square |⟪f i, k x⟫|]
    exact mul_self_nonneg _
  }
  symm
  exact ofReal_sum_of_nonneg pos
}

have test3 : ∀ x, ∑ i in range d, ENNReal.ofReal (↑‖f i‖₊ ^ 2 * ↑‖k x‖₊ ^ 2) = ENNReal.ofReal (∑ i in range d, ENNReal.toReal (‖f i‖₊) ^ 2 * ENNReal.toReal (‖k x‖₊) ^ 2) := by {
  intro x
  have pos : ∀ i ∈ range d, 0 ≤ ENNReal.toReal (‖f i‖₊) ^ 2 * ENNReal.toReal (‖k x‖₊) ^ 2 := by {
    intro i iInRange
    --exact zero_le (ENNReal.toReal (‖f i‖₊) ^ 2 * ENNReal.toReal (‖k x‖₊) ^ 2)
    sorry
  }
  symm
  exact ofReal_sum_of_nonneg pos
}

have sum_le : (fun x => ∑ i in range d, ENNReal.ofReal (|inner (f i) (k x)|^2)) ≤ fun x => ∑ i in range d, ENNReal.ofReal (↑‖f i‖₊ ^ 2 * ↑‖k x‖₊ ^ 2) := by {
  intro x
  simp_rw [test2, test3]
  exact test sum_le
}


calc ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (∑ i in range d, |inner (f i) (k x)| ^ 2) ∂μ = ∫⁻ (x : α) in Set.univ, ∑ i in range d, ENNReal.ofReal |inner (f i) (k x)|^2 ∂μ := by sorry
_ ≤ ∫⁻ (x : α) in Set.univ, ∑ i in range d, ENNReal.ofReal (‖f i‖₊^2 * ‖k x‖₊^2) ∂μ := lintegral_mono sum_le
_ = ∑ i in range d, ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖f i‖^2 * ‖k x‖^2) ∂μ := inverse_sum_int
_ = ∑ i in range d, ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖f i‖^2) * ENNReal.ofReal (‖k x‖^2) ∂μ := by {
  have f_pos : ∀ i, 0 ≤ ‖f i‖^2 := by simp
  have coercion : ∀ i, ∀ x, ENNReal.ofReal (‖f i‖^2 * ‖k x‖^2) = ENNReal.ofReal (‖f i‖^2) * ENNReal.ofReal (‖k x‖^2) := by {
    intros i x
    exact ofReal_mul (f_pos i)
  }
  simp_rw [coercion]
}
_ = ∑ i in range d, ENNReal.ofReal (‖f i‖^2) * ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖k x‖^2) ∂μ := by {
  have is_measurable : Measurable (fun x => ENNReal.ofReal (‖k x‖^2)) := by {
    intros s _hs
    exact h_m_set _
  }
  have const_int : ∀ i, ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖f i‖^2) * ENNReal.ofReal (‖k x‖^2) ∂μ = ENNReal.ofReal (‖f i‖^2) * ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (‖k x‖^2) ∂μ := by {
    intro i
    exact lintegral_const_mul (ENNReal.ofReal (‖f i‖^2)) is_measurable
  }
  simp_rw [const_int]
}
_ = ∑ i in range d, ENNReal.ofReal (‖f i‖^2) * ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (⟪k x, k x⟫) ∂μ := by {
  have norm_sq_eq_inner : ∀ x, ‖k x‖^2 = ⟪k x, k x⟫ := by {
    intro x
    exact inner_self_eq_norm_sq_to_K hr hn hi (k x)
  }
  simp_rw [norm_sq_eq_inner]
}
_ = ∑ i in range d, ENNReal.ofReal (‖f i‖^2) * ∫⁻ (x : α) in Set.univ, ENNReal.ofReal (k x x) ∂μ := by {
  have reproducing_prop : ∀ x, ⟪k x, k x⟫ = k x x := by {
    intro x
    rw [h_kernel (k x) (h_k.left x) x]
  }
  simp_rw [reproducing_prop]
}
_ =  (∑ i in range d, ENNReal.ofReal (‖f i‖^2)) * (∫⁻ (x : α) in Set.univ, ENNReal.ofReal (k x x) ∂μ)  := by 
{
  have sum_mul : (∑ i in range d, ENNReal.ofReal (‖f i‖^2)) * (∫⁻ (x : α) in Set.univ, ENNReal.ofReal (k x x) ∂μ) = ∑ i in range d, (ENNReal.ofReal (‖f i‖^2)) * (∫⁻ (x : α) in Set.univ, ENNReal.ofReal (k x x) ∂μ) := by exact sum_mul
  rw [←sum_mul]
}
_ ≤ C1 * C2 := mul_le_mul finite_sum.left h4.left (by simp) (by simp)

_ < ∞ := by {
  have infty_mul_infty : ∞ * ∞ = ∞ := by simp
  rw [←infty_mul_infty]
  exact mul_lt_mul_of_nonneg_of_pos finite_sum.right ((le_not_le_of_lt h4.right).left) (by simp) (by simp)
} -/