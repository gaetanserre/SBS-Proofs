import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner
namespace MeasureTheory

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace 
open BigOperators Finset ENNReal NNReal

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 5000000

variable {α : Type _} (H₀ : Set (α → ℝ)) [NormedAddCommGroup (α → ℝ)] [InnerProductSpace ℝ (α → ℝ)] [CompleteSpace (α → ℝ)] [MeasurableSpace α] [PosMulStrictMono ℝ≥0∞] [MulPosStrictMono ℝ≥0∞]

variable (k : α → α → ℝ) (h_k : (∀ (x : α), k x ∈ H₀) ∧ (∀ (x : α), (fun y => k y x) ∈ H₀))

def is_kernel := ∀ (f : α → ℝ), f ∈ H₀ → ∀ (x : α), f x = ⟪f, k x⟫

variable (h_kernel : is_kernel H₀ k)

variable {H : Set (ℕ → α → ℝ)} (d : ℕ) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] [Inner ℝ (ℕ → α → ℝ)]

def product_RKHS (H₀ : Set (α → ℝ)) (f : ℕ → α → ℝ) (_h : f ∈ H) := ∀ (i : ℕ), i ∈ range (d + 1) → f i ∈ H₀

def inner_product_H (f g : ℕ → α → ℝ) (_h : f ∈ H ∧ g ∈ H) := ⟪f, g⟫ = ∑ i in range (d + 1), ⟪f i, g i⟫

def integral_is_finite (μ : Measure α) := ∃ (C : ℝ≥0), ∫⁻ x in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ < C

lemma exist_max_finset {ι : Type _} [LinearOrder ι] (s : Finset ι) (h : Finset.Nonempty s) : ∃ e ∈ s, ∀ a ∈ s, a ≤ e := by
{
  use (Finset.max' s h)
  constructor
  {exact max'_mem s h}
  {
    intros a ains
    exact le_max_of_eq ains (Eq.symm (coe_max' h)) 
  }
}

lemma exist_max_image_finset {ι E : Type _} [LinearOrder E] (s : Finset ι) (h : Finset.Nonempty s) (f : ι → E) : ∃ j ∈ s, ∀ i ∈ s, f i ≤ f j := by 
{
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
}

lemma le_coe (a : ℝ) (b : NNReal) (h1 : 0 ≤ a) : ‖a‖₊ ≤ b → ENNReal.ofReal a ≤ ENNReal.ofReal b :=
by
intro h
have k := Real.ennnorm_eq_ofReal h1
rw [←k]
simp
exact h

lemma square_re (a : ℝ) : a * a = a^2 :=
by
symm
exact sq a

lemma square_enn (a : ℝ≥0∞) : a * a = a^2 :=
by
symm
exact sq a

lemma square_nn (a : ℝ≥0) : a * a = a^2 :=
by
symm
exact sq a

lemma le_square {a b : ℝ≥0∞} (h : a ≤ b) : a^2 ≤ b^2 :=
by
have k := mul_le_mul h h (by simp) (by simp)
rwa [←square_enn a, ←square_enn b]

lemma distrib_sq (a b : ℝ≥0∞) : a^2 * b^2 = (a * b)^2 := by {
  exact Eq.symm (mul_pow a b 2)
}

lemma coe_nnreal_le {a b : ℝ≥0} (h : a ≤ b) : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := Iff.mpr coe_le_coe h

lemma coe_distrib (a b : ℝ≥0) : ENNReal.some (a * b) = (a : ℝ≥0∞) * (b : ℝ≥0∞) := ENNReal.coe_mul


lemma finite_sum (f : ℕ → ℝ≥0) : ∃ (C : ℝ≥0), ∑ i in range (d + 1), (f i : ℝ≥0∞)^2 < ENNReal.some C := by
{
  have sup_el : ∀ i ∈ range (d + 1), ∃ c, (f i)^2 < c := fun i _ => exists_gt ((f i)^2)

  have max : ∃ j ∈ range (d+1), ∀ i ∈ range (d+1), (f i)^2 ≤ (f j)^2 := by {
    have non_empty : ∀ (n : ℕ), Finset.Nonempty (range (n+1)) := fun n => nonempty_range_succ
    have max := exist_max_image_finset (range (d+1)) (non_empty d) (fun i => (f i)^2)
    rcases max with ⟨j, jin, max⟩
    use j
    constructor
    {exact jin}
    {
      intros i iin
      exact max i iin
    }
  }

  have sup : ∃ c, ∀ i ∈ range (d + 1), (f i)^2 < c := by {
    rcases max with ⟨j, jin, max⟩
    choose C sup_el using sup_el
    use (C j jin)
    intros i iin
    specialize max i iin
    specialize sup_el j jin
    calc (f i)^2 ≤ (f j)^2 := max
    _ < C j jin := sup_el
  }

  have sup_coe : ∃ (c:ℝ≥0), ∀ (i : ℕ), i ∈ range (d + 1) → (f i : ℝ≥0∞)^2 < c := by {
    rcases sup with ⟨C, sup⟩
    use C
    intros i iin
    specialize sup i iin
    have coe_lt : ∀ (a b : ℝ≥0), (a < b) → ENNReal.some a < ENNReal.some b := by {
      intros a b h
      exact Iff.mpr coe_lt_coe h
    }
    rw [←square_enn (ENNReal.some (f i))]
    rw [←coe_distrib (f i)]
    rw [square_nn (f i)]
    exact coe_lt (f i ^ 2) C sup
  }

  rcases sup_coe with ⟨c, sup_coe⟩

  have sum_le : ∑ i in range (d + 1), (f i : ℝ≥0∞)^2 < ∑ i in range (d + 1), (c : ℝ≥0∞) := sum_lt_sum_of_nonempty (by simp) sup_coe

  have sum_coe : ∑ i in range (d + 1), (c : ℝ≥0∞) = ENNReal.some (∑ i in range (d + 1), c) := by {
    exact Eq.symm coe_finset_sum
  }

  have sum_simpl : ∑ i in range (d + 1), c = (d+1) • c := by {
    exact Eq.symm (nsmul_eq_sum_const c (d + 1))
  }

  use ((d+1) • c)

  calc ∑ i in range (d + 1), (f i: ℝ≥0∞) ^ 2 < ∑ i in range (d + 1), (c : ℝ≥0∞) := sum_le
  _ = ENNReal.some (∑ i in range (d + 1), c) := sum_coe
  _ = ENNReal.some ((d+1) • c) := by rw [sum_simpl]
}

lemma nn_norm_eq_norm (a : α → ℝ) : ‖a‖₊ = ENNReal.ofReal ‖a‖ := by {
  exact Eq.symm (ofReal_norm_eq_coe_nnnorm a)
}

lemma nn_norm_eq_norm_re (a : ℝ) : ‖a‖₊ = ENNReal.ofReal ‖a‖ := by {
  exact Eq.symm (ofReal_norm_eq_coe_nnnorm a)
}

lemma nn_square {a : ℝ} (h : 0 ≤ a) : ENNReal.ofReal (a) ^ 2 = ENNReal.ofReal (a ^ 2) :=
by {
  rw [←square_enn (ENNReal.ofReal (a)), ←square_re a]
  exact Eq.symm (ofReal_mul h)
}

variable (h_m_set : ∀ (s : Set α), MeasurableSet s)

lemma H_subset_of_L2 (μ : Measure α) (f : ℕ → α → ℝ) (h1 : f ∈ H) (h2 : inner_product_H d f f ⟨h1, h1⟩) (h3 : product_RKHS d H₀ f h1) (h4 : integral_is_finite k μ) : ∫⁻ x in Set.univ, ∑ i in range (d + 1), ENNReal.ofReal (|f i x|)^2 ∂μ < ∞ := by
{ 
  --rw [Real.ennnorm_eq_ofReal_abs (f i x)]
  have abs_to_nnorm : ∀ x, ∀ i, ENNReal.ofReal (|f i x|) = ‖f i x‖₊ := fun x i => Eq.symm (Real.ennnorm_eq_ofReal_abs (f i x))
  
  simp_rw [abs_to_nnorm]

  have rkhs : ∀ (x : α), ∑ i in range (d + 1), (‖(f i x)‖₊ : ℝ≥0∞)^2 = ∑ i in range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 := by {
    have temp : ∀ (x : α), ∀ (i : ℕ), i ∈ range (d + 1) → f i x = ⟪f i, k x⟫ := by
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

  have cauchy_schwarz : ∀x, ∀i ∈ range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞) ≤ (‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞) := by {
    intros x i _iInRange
    have nn_cauchy := nnnorm_inner_le_nnnorm (𝕜 := ℝ) (f i) (k x)
    have distrib : ENNReal.some (‖f i‖₊ * ‖k x‖₊) = (‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞) := coe_distrib ‖f i‖₊ ‖k x‖₊
    rw [←distrib]
    exact coe_nnreal_le nn_cauchy
  }

  have cauchy_schwarz_sq : ∀x, ∀i ∈ range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 ≤ (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 := by {
    intros x i iInRange
    have sq_dist : ((‖f i‖₊ : ℝ≥0∞) * (‖k x‖₊ : ℝ≥0∞))^2 = (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 := by {
      symm
      exact distrib_sq (‖f i‖₊ : ℝ≥0∞) (‖k x‖₊ : ℝ≥0∞)
    }
    rw [←sq_dist]
    exact le_square (cauchy_schwarz x i iInRange)
  }

  have sum_le : (fun x => ∑ i in range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2) ≤ (fun x => ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2) := fun x => sum_le_sum (cauchy_schwarz_sq x)

  have inverse_sum_int : ∫⁻ x in Set.univ, ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ = ∑ i in range (d + 1), ∫⁻ x in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := by {
    have is_measurable : ∀ i ∈ range (d + 1), Measurable ((fun i => fun x => (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2) i) := by
    {
      intros i _InRange s _h
      exact h_m_set _
    }
    exact lintegral_finset_sum (range (d + 1)) is_measurable
  }

  rcases finite_sum d (fun i => ‖f i‖₊) with ⟨C1, finite_sum⟩

  rcases h4 with ⟨C2, h4⟩

  calc ∫⁻ (x : α) in Set.univ, ∑ i in range (d + 1), (‖⟪f i, k x⟫‖₊ : ℝ≥0∞)^2 ∂μ ≤ ∫⁻ (x : α) in Set.univ, ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := lintegral_mono sum_le
  _ = ∑ i in range (d + 1), ∫⁻ (x : α) in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := inverse_sum_int
  _ = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : α) in Set.univ, (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := by {
    have is_measurable : Measurable (fun x => (‖k x‖₊ : ℝ≥0∞)^2) := by {
      intros s _hs
      exact h_m_set _
    }
    have const_int : ∀ i, ∫⁻ (x : α) in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ = (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : α) in Set.univ, (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := by {
      intro i
      exact lintegral_const_mul ((‖f i‖₊ : ℝ≥0∞)^2) is_measurable
    }
    simp_rw [const_int]
  }
  _ = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : α) in Set.univ, (‖⟪k x, k x⟫‖₊ : ℝ≥0∞) ∂μ := by {
    
    have coe_nnorm : ∀x, (‖k x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖k x‖ := by {
      intro x
      exact nn_norm_eq_norm (k x)
    }
    simp_rw [coe_nnorm]

    have pos : ∀x, 0 ≤ ‖k x‖ := by {
      intro x
      simp
    }

    have enn_sq : ∀x, ENNReal.ofReal ‖k x‖ ^ 2 = ENNReal.ofReal (‖k x‖ ^ 2) := by {
      intro x
      exact nn_square (pos x)
    }

    simp_rw [enn_sq]

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
  _ = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * ∫⁻ (x : α) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have reproducing_prop : ∀ x, ⟪k x, k x⟫ = k x x := by {
    intro x
    rw [h_kernel (k x) (h_k.left x) x]
    }
    simp_rw [reproducing_prop]
  }
  _ = (∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2) * ∫⁻ (x : α) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ := by {
    have sum_mul : (∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2) * (∫⁻ (x : α) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ) = ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (∫⁻ (x : α) in Set.univ, (‖k x x‖₊ : ℝ≥0∞) ∂μ) := by exact sum_mul
    rw [←sum_mul]
  }
  _ < C1 * C2 := ENNReal.mul_lt_mul finite_sum h4
  _ < ∞ := by {
    have h1 : C1 < ∞ := ENNReal.coe_lt_top
    have h2 : C2 < ∞ := ENNReal.coe_lt_top
    exact ENNReal.mul_lt_mul h1 h2
  }
}