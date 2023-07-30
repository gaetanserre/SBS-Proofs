import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Calculus.FDeriv.Basic

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

/--
  Reproducing propriety
-/
def is_kernel := ∀ (f : (Vector ℝ d) → ℝ), f ∈ H₀ → ∀ (x : (Vector ℝ d)), f x = ⟪f, k x⟫

variable (h_kernel : is_kernel d H₀ k)

/- We define the product RKHS as a space of function on (ℕ → (Vector ℝ d) → ℝ). A function belongs to such a RKHS if f = (f_1, ..., f_d) and ∀ 1 ≤ i ≤ d, fᵢ ∈ H₀. -/
variable {H : Set (ℕ → (Vector ℝ d) → ℝ)} [NormedAddCommGroup (ℕ → (Vector ℝ d) → ℝ)] [InnerProductSpace ℝ (ℕ → (Vector ℝ d) → ℝ)] [CompleteSpace (ℕ → (Vector ℝ d) → ℝ)]

def product_RKHS (H : Set (ℕ → (Vector ℝ d) → ℝ)) (H₀ : Set ((Vector ℝ d) → ℝ)) := ∀ f ∈ H, ∀ (i : ℕ), i ∈ range (d + 1) → f i ∈ H₀

def inner_product_H (H : Set (ℕ → (Vector ℝ d) → ℝ)) := ∀ f ∈ H, ∀ g ∈ H, ⟪f, g⟫ = ∑ i in range (d + 1), ⟪f i, g i⟫

variable [NormedAddCommGroup (ℕ → ℝ)] [InnerProductSpace ℝ (ℕ → ℝ)] [CompleteSpace (ℕ → ℝ)]
/--
  The simple vector norm
-/
def norm_H (H : Set (ℕ → (Vector ℝ d) → ℝ)) := ∀ f ∈ H, ∀x, (‖fun i ↦ f i x‖₊ : ℝ≥0∞) = sqrt (∑ i in range (d + 1), ‖f i x‖₊^2)

example (a : ℝ≥0) : (sqrt a)^2 = a :=
by
exact sq_sqrt a

/- Intermediate lemmas -/

/--
  For all non-empty finite set s, ∃ e ∈ s, ∀ a ∈ s, a ≤ e.
-/
lemma exist_max_finset {ι : Type _} [LinearOrder ι] (s : Finset ι) (h : Finset.Nonempty s) : ∃ e ∈ s, ∀ a ∈ s, a ≤ e :=
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
lemma exist_max_image_finset {ι E : Type _} [LinearOrder E] (s : Finset ι) (h : Finset.Nonempty s) (f : ι → E) : ∃ j ∈ s, ∀ i ∈ s, f i ≤ f j :=
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
lemma square {M : Type _} [Monoid M] (a : M) : a * a = a^2 := (sq a).symm

/--
  a² * b² = (a * b)²
-/
lemma distrib_sq {M : Type _} [CommMonoid M] (a b : M) : a^2 * b^2 = (a * b)^2 := (mul_pow a b 2).symm
/--
  ∀ a b ∈ ℝ⁺ ∪ {∞}, a ≤ b → a² ≤ b²
-/
lemma le_square {a b : ℝ≥0∞} (h : a ≤ b) : a^2 ≤ b^2 :=
by
  have k := mul_le_mul h h (by simp) (by simp)
  rwa [←square a, ←square b]

/- Coercion lemmas -/

lemma le_coe (a : ℝ) (b : NNReal) (h1 : 0 ≤ a) : ‖a‖₊ ≤ b → ENNReal.ofReal a ≤ ENNReal.ofReal b :=
by
  intro h
  have k := Real.ennnorm_eq_ofReal h1
  rw [←k]
  rwa [ENNReal.ofReal_coe_nnreal, ENNReal.coe_le_coe]

lemma coe_nnreal_le {a b : ℝ≥0} (h : a ≤ b) : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := Iff.mpr coe_le_coe h

lemma coe_distrib (a b : ℝ≥0) : ENNReal.some (a * b) = (a : ℝ≥0∞) * (b : ℝ≥0∞) := ENNReal.coe_mul

lemma nn_norm_eq_norm (a : (Vector ℝ d) → ℝ) : ‖a‖₊ = ENNReal.ofReal ‖a‖ := (ofReal_norm_eq_coe_nnnorm a).symm

lemma nn_norm_eq_norm_re (a : ℝ) : ‖a‖₊ = ENNReal.ofReal ‖a‖ := (ofReal_norm_eq_coe_nnnorm a).symm

lemma enn_square {a : ℝ} (h : 0 ≤ a) : ENNReal.ofReal (a) ^ 2 = ENNReal.ofReal (a ^ 2) :=
by
  rw [←square (ENNReal.ofReal (a)), ←square a]
  exact (ofReal_mul h).symm

lemma nn_square {a : ℝ≥0} : (a : ℝ≥0∞) ^ 2 = (a ^ 2 : ℝ≥0∞) := (ENNReal.coe_pow 2).symm

/--
  A finite sum of finite elements is finite.
-/
lemma finite_sum (f : ℕ → ℝ≥0) : ∃ (C : ℝ≥0), ∑ i in range (d + 1), (f i : ℝ≥0∞) < ENNReal.some C :=
by
  /- We begin to show that each element of the sum is bounded from above. -/
  have sup_el : ∀ i ∈ range (d + 1), ∃ c, (f i) < c := fun i _ ↦ exists_gt (f i)

  /- We find the argmax of the set {f i | ∀ i ∈ range (d + 1)} using the *exist_max_image_finset* lemma. -/
  have max : ∃ j ∈ range (d+1), ∀ i ∈ range (d+1), f i ≤ f j := by {
    have non_empty : ∀ (n : ℕ), Finset.Nonempty (range (n+1)) := fun n ↦ nonempty_range_succ
    have max := exist_max_image_finset (range (d+1)) (non_empty d) (fun i ↦ f i)
    rcases max with ⟨j, jin, max⟩
    use j
    constructor
    {exact jin}
    {
      intros i iin
      exact max i iin
    }
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

variable (h_m_set : ∀ (s : Set (Vector ℝ d)), MeasurableSet s)

def integral_is_finite (μ : Measure (Vector ℝ d)) (f : (Vector ℝ d) → ℝ) := ∃ (C : ℝ≥0), ∫⁻ x in Set.univ, ENNReal.ofReal |f x| ∂μ < C

/--
  H ⊆ L2(μ) i.e., ∀ f ∈ H ∫⁻ x in Set.univ, ∑ i in range (d + 1), ENNReal.ofReal (|f i x|)^2 ∂μ < ∞.
-/
example (f : ℕ → (Vector ℝ d) → ℝ) (x : (Vector ℝ d)) : ENNReal.ofReal ‖fun i ↦ f i x‖ = ‖fun i ↦ f i x‖₊ := ofReal_norm_eq_coe_nnnorm fun i => f i x

theorem H_subset_of_L2 (μ : Measure (Vector ℝ d)) (h1 : product_RKHS d H H₀) (h2 : integral_is_finite d μ (fun x ↦ k x x)) (h3 : norm_H d H) : ∀ f ∈ H, ∫⁻ x in Set.univ, ENNReal.ofReal ‖fun i ↦ f i x‖^2 ∂μ < ∞ :=
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

  /- A lower-Lebesgue integral of a finite sum is equal toa finite sum of lower-Lebesgue integral. -/
  have inverse_sum_int : ∫⁻ x in Set.univ, ∑ i in range (d + 1), (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ = ∑ i in range (d + 1), ∫⁻ x in Set.univ, (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2 ∂μ := by {
    have is_measurable : ∀ i ∈ range (d + 1), Measurable ((fun i ↦ fun x ↦ (‖f i‖₊ : ℝ≥0∞)^2 * (‖k x‖₊ : ℝ≥0∞)^2) i) := by
    {
      intros i _InRange s _h
      exact h_m_set _
    }
    exact lintegral_finset_sum (range (d + 1)) is_measurable
  }

  /- Retrieve the majorant of the finite sum : ∑ i in range (d + 1), (↑‖f i‖₊)². -/
  rcases finite_sum d (fun i ↦ ‖f i‖₊^2) with ⟨C1, finite_sum⟩

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
    
    simp_rw [fun x ↦ nn_norm_eq_norm d (k x)]

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