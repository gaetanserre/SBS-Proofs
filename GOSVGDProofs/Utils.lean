import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner

open scoped RealInnerProductSpace
open Finset ENNReal NNReal BigOperators MeasureTheory

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

variable [NormedAddCommGroup ((Vector ℝ d) → ℝ)] [InnerProductSpace ℝ ((Vector ℝ d) → ℝ)]
variable [NormedAddCommGroup (ℕ → (Vector ℝ d) → ℝ)] [InnerProductSpace ℝ (ℕ → (Vector ℝ d) → ℝ)] [MeasurableSpace (Vector ℝ d)]

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
theorem reproducing_derivative (H₀ : Set ((Vector ℝ d) → ℝ)) (dk : Vector ℝ d → ℕ → Vector ℝ d → ℝ) (f : (Vector ℝ d) → ℝ) (df' : ℕ → (Vector ℝ d) → ℝ) (hf : f ∈ H₀) : ∀x, ∀ i ∈ range (d + 1), ⟪f, dk x i⟫ = df' i x :=
by
  -- See Theorem 1 of *Derivative reproducing properties for kernel methods in learning theory*
  sorry

/--
  Linearity of inner product for function
-/
theorem inner_linear_right (f a b : ℕ → Vector ℝ d → ℝ) (c : ℝ) : ⟪fun i x ↦ c * a i x + b i x, f⟫ = c * ⟪fun i x ↦ a i x, f⟫ + ⟪fun i x ↦ b i x, f⟫ := by sorry

theorem inner_zero (a : ℕ → Vector ℝ d → ℝ) : ⟪0, a⟫ = 0 := by sorry

variable [MeasureSpace ℝ≥0] [NormedAddCommGroup ℝ≥0∞] [NormedSpace ℝ ℝ≥0∞] [LocallyFiniteOrder ℝ≥0]

lemma pos_integral (f : ℝ≥0 → ℝ≥0∞) : ∀ (t : ℝ≥0), 0 < t → (∀ s, 0 < f s) → 0 < ∫ s in Icc 0 t, f s := by sorry

lemma finite_integral (f : ℝ≥0 → ℝ≥0∞) : ∀ (t : ℝ≥0), (∀ s, f s ≠ ∞) → ∫ s in Icc 0 t, f s ≠ ∞ := by sorry

lemma coe_integral (f : ℝ≥0 → ℝ≥0∞) : ∀ (t : ℝ≥0), ∫ s in Icc 0 t, ENNReal.toReal (f s) = ENNReal.toReal (∫ s in Icc 0 t, f s) := by sorry

/-==============-/


/- Def of ℝ≥0∞ coerced log. -/
noncomputable def log (a : ℝ≥0∞) := Real.log (ENNReal.toReal a)

noncomputable def KL {α : Type _} [MeasurableSpace α] (μ : Measure α) (dμ dπ : α → ℝ≥0∞) := ENNReal.ofReal (∫ x in Set.univ, log ((dμ x) / (dπ x)) ∂μ)

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


noncomputable def exp (a : ℝ) := ENNReal.ofReal (Real.exp a)

lemma lt_eq_le_and_neq : ∀ (a : ℝ), 0 ≤ a ∧ a ≠ 0 ↔ 0 < a :=
by
  intro a
  constructor
  {
    intro ha
    rcases ha with ⟨pos, nneg⟩
    by_contra ht
    push_neg at ht
    have eq_zero : a = 0 := by linarith
    exact nneg eq_zero
  }
  {
    intro ha
    exact ⟨le_of_lt ha, ne_of_gt ha⟩
  }