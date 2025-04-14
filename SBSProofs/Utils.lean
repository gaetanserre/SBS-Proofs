/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.Bochner.VitaliCaratheodory

open scoped RealInnerProductSpace
open Finset ENNReal NNReal BigOperators MeasureTheory

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

variable {α : Type*}

variable [NormedAddCommGroup (α → ℝ)] [InnerProductSpace ℝ (α → ℝ)]
variable [MeasurableSpace α]

/--
  For all non-empty finite set s, ∃ e ∈ s, ∀ a ∈ s, a ≤ e.
-/
theorem exist_max_finset {ι : Type*} [LinearOrder ι] (s : Finset ι) (h : Finset.Nonempty s) : ∃ e ∈ s, ∀ a ∈ s, a ≤ e :=
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
theorem exist_max_image_finset {ι E : Type*} [LinearOrder E] (s : Finset ι) (h : Finset.Nonempty s) (f : ι → E) : ∃ j ∈ s, ∀ i ∈ s, f i ≤ f j :=
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
  a² * b² = (a * b)²
-/
lemma distrib_sq {M : Type*} [CommMonoid M] (a b : M) : a^2 * b^2 = (a * b)^2 := (mul_pow a b 2).symm
/--
  ∀ a b ∈ ℝ⁺ ∪ {∞}, a ≤ b → a² ≤ b²
-/
lemma le_square {a b : ℝ≥0∞} (h : a ≤ b) : a^2 ≤ b^2 :=
by
  have k := mul_le_mul h h (by simp) (by simp)
  rwa [pow_two a, pow_two b]

/- Coercion lemmas -/

lemma coe_nnreal_le {a b : ℝ≥0} (h : a ≤ b) : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := Iff.mpr coe_le_coe h

lemma nn_norm_eq_norm {α : Type*} [NormedAddCommGroup α] [InnerProductSpace ℝ α] (a : α) : ‖a‖₊ = ENNReal.ofReal ‖a‖ := (ofReal_norm_eq_enorm a).symm

lemma nn_norm_eq_norm_re (a : ℝ) : ‖a‖₊ = ENNReal.ofReal ‖a‖ := (ofReal_norm_eq_enorm a).symm

lemma enn_square {a : ℝ} (h : 0 ≤ a) : ENNReal.ofReal (a) ^ 2 = ENNReal.ofReal (a ^ 2) :=
by
  rw [pow_two (ENNReal.ofReal (a)), pow_two a]
  exact (ofReal_mul h).symm


variable {d : ℕ} (hd : d ≠ 0)
include hd in

/-ASSUMED LEMMAS-/
/--
  Linearity of inner product applied to integral
-/
lemma inter_inner_integral_right (μ : Measure α) [IsFiniteMeasure μ] (g : α → ℝ) (f : α → α → ℝ) : ⟪g, (λ x ↦ (∫ y, f y x ∂μ))⟫ = ∫ y, ⟪g, f y⟫ ∂μ :=
by
sorry

/--
  Linearity of inner product for function
-/
lemma inner_linear_left (f a b : α → ℝ) (c : ℝ) : ⟪f, λ x ↦ c * a x + b x⟫ = c * ⟪f, λ x ↦ a x⟫ + ⟪f, λ x ↦ b x⟫ := by sorry

/--
  ⟪f, ∇k(x, ̇)⟫ = ∇f(x)
-/
lemma reproducing_derivative (H₀ : Set (α → ℝ)) (dk : α → ℕ → α → ℝ) (f : α → ℝ) (df' : ℕ → α → ℝ) (hf : f ∈ H₀) : ∀x, ∀ i ∈ range d, ⟪f, dk x i⟫ = df' i x :=
by
  -- See Theorem 1 of *Derivative reproducing properties for kernel methods in learning theory, Zhou 2008*.
  sorry

/-==============-/

/- Def of ℝ≥0∞ coerced log. -/
noncomputable def log (a : ℝ≥0∞) := Real.log (ENNReal.toReal a)

noncomputable def KL {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ] (dμ dπ : α → ℝ≥0∞) := ENNReal.ofReal (∫ x in Set.univ, log ((dμ x) / (dπ x)) ∂μ)

/--
 ∀ a ∈ ]0, ∞[, exp (log a) = (a : ℝ).
-/
lemma enn_comp_exp_log (a : ℝ≥0∞) (ha : a ≠ 0) (ha2 : a ≠ ∞) : Real.exp (log a) = ENNReal.toReal a := by
  by_cases h : ENNReal.toReal a = 0
  · exfalso
    have t : a = 0 ∨ a = ∞ := (toReal_eq_zero_iff a).mp h
    cases t with
    | inl hp => exact ha hp
    | inr hq => exact ha2 hq

  push_neg at h
  have t : ENNReal.toReal a ≠ 0 → ENNReal.toReal a < 0 ∨ 0 < ENNReal.toReal a := by {simp}
  specialize t h
  cases t with
  | inl hp => {
    have tt : 0 < ENNReal.toReal a := toReal_pos ha ha2
    linarith
  }
  | inr hq => exact Real.exp_log hq

/--
 ∀ a ∈ ]0, ∞[, log (exp a) = (a : ℝ).
-/
lemma enn_comp_log_exp (a : ℝ) : log (ENNReal.ofReal (Real.exp a)) = a := by
  unfold log
  rw [toReal_ofReal (Real.exp_nonneg a)]
  exact Real.log_exp a

/--
 ∀ a ∈ ]0, ∞[, ln a = (c : ℝ) → a = (exp c : ℝ≥0∞).
-/
lemma cancel_log_exp (a : ℝ≥0∞) (ha : a ≠ 0) (ha2 : a ≠ ∞) (c : ℝ) : log a = c → a = ENNReal.ofReal (Real.exp c) :=
by
  intro h
  rw [←h, enn_comp_exp_log a ha ha2]
  exact Eq.symm (ofReal_toReal ha2)
  /- intro h
  have log_a := enn_comp_log_exp c
  rwa [h] -/

/--
  Definition of infinite limit at infinity for vector-valued function (we use the order of real numbers on the norm of vectors as an order on ℝᵈ).
-/
def tends_to_infty {α : Type*} [Norm α] (f : α → ℝ) := ∀ c > 0, ∃ (x : α), ∀ (x':α), ‖x‖ ≤ ‖x'‖ → c < f x
variable [Norm α]
omit [NormedAddCommGroup (α → ℝ)] [InnerProductSpace ℝ (α → ℝ)] in
/--
  Unformal but highly pratical multivariate integration by parts.
-/
theorem mv_integration_by_parts (μ : Measure α) (f : α → ℝ) (g grad_f dg : Fin d → α → ℝ) (h : ∀ x, tends_to_infty (λ (x : α) ↦ ‖x‖) → ∀i, f x * g i x = 0) : ∫ x, f x * (∑ i ∈ Set.univ, dg i x) ∂μ = - ∫ x, (∑ i ∈ Set.univ, grad_f i x * g i x) ∂μ := by sorry

lemma summable_nonneg_iff_0 {f : ℕ → ℝ} (h_nonneg : ∀ i, 0 <= f i) (s : Summable f) : ∑' i, f i = 0 ↔ ∀ i, f i = 0 := by
  let g := λ i ↦ (f i).toNNReal

  have f_coe : f = λ a => (g a : ℝ) := by {
      ext a
      rw [λ i ↦ Real.coe_toNNReal (f i) (h_nonneg i)]
    }

  have coe_summable : Summable g := by {
    rw [f_coe] at s
    exact NNReal.summable_coe.mp s
  }

  constructor
  · intro h_tsum
    have sum_coe_eq_0 : ∑' i, (g i : ℝ) = 0 := by {
      simp_rw [show ∀ i, (g i : ℝ) = f i by intro i; rw [f_coe]]
      exact h_tsum
    }
    have coe_sum_eq_0 : ↑(∑' i, g i) = 0 := by {
      have coe_tsum : ↑(∑' i, g i) = ∑' i, (g i : ℝ) := NNReal.coe_tsum
      rw [sum_coe_eq_0] at coe_tsum
      exact NNReal.coe_eq_zero.mp coe_tsum
    }

    have g_eq_0 := (Summable.tsum_eq_zero_iff coe_summable).mp coe_sum_eq_0
    intro i
    specialize g_eq_0 i
    rw [f_coe]
    exact NNReal.coe_eq_zero.mpr g_eq_0
  intro hf
  simp_rw [hf]
  exact tsum_zero

lemma remove_univ_integral {α : Type} [MeasureSpace α] (μ : Measure α) (f : α → ℝ) : ∫ x in Set.univ, f x ∂μ = ∫ x, f x ∂μ := by simp
