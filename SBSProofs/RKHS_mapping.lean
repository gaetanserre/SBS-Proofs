/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib

import SBSProofs.Utils

open Classical MeasureTheory ENNReal NNReal

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 600000

variable {d : ℕ} {Ω : Set (Vector ℝ d)} [MeasureSpace Ω]

--variable (k : Ω → Ω → ℝ) (e : ℕ → ℝ) (ϕ : ℕ → Ω → ℝ)

def L2 (μ : Measure Ω) := {f : Ω → ℝ | ∃ C, ∫ x, |f x|^2 ∂μ <= C}

/- theorem mercer (x y : Ω) : Summable ((e ·) * (ϕ · x) * (ϕ · y)) ∧  k x y = ∑' i, (e i) * (ϕ i x) * (ϕ i y) := by sorry -/

def eigen := {e : ℕ → ℝ // ∀ i, 0 <= e i}

def H (v : eigen) (e : ℕ → Ω → ℝ) (μ : Measure Ω) := {f | f ∈ L2 μ ∧ ∃ (a : ℕ → ℝ), (f = λ x ↦ (∑' i, (v.1 i) * (a i) * (e i x))) ∧ Summable (λ i ↦ (v.1 i) * (a i)^2)}

def h_repr {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} (f : H v e μ) := {a : ℕ → ℝ | (f = λ x ↦ (∑' i, (v.1 i) * (a i) * (e i x))) ∧ (Summable (λ i ↦ (v.1 i) * (a i)^2))}

lemma h_repr_ne {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} (f : H v e μ) : (h_repr f).Nonempty := by
  rcases f.2 with ⟨_, ⟨a, ha⟩⟩
  use a
  exact ha

axiom h_repr_unique {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} {f : H v e μ} {a b : ℕ → ℝ} (ha : a ∈ h_repr f) (hb : b ∈ h_repr f) : a = b

lemma unique_choice {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} {f : H v e μ} {a : ℕ → ℝ} (h : a ∈ h_repr f) : (h_repr_ne f).some = a := h_repr_unique (h_repr_ne f).some_mem h

noncomputable def H_inner {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} (f g : H v e μ) : ℝ := ∑' i, (v.1 i) * ((h_repr_ne f).some i) * ((h_repr_ne g).some i)

variable {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} (f g : H v e μ)

def zero : Ω → ℝ := λ _ ↦ 0

lemma zero_in_L2 : zero ∈ L2 μ := by
  have integrable : ∃ C, ∫ x, |zero x|^2 ∂μ <= C := by {
    simp_rw [
        show ∀ (x : Ω), zero x = 0 by exact λ x ↦ rfl,
        abs_zero,
        sq_eq_zero_iff.mpr rfl,
        integral_zero Ω ℝ
      ]
    use 0
  }
  exact integrable

lemma zero_repr : zero = λ x ↦ (∑' i, (v.1 i) * ((λ _ ↦ 0) i) * (e i x)) := by
  let a : ℕ → ℝ := λ _ ↦ 0
  ext x
  have summand_zero : ∀ i, v.1 i * a i * e i x = 0 := by {
    intro i
    rw [show v.1 i * a i * e i x = v.1 i * 0 * e i x by rfl]
    ring
  }
  simp_rw [summand_zero, tsum_zero]
  rfl

lemma zero_summable : Summable (λ i ↦ (v.1 i) * (0 : ℝ)^2) := by
  have zero_fun : (λ i ↦ v.1 i * (0 : ℝ)^2) = (λ (i : ℕ) ↦ (0 : ℝ)) := by {
    ext i
    ring
  }
  rw [zero_fun]
  have hf : ∀ b ∉ (∅ : Finset ℕ), (λ (i : ℕ) ↦ (0 : ℝ)) b = 0 := by {
    intro b b_not_in
    rfl
  }
  exact summable_of_ne_finset_zero hf

lemma zero_in_H : zero ∈ L2 μ ∧ ∃ (a : ℕ → ℝ), (zero = λ x ↦ (∑' i, (v.1 i) * (a i) * (e i x))) ∧ Summable (λ i ↦ (v.1 i) * (a i)^2) := by
  refine ⟨zero_in_L2, ?_⟩
  let a : ℕ → ℝ := λ _ ↦ 0
  use (λ _ ↦ 0)
  refine ⟨zero_repr, zero_summable⟩

instance : Zero (H v e μ) where
  zero := ⟨zero, zero_in_H⟩

lemma zero_unique_repr : (h_repr_ne (0 : H v e μ)).some = (λ i ↦ 0) := by
  let a : ℕ → ℝ := λ i ↦ 0
  have a_in_repr : a ∈ h_repr 0 := by {
    have tmp : (0 : H v e μ) = λ x ↦ (∑' i, (v.1 i) * ((λ _ ↦ 0) i) * (e i x)) := zero_repr
    exact ⟨tmp, zero_summable⟩
  }
  exact unique_choice a_in_repr

axiom inner_summable : Summable (λ i ↦ (v.1 i) * ((h_repr_ne f).some i) * ((h_repr_ne g).some i))

/--
 - ∀ f, 0 <= ⟨f, f⟩
-/
lemma inner_nonneg : 0 <= H_inner f f := by
  unfold H_inner
  let a := (h_repr_ne f).some
  have sq : ∀ i, v.1 i * a i * a i = (v.1 i) * (a i)^2 := by {
    intro i
    ring
  }
  simp_rw [sq]
  have nonneg : ∀ i, (0 : ℝ) <= (v.1 i) * (a i)^2 := by {
    intro i
    exact Left.mul_nonneg (v.2 i) (sq_nonneg (a i))
  }
  exact tsum_nonneg nonneg

lemma inner_symmetric : H_inner f g = H_inner g f := by
  unfold H_inner
  have comm : ∀ i, (v.1 i) * ((h_repr_ne f).some i) * ((h_repr_ne g).some i) = (v.1 i) * ((h_repr_ne g).some i) * ((h_repr_ne f).some i) := λ i ↦ by ring
  simp_rw [comm]

lemma inner_zero_eq_zero : H_inner f 0 = 0 := by
  unfold H_inner
  rw [zero_unique_repr]

  have summand_eq_zero : ∀ i, v.1 i * (h_repr_ne f).some i * (λ i ↦ 0) i = 0 := by {
    intro i
    rw [show (λ (i : ℕ) ↦ (0 : ℝ)) i = 0 by rfl]
    ring
  }
  simp_rw [summand_eq_zero]
  exact tsum_zero

example : f ≠ 0 → 0 < H_inner f f := by
  intro f_neq_0
  by_contra h; push_neg at h
  have inner_pos := inner_nonneg f
  have inner_eq_0 : H_inner f f = 0 := by linarith
  unfold H_inner at inner_eq_0

  let a := (h_repr_ne f).some

  have sq_summand : ∀ i, v.1 i * a i * a i = v.1 i * (a i)^2 := λ i ↦ by ring
  simp_rw [sq_summand] at inner_eq_0

  have summand_nonneg : ∀ i, (0 : ℝ) <= v.1 i * (a i)^2 := by {
    intro i
    exact Left.mul_nonneg (v.2 i) (sq_nonneg (a i))
  }

  have summand_summable : Summable (λ i ↦ v.1 i * (a i)^2) := by {
    simp_rw [←sq_summand]
    exact inner_summable f f
  }

  have summand_eq_zero := (summable_nonneg_iff_0 summand_nonneg summand_summable).mp inner_eq_0

  have prod_v_a_eq_0 : ∀ i, v.1 i * a i = 0 := by {
    intro i
    cases mul_eq_zero.mp (summand_eq_zero i) with
    | inl hv =>
      rw [hv]
      ring
    | inr ha =>
      rw [sq_eq_zero_iff.mp ha]
      ring
  }

  have f_eq_0 : f = 0 := by {
    ext x
    rw [show (0 : H v e μ).1 = zero by rfl]
    rw [show zero x = 0 by rfl]
    rcases (h_repr_ne f).some_mem with ⟨ha, _⟩
    rw [ha, show (h_repr_ne f).some = a by rfl]

    have summand_eq_0 : ∀ i, (v.1 i) * (a i) * (e i x) = 0 := by {
      intro i
      rw [prod_v_a_eq_0]
      ring
    }

    simp_rw [summand_eq_0]
    exact tsum_zero
  }

  exact f_neq_0 f_eq_0

lemma prod_f_eq_tsum (a : ℝ) : (λ x ↦ a * f.1 x) = λ x ↦ ∑' i, v.1 i * (λ i ↦ a * (h_repr_ne f).some i) i * e i x := by
  let g := λ x ↦ a * f.1 x
  let h := (h_repr_ne f).some
  let g_h := λ i ↦ a * h i
  have h_repr : h ∈ h_repr f := (h_repr_ne f).some_mem

  ext x
  rcases h_repr with ⟨f_repr, _⟩
  have g_eq_tsum : g = λ x ↦ ∑' i, v.1 i * a * h i * e i x := by {
    ext x
    have comm : ∀ i, v.1 i * a * h i * e i x = a * v.1 i * h i * e i x := λ i ↦ by ring
    simp_rw [comm]

    have summand_comm : ∀ i, a * v.1 i * h i * e i x = a * (v.1 i * h i * e i x) := by {
      intro i
      ring
    }
    simp_rw [summand_comm]

    have const_out : ∑' i, a * (λ i ↦ (v.1 i * h i * e i x)) i = a * ∑' i, (λ i ↦ (v.1 i * h i * e i x)) i := by exact tsum_mul_left
    rw [const_out, ←congrFun f_repr x]
  }
  have g_x := congrFun g_eq_tsum x
  simp_rw [show ∀ i, v.1 i * a * h i * e i x = v.1 i * (a * h i) * e i x by intro i; ring] at g_x
  simp_rw [show ∀ i, a * h i = g_h i by intro i; rfl] at g_x
  exact g_x

lemma prod_f_summable (a : ℝ) : Summable (λ i ↦ v.1 i * (λ i ↦ a * (h_repr_ne f).some i) i ^ 2) := by
  let h := (h_repr_ne f).some
  let g_h := λ i ↦ a * h i
  have h_repr : h ∈ h_repr f := (h_repr_ne f).some_mem

  rcases h_repr with ⟨_, h_summable⟩
  have comm_fun : (λ i ↦ v.1 i * (g_h i)^2) = (λ i ↦ a^2 * (v.1 i * (h i)^2)) := by {
    ext i
    rw [show g_h i = a * h i by rfl]
    rw [mul_pow a (h i) 2]
    rw [show (v.1 i) * (a^2 * (h i)^2) = (a^2) * (v.1 i * (h i)^2) by ring]

  }
  rw [comm_fun]
  exact (h_summable.mul_left (a^2))

lemma mul_in_H (a : ℝ) : (λ x ↦ a * f.1 x) ∈ (H v e μ) := by
  let g := λ x ↦ a * f.1 x
  have g_in_L2 : g ∈ L2 μ := by {
    unfold L2
    rcases f.2 with ⟨⟨C, hC⟩, _⟩
    use a^2 * C
    have g_to_f : ∀ x, |g x|^2 = |a * f.1 x|^2 := by {
      intro x
      rfl
    }
    simp_rw [g_to_f, show ∀ x, |a * f.1 x|^2 = (a * f.1 x)^2 by intro x; simp]
    simp_rw [λ x ↦ mul_pow a (f.1 x) 2]
    rw [integral_mul_left (a^2) fun x ↦ (f.1 x)^2]
    simp_rw [show ∀ x, (f.1 x)^2 = |f.1 x|^2 by simp]
    exact mul_le_mul_of_nonneg_left hC (sq_nonneg a)
  }

  let h := (h_repr_ne f).some
  let g_h := λ i ↦ a * h i
  refine ⟨g_in_L2, g_h, prod_f_eq_tsum f a, prod_f_summable f a⟩

instance : HMul ℝ (H v e μ) (H v e μ) where
  hMul := λ a f ↦ ⟨λ x ↦ a * f.1 x, mul_in_H f a⟩

example (a : ℝ) : H_inner (a * f) g = a * H_inner f g := by
  let h := (h_repr_ne f).some
  let h_af := λ i ↦ a * h i

  have h_af_in : h_af ∈ h_repr (a * f) := ⟨prod_f_eq_tsum f a, prod_f_summable f a⟩
  unfold H_inner
  rw [unique_choice h_af_in]
  have comm_summand : ∀ i, v.1 i * h_af i * (h_repr_ne g).some i = a * v.1 i * h i * (h_repr_ne g).some i := by {
    intro i
    ring
  }
  have lambda_comm : ∀ i, a * v.1 i * h i * (h_repr_ne g).some i = a * (λ i ↦ v.1 i * h i * (h_repr_ne g).some i) i := by {
    intro i
    ring
  }
  simp_rw [comm_summand, lambda_comm]
  exact tsum_mul_left


/--
  ∀ f, g ∈ H, f + g ∈ L2. Assume it.
-/
lemma add_in_L2 : (λ x ↦ f.1 x + g.1 x) ∈ L2 μ := by sorry

lemma add_repr : (λ x ↦ f.1 x + g.1 x) = λ x ↦ (∑' i, v.1 i * ((h_repr_ne f).some i + (h_repr_ne g).some i) * e i x) := by sorry

lemma add_summable : Summable (λ i ↦ v.1 i * ((h_repr_ne f).some i + (h_repr_ne g).some i)^2) := by sorry

lemma add_in_H : (λ x ↦ f.1 x + g.1 x) ∈ H v e μ := by
  let h := λ i ↦ (h_repr_ne f).some i + (h_repr_ne g).some i
  exact ⟨add_in_L2 f g, h, add_repr f g, add_summable f g⟩

instance : HAdd (H v e μ) (H v e μ) (H v e μ) where
  hAdd := λ f g ↦ ⟨(λ x ↦ f.1 x + g.1 x), add_in_H f g⟩

/- instance : NormedAddCommGroup (H v e μ) where
  norm := λ f ↦ H_inner f f
  add := λ f g ↦ f + g
  --add_assoc -/
