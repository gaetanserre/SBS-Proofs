/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib

import SBSProofs.Utils

open Classical MeasureTheory

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

set_option trace.Meta.Tactic.simp.rewrite true
--set_option maxHeartbeats 600000

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

noncomputable def H_inner {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} (f g : H v e μ) : ℝ := ∑' i, (v.1 i) * ((h_repr_ne f).some i) * ((h_repr_ne g).some i)

variable {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} (f g : H v e μ)


/--
 - ∀ f, 0 <= ⟨f, f⟩
-/
example : 0 <= H_inner f f := by
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

lemma zero_in_H : zero ∈ L2 μ ∧ ∃ (a : ℕ → ℝ), (zero = λ x ↦ (∑' i, (v.1 i) * (a i) * (e i x))) ∧ Summable (λ i ↦ (v.1 i) * (a i)^2) := by
  refine ⟨zero_in_L2, ?_⟩
  let a : ℕ → ℝ := λ _ ↦ 0
  use a
  constructor
  · ext x
    have summand_zero : ∀ i, v.1 i * a i * e i x = 0 := by {
      intro i
      rw [show v.1 i * a i * e i x = v.1 i * 0 * e i x by rfl]
      ring
    }
    simp_rw [summand_zero, tsum_zero]
    rfl
  have zero_fun : (λ i ↦ v.1 i * a i ^ 2) = (λ (i : ℕ) ↦ (0 : ℝ)) := by {
    ext i
    rw [show a i = 0 by rfl]
    ring
  }
  rw [zero_fun]
  have hf : ∀ b ∉ (∅ : Finset ℕ), (λ (i : ℕ) ↦ (0 : ℝ)) b = 0 := by {
    intro b b_not_in
    rfl
  }
  exact summable_of_ne_finset_zero hf

instance : Zero (H v e μ) where
  zero := ⟨zero, zero_in_H⟩

example : H_inner f 0 = 0 := by

  sorry
