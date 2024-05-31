/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.Analysis.InnerProductSpace.Basic

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace
open BigOperators Finset

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 4000000

/-=====================================RKHS SECTION=====================================-/

/-
  Here we define the product RKHS.
-/

/-
  We provide a typeclass definition for a generic RKHS.
-/

class RKHS {E F : Type*} [RCLike F] (H : Set (E → F)) [NormedAddCommGroup H] [InnerProductSpace F H] where
  k : E → E → F
  memb : ∀ (x : E), k x ∈ H
  repro : ∀ f, (hf : f ∈ H) → ∀ (x : E), f x = inner (⟨f, hf⟩ : H) ⟨k x, memb x⟩

def product_RKHS {α : Type*} (H : Set (α → ℝ)) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [RKHS H] {d : ℕ} (hd : d ≠ 0) := range d → H

namespace RKHS

variable {α : Type*} {H : Set (α → ℝ)} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [RKHS H]

variable {d : ℕ} {hd : d ≠ 0}

instance : Inner ℝ (product_RKHS H hd) where
  inner := λ f g ↦ ∑ i ∈ Set.univ, inner (f i) (g i)

instance : Norm (product_RKHS H hd) where
  norm := λ f ↦ inner f f

lemma norm_eq_zero_iff (f : product_RKHS H hd) : ‖f‖ = 0 ↔ ∀ i, f i = 0 := by
  constructor
  · intro norm_eq_0
    rw [show ‖f‖ = inner f f by rfl] at norm_eq_0
    rw [show inner f f = ∑ i ∈ Set.univ, inner (f i) (f i) by rfl] at norm_eq_0
    simp_rw [λ i ↦ real_inner_self_eq_norm_sq (f i)] at norm_eq_0

    have sq_norm_nonneg : ∀ i ∈ Set.toFinset (Set.univ), (0 : ℝ) <= ‖f i‖^2 := λ i _ ↦ sq_nonneg (‖f i‖)
    intro i
    have sq_norm_eq_0 := (sum_eq_zero_iff_of_nonneg sq_norm_nonneg).mp norm_eq_0 i (Set.mem_toFinset.mpr (by trivial))

    have norm_eq_0 : ‖f i‖ = (0 : ℝ) := sq_eq_zero_iff.mp sq_norm_eq_0
    exact normAddGroupNorm.proof_1 H (f i) norm_eq_0

  intro hf
  rw [show ‖f‖ = inner f f by rfl]
  rw [show inner f f = ∑ i ∈ Set.univ, inner (f i) (f i) by rfl]
  have inner_eq_0 : ∀ i ∈ Set.toFinset (Set.univ), inner (f i) (f i) = (0 : ℝ) := by {
    intro i _
    rw [hf i]
    exact inner_zero_right 0
  }
  rw [sum_congr rfl inner_eq_0]
  exact sum_const_zero

end RKHS
