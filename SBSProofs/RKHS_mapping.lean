/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib

import SBSProofs.Utils

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

variable {d : ℕ} {Ω : Set (Vector ℝ d)}

variable (k : Ω → Ω → ℝ) (l : ℕ → ℝ) (ϕ : ℕ → Ω → ℝ)

theorem mercer (x y : Ω) : Summable ((l ·) * (ϕ · x) * (ϕ · y)) ∧  k x y = ∑' i, (l i) * (ϕ i x) * (ϕ i y) := by sorry

def H := {f : Ω → ℝ // ∃ (a : ℕ → ℝ), (f = λ x ↦ (∑' i, (l i) * (a i) * (ϕ i x))) ∧ Summable ((l ·) * (a ·)^2)}

variable {α : Type} (H : Set α) [NormedAddCommGroup (st H)] [InnerProductSpace ℝ (st H)]

--def inner (f g : H l ϕ) :=
