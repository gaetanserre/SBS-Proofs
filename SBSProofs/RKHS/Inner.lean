/-
 - Created in 2024 by Gaëtan Serré
-/

/-
 - https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.RingTheory.HopfAlgebra
import Mathlib.Topology.CompletelyRegular
import Mathlib.Topology.MetricSpace.Polish

import SBSProofs.Utils
import SBSProofs.RKHS.Basic

open Classical MeasureTheory

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

set_option trace.Meta.Tactic.simp.rewrite true
set_option maxHeartbeats 600000

variable {d : ℕ} {Ω : Set (Vector ℝ d)} [MeasureSpace Ω]

def L2 (μ : Measure Ω) [IsFiniteMeasure μ] := {f : Ω → ℝ | Memℒp f 2 μ}

def eigen := {v : ℕ → ℝ // ∀ i, 0 <= v i}

def f_repr (v : eigen) (e : ℕ → Ω → ℝ) (f : Ω → ℝ) (a : ℕ → ℝ) := (f = λ x ↦ (∑' i, (v.1 i) * (a i) * (e i x))) ∧ (∀ x, Summable (λ i ↦ (v.1 i) * (a i) * (e i x)))

/-
  We define a set of functions that depends on a finite measure μ. Each function is representable by a infinite sum.
-/

def H (v : eigen) (e : ℕ → Ω → ℝ) (μ : Measure Ω) [IsFiniteMeasure μ] := {f | f ∈ L2 μ ∧ ∃ (a : ℕ → ℝ), (f_repr v e f a) ∧ Summable (λ i ↦ (v.1 i) * (a i)^2)}

def set_repr {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f : H v e μ) := {a : ℕ → ℝ | (f_repr v e f.1 a) ∧ (Summable (λ i ↦ (v.1 i) * (a i)^2))}

lemma set_repr_ne {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f : H v e μ) : (set_repr f).Nonempty := by
  rcases f.2 with ⟨_, ⟨a, ha⟩⟩
  use a
  exact ha

/-
  We assume that the the representative of each function in H is unique (property of v and e).
-/

axiom set_repr_unique {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] {f : H v e μ} {a b : ℕ → ℝ} (ha : a ∈ set_repr f) (hb : b ∈ set_repr f) : a = b

lemma unique_choice {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] {f : H v e μ} {a : ℕ → ℝ} (h : a ∈ set_repr f) : (set_repr_ne f).some = a := set_repr_unique (set_repr_ne f).some_mem h

/-
  We assume that the product of two representative is summable.
-/

axiom product_summable {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f g : H v e μ) : Summable (λ i ↦ (v.1 i) * ((set_repr_ne f).some i) * ((set_repr_ne g).some i))


/-
  We define the multiplication between a real number and a function in H as the pointwise product. We show that the result lies in H.
-/

namespace Ring

variable {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f g : H v e μ)

lemma mul_repr (a : ℝ) : f_repr v e (λ x ↦ a * f.1 x) (λ i ↦ a * (set_repr_ne f).some i) := by
  let g := λ x ↦ a * f.1 x
  let h := (set_repr_ne f).some
  let g_h := λ i ↦ a * h i
  have f_repr : h ∈ set_repr f := (set_repr_ne f).some_mem
  constructor
  · ext x
    rcases f_repr with ⟨⟨f_repr, _⟩, _⟩
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
  intro x
  have remove_function : (λ i ↦ v.1 i * (λ i ↦ a * h i) i * e i x) =(λ i ↦ a * (v.1 i * h i * e i x)) := by {
    ext i
    ring
  }
  rw [remove_function]
  exact (f_repr.1.2 x).mul_left a

lemma mul_summable (a : ℝ) : Summable (λ i ↦ v.1 i * (λ i ↦ a * (set_repr_ne f).some i) i ^ 2) := by
  let h := (set_repr_ne f).some
  let g_h := λ i ↦ a * h i
  have set_repr : h ∈ set_repr f := (set_repr_ne f).some_mem

  rcases set_repr with ⟨_, h_summable⟩
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
  have g_in_L2 : g ∈ L2 μ := Memℒp.const_mul (f.2).1 a
  let h := (set_repr_ne f).some
  let g_h := λ i ↦ a * h i
  refine ⟨g_in_L2, g_h, mul_repr f a, mul_summable f a⟩

instance : HMul ℝ (H v e μ) (H v e μ) where
  hMul := λ a f ↦ ⟨λ x ↦ a * f.1 x, mul_in_H f a⟩

instance : HSMul ℝ (H v e μ) (H v e μ) where
  hSMul := λ r f ↦ r * f

end Ring

/-
  We define the sum between two functions in H as the pointwise sum. We show that the result lies in H. We also define the 0 function of H. We show several properties on the addition.
-/

namespace Group

variable {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f g : H v e μ)

lemma add_in_L2 : (λ x ↦ f.1 x + g.1 x) ∈ L2 μ := Memℒp.add (f.2.1) (g.2.1)

lemma add_summable : Summable (λ i ↦ v.1 i * ((set_repr_ne f).some i + (set_repr_ne g).some i)^2) := by
  let a_f := (set_repr_ne f).some
  let a_g := (set_repr_ne g).some
  have f_eq : (λ i ↦ v.1 i * (a_f i + a_g i)^2) = (λ i ↦ v.1 i * a_f i * a_f i + 2 * (v.1 i * a_f i * a_g i) + v.1 i * a_g i * a_g i) := by {
    ext i
    ring
  }
  rw [f_eq]

  exact ((product_summable f f).add ((product_summable f g).mul_left 2)).add (product_summable g g)

lemma add_repr : f_repr v e (λ x ↦ f.1 x + g.1 x) (λ i ↦ (set_repr_ne f).some i + (set_repr_ne g).some i) := by
  let a_f := (set_repr_ne f).some
  let a_g := (set_repr_ne g).some

  obtain ⟨af_repr, _⟩ := (set_repr_ne f).some_mem
  obtain ⟨ag_repr, _⟩ := (set_repr_ne g).some_mem

  have summand_distrib : ∀ x, ∀ i, v.1 i * (a_f i + a_g i) * e i x = v.1 i * a_f i * e i x + v.1 i * a_g i * e i x := by intro x i; ring

  constructor
  · ext x
    simp_rw [summand_distrib x]

    rw [
      tsum_add (af_repr.2 x) (ag_repr.2 x),
      ←congrFun af_repr.1 x,
      ←congrFun ag_repr.1 x
    ]
  intro x
  simp_rw [summand_distrib x]
  exact (af_repr.2 x).add (ag_repr.2 x)

/-
 We define the 0 of H as pointwise 0 function. We show that it lies in H.
-/

def zero : Ω → ℝ := λ _ ↦ 0

lemma zero_repr : f_repr v e zero (λ _ ↦ 0) := by
  let a : ℕ → ℝ := λ _ ↦ 0
  constructor
  · ext x
    have summand_zero : ∀ i, v.1 i * a i * e i x = 0 := by {
      intro i
      rw [show v.1 i * a i * e i x = v.1 i * 0 * e i x by rfl]
      ring
    }
    simp_rw [summand_zero, tsum_zero]
    rfl
  intro x
  have null_function : (λ i ↦ (v.1 i) * (a i) * (e i x)) = (λ (i : ℕ) ↦ (0 : ℝ)) := by {
    ext i
    rw [show a i = 0 by rfl]
    ring
  }
  rw [null_function]
  exact summable_zero

lemma zero_summable : Summable (λ i ↦ (v.1 i) * (0 : ℝ)^2) := by
  have zero_fun : (λ i ↦ v.1 i * (0 : ℝ)^2) = (λ (i : ℕ) ↦ (0 : ℝ)) := by {
    ext i
    ring
  }
  rw [zero_fun]
  have hf : ∀ b ∉ (∅ : Finset ℕ), (λ (i : ℕ) ↦ (0 : ℝ)) b = 0 := λ _ _ ↦ rfl
  exact summable_of_ne_finset_zero hf

lemma zero_in_H : zero ∈ L2 μ ∧ ∃ (a : ℕ → ℝ), (f_repr v e zero a) ∧ Summable (λ i ↦ (v.1 i) * (a i)^2) := ⟨memℒp_const 0, (λ _ ↦ 0), zero_repr, zero_summable⟩

instance : Zero (H v e μ) where
  zero := ⟨zero, zero_in_H⟩

lemma zero_unique_repr : (set_repr_ne (0 : H v e μ)).some = (λ i ↦ 0) := by
  let a : ℕ → ℝ := λ _ ↦ 0
  have a_in_repr : a ∈ set_repr (0 : H v e μ) := by {
    --have tmp := zero_repr
    refine ⟨(zero_repr : f_repr v e (0 : H v e μ).1 a), ?_⟩
    have null_function : (λ i ↦ v.1 i * (a i)^2) = λ (i : ℕ) ↦ (0 : ℝ) := by {
      ext i
      rw [show a i = 0 by rfl]
      ring
    }
    rw [null_function]
    exact summable_zero
  }
  exact unique_choice a_in_repr

lemma add_in_H : (λ x ↦ f.1 x + g.1 x) ∈ H v e μ := by
  let h := λ i ↦ (set_repr_ne f).some i + (set_repr_ne g).some i
  exact ⟨add_in_L2 f g, h, add_repr f g, add_summable f g⟩

instance : HAdd (H v e μ) (H v e μ) (H v e μ) where
  hAdd := λ f g ↦ ⟨(λ x ↦ f.1 x + g.1 x), add_in_H f g⟩

instance : HSub (H v e μ) (H v e μ) (H v e μ) where
  hSub := λ f g ↦ f + (-1 : ℝ) * g

instance : Neg (H v e μ) where
  neg := λ f ↦ (-1 : ℝ) * f

lemma H_add_assoc (a b c : H v e μ) : a + b + c = a + (b + c) := by
  ext x
  rw [show (a + b + c).1 x = a.1 x + b.1 x + c.1 x by rfl]
  rw [show (a + (b + c)).1 x = a.1 x + (b.1 x + c.1 x) by rfl]
  ring

lemma H_add_comm (a b : H v e μ) : a + b = b + a := by
  ext x
  rw [show (a + b).1 x = a.1 x + b.1 x by rfl]
  rw [show (b + a).1 x = b.1 x + a.1 x by rfl]
  ring

lemma H_add_zero (a : H v e μ) : a + 0 = a := by
  ext x
  rw [show (a + 0).1 x = a.1 x + (0 : H v e μ).1 x by rfl]
  rw [show (0 : H v e μ).1 x = 0 by rfl]
  ring

lemma H_zero_add (a : H v e μ) : 0 + a = a := by
  rw [H_add_comm 0 a]
  exact H_add_zero a

lemma H_add_left_neg (a : H v e μ) : -a + a = 0 := by
  rw [show -a = (-1 : ℝ) * a by rfl]
  ext x
  rw [show ((-1 : ℝ) * a + a).1 x = ((-1 : ℝ) * a).1 x + a.1 x by rfl]
  rw [show ((-1 : ℝ) * a).1 x = (-1 : ℝ) * a.1 x by rfl]
  rw [show (0 : H v e μ).1 x = 0 by rfl]
  ring

end Group

/-
  We define a function : H × H → ℝ. The purpose of the following is to prove that H endowed with this function is a inner product space.
-/
noncomputable def H_inner {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f g : H v e μ) : ℝ := ∑' i, (v.1 i) * ((set_repr_ne f).some i) * ((set_repr_ne g).some i)

/-
 - We show properties on the inner product of H and the induced norm.
-/

namespace Inner

open Ring Group

variable {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f g : H v e μ)

noncomputable instance : Inner ℝ (H v e μ) where
  inner := H_inner

noncomputable instance : Norm (H v e μ) where
  norm := λ f ↦ Real.sqrt (inner f f)

noncomputable instance : Dist (H v e μ) where
  dist := λ f g ↦ norm (f - g)

lemma inner_mul_left (a : ℝ) : inner (a * f) g = a * inner f g := by
  let h := (set_repr_ne f).some
  let h_af := λ i ↦ a * h i

  have h_af_in : h_af ∈ set_repr (a * f) := ⟨mul_repr f a, mul_summable f a⟩
  rw [show inner (a * f) g = H_inner (a * f) g by rfl]
  unfold H_inner
  rw [unique_choice h_af_in]
  have comm_summand : ∀ i, v.1 i * h_af i * (set_repr_ne g).some i = a * v.1 i * h i * (set_repr_ne g).some i := by {
    intro i
    ring
  }
  have lambda_comm : ∀ i, a * v.1 i * h i * (set_repr_ne g).some i = a * (λ i ↦ v.1 i * h i * (set_repr_ne g).some i) i := by {
    intro i
    ring
  }
  simp_rw [comm_summand, lambda_comm]
  exact tsum_mul_left

lemma H_inner_add_left (h : H v e μ) : (inner (f + g) h : ℝ) = inner f h + inner g h := by
  let a_f := (set_repr_ne f).some
  let a_g := (set_repr_ne g).some
  let a_h := (set_repr_ne h).some
  let a_fg := λ i ↦ a_f i + a_g i

  have a_fg_repr : a_fg ∈ set_repr (f + g) := ⟨add_repr f g, add_summable f g⟩
  rw [show inner (f + g) h = H_inner (f + g) h by rfl]
  unfold H_inner
  rw [unique_choice a_fg_repr]
  simp_rw [show ∀ i, v.1 i * a_fg i * a_h i = v.1 i * (a_f i + a_g i) * a_h i by intro i; rfl]

  simp_rw [show ∀ i, v.1 i * (a_f i + a_g i) * a_h i = v.1 i * a_f i * a_h i + v.1 i * a_g i * a_h i by intro i; ring]

  rw [tsum_add (product_summable f h) (product_summable g h)]
  rfl

lemma inner_symmetric : (inner f g : ℝ) = inner g f := by
  rw [show inner f g = H_inner f g by rfl]
  unfold H_inner
  have comm : ∀ i, (v.1 i) * ((set_repr_ne f).some i) * ((set_repr_ne g).some i) = (v.1 i) * ((set_repr_ne g).some i) * ((set_repr_ne f).some i) := λ i ↦ by ring
  simp_rw [comm]
  rfl

lemma inner_nonneg : (0 : ℝ) <= inner f f := by
  rw [show inner f f = H_inner f f by rfl]
  unfold H_inner
  let a := (set_repr_ne f).some
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

lemma H_norm_nonneg : (0 : ℝ) <= norm f := by
  rw [show norm f = Real.sqrt (inner f f) by rfl]
  exact Real.sqrt_nonneg (inner f f)

lemma inner_zero_eq_zero : inner f 0 = (0 : ℝ) := by
  rw [show inner f 0 = H_inner f 0 by rfl]
  unfold H_inner
  rw [zero_unique_repr]

  have summand_eq_zero : ∀ i, v.1 i * (set_repr_ne f).some i * (λ i ↦ 0) i = 0 := by {
    intro i
    rw [show (λ (i : ℕ) ↦ (0 : ℝ)) i = 0 by rfl]
    ring
  }
  simp_rw [summand_eq_zero]
  exact tsum_zero

lemma null_inner_imp_null_f : inner f f = (0 : ℝ) → f = 0 := by
  intro inner_eq_0
  rw [show inner f f = H_inner f f by rfl] at inner_eq_0
  unfold H_inner at inner_eq_0

  let a := (set_repr_ne f).some

  have sq_summand : ∀ i, v.1 i * a i * a i = v.1 i * (a i)^2 := λ i ↦ by ring
  simp_rw [sq_summand] at inner_eq_0

  have summand_nonneg : ∀ i, (0 : ℝ) <= v.1 i * (a i)^2 := by {
    intro i
    exact Left.mul_nonneg (v.2 i) (sq_nonneg (a i))
  }

  have summand_summable : Summable (λ i ↦ v.1 i * (a i)^2) := by {
    simp_rw [←sq_summand]
    exact product_summable f f
  }

  have summand_eq_zero := (summable_nonneg_iff_0 summand_nonneg summand_summable).mp inner_eq_0

  have mul_v_a_eq_0 : ∀ i, v.1 i * a i = 0 := by {
    intro i
    cases mul_eq_zero.mp (summand_eq_zero i) with
    | inl hv =>
      rw [hv]
      ring
    | inr ha =>
      rw [sq_eq_zero_iff.mp ha]
      ring
  }

  ext x
  rw [show (0 : H v e μ).1 = zero by rfl]
  rw [show zero x = 0 by rfl]
  rcases (set_repr_ne f).some_mem with ⟨⟨ha_r, ha_s⟩, _⟩
  rw [ha_r, show (set_repr_ne f).some = a by rfl]

  have summand_eq_0 : ∀ i, (v.1 i) * (a i) * (e i x) = 0 := by {
    intro i
    rw [mul_v_a_eq_0]
    ring
  }

  simp_rw [summand_eq_0]
  exact tsum_zero

lemma inner_eq_sq_norm : inner f f = (norm f)^2 := by
  rw [show norm f = Real.sqrt (inner f f) by rfl]
  rw [Real.sq_sqrt (inner_nonneg f)]

lemma distrib_H_norm (t : ℝ) : ‖f + t*g‖^2 = ‖f‖^2 + (2 : ℝ) * t * inner f g + t^2 * ‖g‖^2 := by
  rw [show  ‖f + t*g‖ = Real.sqrt (inner (f + t*g) (f + t*g)) by rfl]
  have inner_nn : (0 : ℝ) <= inner (f + t*g) (f + t*g) := inner_nonneg (f + t * g)
  rw [Real.sq_sqrt inner_nn]

  let a_f := (set_repr_ne f).some
  let a_g := (set_repr_ne g).some
  let a_f_tg := λ i ↦ a_f i + t * a_g i

  have a_f_tg_repr : a_f_tg ∈ set_repr (f + t*g) := by {
    have repr_add :
      (λ i ↦ a_f i + (set_repr_ne (t*g)).some i) ∈ set_repr (f + t*g)
      := ⟨add_repr f (t*g), add_summable f (t*g)⟩
    have repr_mul :
      (λ i ↦ t*(a_g i)) ∈ set_repr (t*g)
      := ⟨mul_repr g t, mul_summable g t⟩

    rwa [unique_choice repr_mul] at repr_add
  }

  rw [show inner (f + t*g) (f + t*g) = H_inner (f + t*g) (f + t*g) by rfl]
  unfold H_inner
  rw [unique_choice a_f_tg_repr]

  have distribute : ∀ i, v.1 i * a_f_tg i * a_f_tg i = v.1 i * a_f i * a_f i + (2:ℝ) * t * (v.1 i * a_f i * a_g i) + t^2 * (v.1 i * a_g i * a_g i) := by intro i; ring
  simp_rw [distribute]

  have add_summable : Summable (λ i ↦ v.1 i * a_f i * a_f i + ((2:ℝ) * t) * (v.1 i * a_f i * a_g i)) :=(product_summable f f).add ((product_summable f g).mul_left ((2:ℝ) * t))

  rw [tsum_add add_summable ((product_summable g g).mul_left (t^2))]

  have tsum_to_norm (h : H v e μ) : ∑' i, v.1 i * (set_repr_ne h).some i * (set_repr_ne h).some i = (norm h)^2 := by {
    rw [show ∑' i, v.1 i * (set_repr_ne h).some i * (set_repr_ne h).some i = H_inner h h by rfl]
    rw [show H_inner h h = inner h h by rfl]
    rw [inner_eq_sq_norm h]
  }

  rw [tsum_add (product_summable f f) ((product_summable f g).mul_left ((2:ℝ) * t))]

  have const_out : ∑' i, t^2 * (v.1 i * a_g i * a_g i) =  t^2 * ∑' i, v.1 i * a_g i * a_g i := tsum_mul_left
  rw [const_out, tsum_to_norm f, tsum_to_norm g]

  have const_out : ∑' i, 2 * t * (v.1 i * a_f i * a_g i) =  2 * t * ∑' i, (v.1 i * a_f i * a_g i) := tsum_mul_left
  rw [const_out]

  have tsum_to_inner : ∑' i, v.1 i * a_f i * a_g i = inner f g := by rfl
  rw [tsum_to_inner]

lemma H_cauchy_schwarz : inner f g <= ‖f‖ * ‖g‖ := by
  by_cases hg : ‖g‖ ≠ 0
  · have hg_sq := pow_ne_zero 2 hg
    let P := λ (t : ℝ) ↦ ‖f + t*g‖^2
    let t₀ := -inner f g / ‖g‖^2

    have P_nonneg : 0 <= P t₀  := sq_nonneg ‖f + t₀*g‖

    have P_t0_val : P t₀ = ‖f‖^2 - (inner f g)^2 / ‖g‖^2 := by {
      have P_t0 : P t₀ = ‖f‖^2 + (2 : ℝ) * t₀ * inner f g + t₀^2 * ‖g‖^2 := distrib_H_norm f g t₀
      rw [P_t0]
      rw [show t₀^2 = (inner f g)^2 / (‖g‖^2 * ‖g‖^2) by ring]
      rw [show (inner f g)^2 / (‖g‖^2 * ‖g‖^2) = (inner f g)^2 / ‖g‖^2 * (1:ℝ) / ‖g‖^2 by ring]
      rw [show (inner f g)^2 / ‖g‖^2 * (1:ℝ) / ‖g‖^2 * ‖g‖^2 = (inner f g)^2 / ‖g‖^2 * ((1:ℝ) / ‖g‖^2 * ‖g‖^2) by ring]
      rw [one_div_mul_cancel hg_sq]
      rw [show (inner f g)^2 / ‖g‖^2 * (1:ℝ) = (inner f g)^2 / ‖g‖^2 by ring]
      rw [show (2:ℝ) * t₀ * inner f g = (-2:ℝ) * (inner f g)^2 / ‖g‖^2 by ring]
      rw [show ‖f‖^2 + (-2:ℝ) * (inner f g)^2 / ‖g‖^2 + (inner f g)^2 / ‖g‖^2 = ‖f‖^2 -(inner f g)^2 / ‖g‖^2 by ring]
    }

    rw [P_t0_val] at P_nonneg

    have sq_ineq : (inner f g)^2 <= (‖f‖ * ‖g‖)^2 := by {
      rw [show (‖f‖ * ‖g‖)^2 = ‖f‖^2 * ‖g‖^2 by ring]
      rw [←(mul_inv_le_iff' (pow_two_pos_of_ne_zero hg))]
      rwa [←sub_nonneg]
    }
    --rw [←sq_abs (inner f g)] at sq_ineq
    rw [show (inner f g)^2 = (inner f g) * (inner f g) by ring] at sq_ineq
    rw [show (‖f‖ * ‖g‖)^2 = (‖f‖ * ‖g‖) * (‖f‖ * ‖g‖) by ring] at sq_ineq
    have norm_mul_nonneg : 0 <= ‖f‖ * ‖g‖ := Left.mul_nonneg (H_norm_nonneg f) (H_norm_nonneg g)
    exact nonneg_le_nonneg_of_sq_le_sq norm_mul_nonneg sq_ineq

  push_neg at hg
  rw [show ‖g‖ = Real.sqrt (inner g g) by rfl] at hg
  rw [Real.sqrt_eq_zero (inner_nonneg g)] at hg
  have g_eq_0 := null_inner_imp_null_f g hg
  rw [g_eq_0]
  rw [show inner f (0 : H v e μ) = inner f 0 by rfl]
  rw [inner_zero_eq_zero f]
  rw [show norm (0 : H v e μ) = Real.sqrt (inner (0 : H v e μ) 0) by rfl]
  rw [inner_zero_eq_zero 0]
  simp

lemma ineq_add_norm : ‖f + g‖ <= ‖f‖ + ‖g‖ := by
  apply nonneg_le_nonneg_of_sq_le_sq
  · exact Left.add_nonneg (H_norm_nonneg f) (H_norm_nonneg g)
  rw [show ‖f + g‖ * ‖f + g‖ = ‖f + g‖^2 by ring]
  rw [show (‖f‖ + ‖g‖) * (‖f‖ + ‖g‖) = (‖f‖ + ‖g‖)^2 by ring]

  have sq_ineq : ‖f‖^2 + (2 : ℝ) * inner f g + ‖g‖^2 <= (‖f‖ + ‖g‖)^2 := by {

    have cauchy_schwarz : 2 * inner f g <= 2 * (‖f‖ * ‖g‖) := by {
      have := H_cauchy_schwarz f g
      linarith
    }

    have ineq := add_le_add_right (add_le_add_left cauchy_schwarz (‖f‖^2)) (‖g‖^2)
    rwa [show ‖f‖^2 + (2 : ℝ) * (‖f‖ * ‖g‖) + ‖g‖^2 = (‖f‖ + ‖g‖)^2 by ring] at ineq
  }

  have distrib_norm := distrib_H_norm f g 1
  rw [show (2:ℝ) * (1:ℝ) * inner f g = 2 * inner f g by ring] at distrib_norm
  rw [show (1:ℝ)^2 * ‖g‖^2 = ‖g‖^2 by ring] at distrib_norm
  rw [←distrib_norm] at sq_ineq
  have one_mul_g_eq_g : (1 : ℝ) * g = g := by {
    ext x
    rw [show ((1 : ℝ) * g).1 x = (1 : ℝ) * g.1 x by rfl]
    rw [show (1 : ℝ) * g.1 x = g.1 x by ring]
  }
  rwa [one_mul_g_eq_g] at sq_ineq

end Inner


/-
  We show properties on the distance induced by the inner product of H.
-/

namespace Dist

open Inner Ring Group

variable {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f g : H v e μ)

lemma H_dist_self (a : H v e μ) : dist a a = 0 := by
  rw [show dist a a = norm (a - a) by rfl]
  have a_sub_a_eq_0 : a - a = 0 := by {
    rw [show a - a = a + (-1 : ℝ) * a by rfl]
    ext x
    rw [show (a + (-1 : ℝ) * a).1 x = a.1 x + ((-1 : ℝ) * a).1 x by rfl]
    rw [show ((-1 : ℝ) * a).1 x = (-1 : ℝ) * a.1 x by rfl]
    rw [show (0 : H v e μ).1 x = 0 by rfl]
    ring
  }
  rw [a_sub_a_eq_0]
  rw [show norm (0 : H v e μ) = Real.sqrt (inner (0 : H v e μ) 0) by rfl]
  rw [inner_zero_eq_zero]
  exact Real.sqrt_zero

lemma dist_rw (a b : H v e μ) : (dist a b) = Real.sqrt (∑' i, v.1 i * ((set_repr_ne a).some i - (set_repr_ne b).some i)^2) := by
  rw [show dist a b = norm (a - b) by rfl]
  rw [show norm (a - b) = Real.sqrt (H_inner (a - b) (a - b)) by rfl]
  unfold H_inner
  let repr := λ i ↦ (set_repr_ne a).some i + (-1 : ℝ) * (set_repr_ne b).some i
  have repr_a_minus_b : repr ∈ set_repr (a - b) := by {
    have repr_minus_b :
    (λ i ↦ (-1 : ℝ) * (set_repr_ne b).some i) ∈ set_repr ((-1 : ℝ) * b) :=
      ⟨mul_repr b (-1), mul_summable b (-1)⟩

    have repr_a_sub_b :
      (λ i ↦ (set_repr_ne a).some i + (set_repr_ne ((-1 : ℝ) * b)).some i) ∈ set_repr (a + (-1 : ℝ) * b) :=
        ⟨add_repr a ((-1 : ℝ) * b), add_summable a ((-1 : ℝ) * b)⟩

    rwa [unique_choice repr_minus_b] at repr_a_sub_b
  }
  rw [unique_choice repr_a_minus_b]
  let a_r := (set_repr_ne a).some
  let b_r := (set_repr_ne b).some
  simp_rw [show ∀ i, v.1 i * repr i * repr i = v.1 i * (repr i)^2 by intro i; ring]
  simp_rw[show ∀ i, v.1 i * (repr i)^2 = v.1 i * (a_r i - b_r i)^2 by intro i; ring]

lemma H_dist_comm (a b : H v e μ) : dist a b = dist b a := by
  rw [dist_rw a b, dist_rw b a]
  let a_r := (set_repr_ne a).some
  let b_r := (set_repr_ne b).some
  simp_rw [show ∀ i, v.1 i * (a_r i - b_r i)^2 = v.1 i * (b_r i - a_r i)^2 by intro i; ring]

lemma H_dist_nonneg (a b : H v e μ) : 0 <= dist a b := by
  rw [show dist a b = norm (a - b) by rfl]
  rw [show norm (a - b) = Real.sqrt (H_inner (a - b) (a - b)) by rfl]
  exact Real.sqrt_nonneg (H_inner (a - b) (a - b))

lemma H_eq_of_dist_eq_zero {a b : H v e μ} : dist a b = 0 → a = b := by
  intro zero_dist
  rw [show dist a b = norm (a - b) by rfl] at zero_dist
  rw [show norm (a - b) = Real.sqrt (inner (a - b) (a - b)) by rfl] at zero_dist
  rw [Real.sqrt_eq_zero (inner_nonneg (a - b))] at zero_dist
  have a_minus_b_eq_zero : a - b = 0 := null_inner_imp_null_f (a - b) zero_dist
  ext x
  have dif_imp_eq : a.1 x - b.1 x = 0 → a.1 x = b.1 x := by intro h; linarith
  apply dif_imp_eq
  rw [show a.1 x - b.1 x = a.1 x + (-1 : ℝ) * b.1 x by ring]
  rw [show (a - b) = a + (-1 : ℝ) * b by rfl] at a_minus_b_eq_zero
  have a_minus_b_eq_zero_val : (a + (-1 : ℝ) * b).1 = (0 : H v e μ).1 := congrArg Subtype.val a_minus_b_eq_zero
  rw [show (a + (-1 : ℝ) * b).1 = (λ x ↦ a.1 x + (-1 : ℝ) * b.1 x) by rfl] at a_minus_b_eq_zero_val
  rw [congrFun a_minus_b_eq_zero_val x]
  rfl

lemma H_dist_triangle (a b c : H v e μ) : dist a c ≤ dist a b + dist b c := by
  rw [show dist a c = norm (a - c) by rfl]
  rw [show dist a b = norm (a - b) by rfl]
  rw [show dist b c = norm (b - c) by rfl]
  have split_a_sub_c : a - c = (a - b) + (b - c) := by {
    ext x
    rw [show (a - b + (b - c)).1 x = (a - b).1 x + (b - c).1 x by rfl]
    rw [show (a - b).1 x = a.1 x + (-1:ℝ)*b.1 x by rfl]
    rw [show (b - c).1 x = b.1 x + (-1:ℝ)*c.1 x by rfl]
    rw [show a.1 x + -1 * b.1 x + (b.1 x + -1 * c.1 x) = a.1 x + (-1:ℝ)*c.1 x by ring]
    rw [show (a - c).1 x = a.1 x + (-1:ℝ)*c.1 x by rfl]
  }
  rw [split_a_sub_c]

  exact ineq_add_norm (a - b) (b - c)

end Dist

/-
 - We instanciate the `NormedAddCommGroup` and `InnerProductSpace ℝ` typeclasses for H.
-/

variable {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]

lemma coe_mul_nat_fun (f : H v e μ) (n : ℕ) : (λ (n : ℕ) (f : H v e μ) ↦ (n : ℝ) * f) n f = (n : ℝ) * f := by rfl

lemma coe_mul_int_fun (f : H v e μ) (z : ℤ) : (λ (z : ℤ) (f : H v e μ) ↦ (z : ℝ) * f) z f = (z : ℝ) * f := by rfl

lemma cast_nat_succ (n : ℕ) : ↑(n + 1) = (n : ℝ) + 1 := by simp

lemma mul_succ_eq (f : H v e μ) (n : ℕ) : ((n : ℝ) + 1) * f = ((n : ℝ) * f + f) := by
  ext x
  let n' := (n : ℝ)
  rw [show (n' * f + f).1 x = (n' * f).1 x + f.1 x by rfl]
  rw [show (n' * f).1 x = n' * f.1 x by rfl]
  rw [show ((n' + (1:ℝ)) * f).1 x = (n' + 1) * f.1 x by rfl]
  ring

noncomputable instance : NormedAddCommGroup (H v e μ) where
  dist := λ f g ↦ dist f g
  edist := λ f g ↦ ENNReal.ofReal (dist f g)
  norm := λ f ↦ norm f
  add := λ f g ↦ f + g
  add_assoc := Group.H_add_assoc
  zero_add := Group.H_zero_add
  add_zero := Group.H_add_zero
  nsmul := λ n f ↦ (n : ℝ) * f
  neg := λ f ↦ -f
  zsmul := λ z f ↦ (z : ℝ) * f
  add_left_neg := Group.H_add_left_neg
  add_comm := Group.H_add_comm
  dist_self := Dist.H_dist_self
  dist_comm := Dist.H_dist_comm
  dist_triangle := Dist.H_dist_triangle
  edist_dist := λ f g ↦ rfl
  eq_of_dist_eq_zero := Dist.H_eq_of_dist_eq_zero
  dist_eq := λ x y ↦ by rfl
  nsmul_zero := by {
    intro f
    rw [coe_mul_nat_fun f 0]
    rw [show ((0 : ℕ) : ℝ) = (0 : ℝ) by simp]
    ext x
    rw [show ((0:ℝ) * f).1 x = (0:ℝ) * f.1 x by rfl]
    rw [show (0 : H v e μ).1 x = 0 by rfl]
    ring
  }
  nsmul_succ := by {
    intro n f
    rw [coe_mul_nat_fun f (n+1), cast_nat_succ n, coe_mul_nat_fun f n]
    exact mul_succ_eq f n
  }
  zsmul_zero' := by {
    intro f
    rw [coe_mul_int_fun f 0]
    rw [Int.cast_zero]
    ext x
    rw [show ((0 : ℝ) * f).1 x = 0 * f.1 x by rfl]
    rw [show (0 : H v e μ).1 x = 0 by rfl]
    ring
  }
  zsmul_succ' := by {
    intro n f
    rw [show Nat.succ n = n + 1 by rfl]
    rw [coe_mul_int_fun f (Int.ofNat (n + 1))]
    rw [show (Int.ofNat (n + 1) : ℝ) = ↑(n + 1) by rfl]
    rw [cast_nat_succ n]
    rw [coe_mul_int_fun f (Int.ofNat n)]
    rw [show (Int.ofNat n : ℝ) = (n : ℝ) by rfl]
    exact mul_succ_eq f n
  }
  zsmul_neg' := by {
    intro n f
    rw [show Int.negSucc n = -(n + 1) by rfl]
    rw [show Nat.succ n = n + 1 by rfl]
    rw [coe_mul_int_fun f (-(n + 1))]
    rw [show -((λ (z:ℤ) (f:H v e μ) ↦ (z:ℝ) * f) (↑(n + 1)) f) = (-1 : ℝ) * ((λ (z:ℤ) (f:H v e μ) ↦ (z:ℝ) * f) (↑(n + 1)) f) by rfl]

    rw [show (↑(n + 1) : ℤ) = (n : ℤ) + 1 by rfl]
    rw [coe_mul_int_fun f (n + 1)]
    rw [show (↑((n : ℤ) + 1) : ℝ) = (n : ℝ) + 1 by simp]
    rw [show (↑(- ((n : ℤ) + 1)) : ℝ) = -((n : ℝ) + 1) by simp]
    ext x
    rw [show (-((n : ℝ) + (1 : ℝ)) * f).1 x = -((n : ℝ) + 1) * f.1 x by rfl]
    rw [show ( (-1 : ℝ) * ( ((n : ℝ) + (1 : ℝ)) * f ) ).1 x = (-1 : ℝ) * (((n : ℝ) + (1 : ℝ)) * f).1 x by rfl]
    rw [show (((n : ℝ) + (1 : ℝ)) * f).1 x = ((n : ℝ) + (1 : ℝ)) * f.1 x by rfl]
    ring
  }

open Inner

noncomputable instance : InnerProductSpace ℝ (H v e μ) where
smul := λ a f ↦ a * f
one_smul := by {
  intro b
  ext x
  rw [show ((1:ℝ) • b).1 x = (1:ℝ) * b.1 x by rfl]
  ring
}
mul_smul := by {
  intro x y b
  ext e
  rw [show ((x*y) • b).1 e = (x*y) * b.1 e by rfl]
  rw [show (x • y • b).1 e = x * y • b.1 e by rfl]
  rw [show y • b.1 e = y * b.1 e by rfl]
  ring
}
smul_zero := by {
  intro a
  ext x
  rw [show (a • (0 : H v e μ)).1 x = a * 0 by rfl]
  rw [show (0 : H v e μ).1 x = 0 by rfl]
  ring
}
smul_add := by {
  intro a f g
  ext x
  rw [show (a • (f + g)).1 x = a * (f + g).1 x by rfl]
  rw [show (f + g).1 x = f.1 x + g.1 x by rfl]
  rw [show (a • f + a • g).1 x = a * f.1 x + a * g.1 x by rfl]
  ring
}
add_smul := by {
  intro r s f
  ext x
  rw [show ((r + s) • f).1 x = (r + s) * f.1 x by rfl]
  rw [show (r • f + s • f).1 x = r * f.1 x + s * f.1 x by rfl]
  ring
}
zero_smul := by {
  intro f
  ext x
  rw [show ((0:ℝ) • f).1 x = (0:ℝ) * f.1 x by rfl]
  rw [show (0 : H v e μ).1 x = 0 by rfl]
  ring
}
norm_smul_le := by {
  intro r f
  apply le_of_eq
  rw [show r • f = r * f by rfl]
  rw [show ‖r‖ = |r| by rfl]
  rw [←mul_self_inj (H_norm_nonneg (r * f)) (Left.mul_nonneg (abs_nonneg r) (H_norm_nonneg (f)))]
  rw [show ‖r * f‖ * ‖r * f‖ = ‖r * f‖^2 by ring]
  rw [show |r| * ‖f‖ * (|r| * ‖f‖) = (|r| * ‖f‖)^2 by ring]
  rw [←inner_eq_sq_norm (r * f), inner_mul_left f (r * f) r]
  rw [inner_symmetric, inner_mul_left f f r, inner_eq_sq_norm]
  rw [show r * (r * ‖f‖^2) = r^2 * ‖f‖^2 by ring, ←sq_abs r]
  ring
}
inner := H_inner
norm_sq_eq_inner := by {
  intro f
  rw [←inner_eq_sq_norm]
  rfl
}
conj_symm := by {
  intro f g
  rw [inner_symmetric f g]
  rfl
}
add_left := by {
  intro f g h
  exact H_inner_add_left f g h
}
smul_left := by {
  intro f g r
  rw [show r • f = r * f by rfl]
  exact inner_mul_left f g r
}


/- --- MERCER --- -/
/-
  Given the Mercer's theorem, we prove that H, endowed with k is a RKHS.
-/

def mercer (v : eigen) (e : ℕ → Ω → ℝ) (k : Ω → Ω → ℝ) := ∀ s, (k s = λ t ↦ ∑' i, v.1 i * e i s * e i t) ∧ (∀ t, Summable (fun i ↦ v.1 i * e i s * e i t))

lemma k_repr {v : eigen} {e : ℕ → Ω → ℝ} {k : Ω → Ω → ℝ} (h_mercer : mercer v e k) : ∀ s, f_repr v e (k s) (λ i ↦ e i s) := λ s ↦ ⟨(h_mercer s).1, λ t ↦ (h_mercer s).2 t⟩

lemma k_summable {v : eigen} {e : ℕ → Ω → ℝ} {k : Ω → Ω → ℝ} (h_mercer : mercer v e k) : ∀ s, Summable (λ i ↦ (v.1 i) * (e i s)^2) := by
  intro s
  simp_rw [show ∀ i, v.1 i * (e i s)^2 = v.1 i * (e i s) * (e i s) by intro i; ring]
  exact (h_mercer s).2 s

lemma k_i_H {v : eigen} {e : ℕ → Ω → ℝ} {k : Ω → Ω → ℝ} (h_mercer : mercer v e k) (hk_l2 : ∀ s, k s ∈ L2 μ) : ∀ s, k s ∈ H v e μ :=
  λ s ↦ ⟨hk_l2 s, (λ i ↦ e i s), k_repr h_mercer s, k_summable h_mercer s⟩

lemma k_repro {v : eigen} {e : ℕ → Ω → ℝ} {k : Ω → Ω → ℝ}
    (h_mercer : mercer v e k) (hk_l2 : ∀ s, k s ∈ L2 μ) :
    ∀ f, (hf : f ∈ H v e μ) → ∀ x, f x = inner (⟨f, hf⟩ : H v e μ) ⟨k x, k_i_H h_mercer hk_l2 x⟩ := by
  intro f hf x
  let f_H : H v e μ := ⟨f, hf⟩
  let k_H : H v e μ := ⟨k x, k_i_H h_mercer hk_l2 x⟩
  rw [show inner f_H k_H = H_inner f_H k_H by rfl]
  unfold H_inner
  let a_f := (set_repr_ne f_H).some
  have : (set_repr_ne k_H).some = (λ i ↦ e i x) :=
    unique_choice ⟨k_repr h_mercer x, k_summable h_mercer x⟩
  rw [this]
  suffices f = fun x ↦ ∑' (i : ℕ), v.1 i * a_f i * e i x by exact congrFun this x
  exact (Set.Nonempty.some_mem (set_repr_ne f_H)).1.1

variable (k : Ω → Ω → ℝ) (v : eigen) (e : ℕ → Ω → ℝ) (h_mercer : mercer v e k) (hk_l2 : ∀ s, k s ∈ L2 μ)

instance : RKHS (H v e μ) where
  k := k
  memb := k_i_H h_mercer hk_l2
  repro := k_repro h_mercer hk_l2
