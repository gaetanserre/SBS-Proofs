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
set_option maxHeartbeats 600000

variable {d : ℕ} {Ω : Set (Vector ℝ d)} [MeasureSpace Ω]

--variable (k : Ω → Ω → ℝ) (e : ℕ → ℝ) (ϕ : ℕ → Ω → ℝ)

--def L2 (μ : Measure Ω) := {f : Ω → ℝ | ∃ C, ∫ x, |f x|^2 ∂μ <= C}

def L2 (μ : Measure Ω) [IsFiniteMeasure μ] := {f : Ω → ℝ | Memℒp f 2 μ}

/- theorem mercer (x y : Ω) : Summable ((e ·) * (ϕ · x) * (ϕ · y)) ∧  k x y = ∑' i, (e i) * (ϕ i x) * (ϕ i y) := by sorry -/

def eigen := {e : ℕ → ℝ // ∀ i, 0 <= e i}

def f_repr (v : eigen) (e : ℕ → Ω → ℝ) (f : Ω → ℝ) (a : ℕ → ℝ) := (f = λ x ↦ (∑' i, (v.1 i) * (a i) * (e i x))) ∧ (∀ x, Summable (λ i ↦ (v.1 i) * (a i) * (e i x)))

def H (v : eigen) (e : ℕ → Ω → ℝ) (μ : Measure Ω) [IsFiniteMeasure μ] := {f | f ∈ L2 μ ∧ ∃ (a : ℕ → ℝ), (f_repr v e f a) ∧ Summable (λ i ↦ (v.1 i) * (a i)^2)}

def set_repr {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f : H v e μ) := {a : ℕ → ℝ | (f_repr v e f.1 a) ∧ (Summable (λ i ↦ (v.1 i) * (a i)^2))}

lemma set_repr_ne {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f : H v e μ) : (set_repr f).Nonempty := by
  rcases f.2 with ⟨_, ⟨a, ha⟩⟩
  use a
  exact ha

axiom set_repr_unique {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] {f : H v e μ} {a b : ℕ → ℝ} (ha : a ∈ set_repr f) (hb : b ∈ set_repr f) : a = b

lemma unique_choice {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] {f : H v e μ} {a : ℕ → ℝ} (h : a ∈ set_repr f) : (set_repr_ne f).some = a := set_repr_unique (set_repr_ne f).some_mem h

noncomputable def H_inner {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f g : H v e μ) : ℝ := ∑' i, (v.1 i) * ((set_repr_ne f).some i) * ((set_repr_ne g).some i)

variable {v : eigen} {e : ℕ → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] (f g : H v e μ)

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
  have hf : ∀ b ∉ (∅ : Finset ℕ), (λ (i : ℕ) ↦ (0 : ℝ)) b = 0 := by {
    intro b b_not_in
    rfl
  }
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

axiom inner_summable : Summable (λ i ↦ (v.1 i) * ((set_repr_ne f).some i) * ((set_repr_ne g).some i))

/--
 - ∀ f, 0 <= ⟨f, f⟩
-/
lemma inner_nonneg : 0 <= H_inner f f := by
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

lemma inner_symmetric : H_inner f g = H_inner g f := by
  unfold H_inner
  have comm : ∀ i, (v.1 i) * ((set_repr_ne f).some i) * ((set_repr_ne g).some i) = (v.1 i) * ((set_repr_ne g).some i) * ((set_repr_ne f).some i) := λ i ↦ by ring
  simp_rw [comm]

lemma inner_zero_eq_zero : H_inner f 0 = 0 := by
  unfold H_inner
  rw [zero_unique_repr]

  have summand_eq_zero : ∀ i, v.1 i * (set_repr_ne f).some i * (λ i ↦ 0) i = 0 := by {
    intro i
    rw [show (λ (i : ℕ) ↦ (0 : ℝ)) i = 0 by rfl]
    ring
  }
  simp_rw [summand_eq_zero]
  exact tsum_zero

lemma null_inner_imp_null_f : H_inner f f = 0 → f = 0 := by
  intro inner_eq_0
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

  ext x
  rw [show (0 : H v e μ).1 = zero by rfl]
  rw [show zero x = 0 by rfl]
  rcases (set_repr_ne f).some_mem with ⟨⟨ha_r, ha_s⟩, _⟩
  rw [ha_r, show (set_repr_ne f).some = a by rfl]

  have summand_eq_0 : ∀ i, (v.1 i) * (a i) * (e i x) = 0 := by {
    intro i
    rw [prod_v_a_eq_0]
    ring
  }

  simp_rw [summand_eq_0]
  exact tsum_zero

lemma prod_f_repr (a : ℝ) : f_repr v e (λ x ↦ a * f.1 x) (λ i ↦ a * (set_repr_ne f).some i) := by
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

lemma prod_f_summable (a : ℝ) : Summable (λ i ↦ v.1 i * (λ i ↦ a * (set_repr_ne f).some i) i ^ 2) := by
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
  refine ⟨g_in_L2, g_h, prod_f_repr f a, prod_f_summable f a⟩

instance : HMul ℝ (H v e μ) (H v e μ) where
  hMul := λ a f ↦ ⟨λ x ↦ a * f.1 x, mul_in_H f a⟩

example (a : ℝ) : H_inner (a * f) g = a * H_inner f g := by
  let h := (set_repr_ne f).some
  let h_af := λ i ↦ a * h i

  have h_af_in : h_af ∈ set_repr (a * f) := ⟨prod_f_repr f a, prod_f_summable f a⟩
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


/--
  ∀ f, g ∈ H, f + g ∈ L2. Assume it.
-/
lemma add_in_L2 : (λ x ↦ f.1 x + g.1 x) ∈ L2 μ := by sorry


lemma add_summable : Summable (λ i ↦ v.1 i * ((set_repr_ne f).some i + (set_repr_ne g).some i)^2) := by sorry

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
  exact Summable.add (af_repr.2 x) (ag_repr.2 x)

lemma add_in_H : (λ x ↦ f.1 x + g.1 x) ∈ H v e μ := by
  let h := λ i ↦ (set_repr_ne f).some i + (set_repr_ne g).some i
  exact ⟨add_in_L2 f g, h, add_repr f g, add_summable f g⟩

instance : HAdd (H v e μ) (H v e μ) (H v e μ) where
  hAdd := λ f g ↦ ⟨(λ x ↦ f.1 x + g.1 x), add_in_H f g⟩

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

noncomputable instance : Norm (H v e μ) where
  norm := λ f ↦ Real.sqrt (H_inner f f)

instance : HSub (H v e μ) (H v e μ) (H v e μ) where
  hSub := λ f g ↦ f + (-1 : ℝ) * g

instance : Neg (H v e μ) where
  neg := λ f ↦ (-1 : ℝ) * f

lemma H_add_left_neg (a : H v e μ) : -a + a = 0 := by
  rw [show -a = (-1 : ℝ) * a by rfl]
  ext x
  rw [show ((-1 : ℝ) * a + a).1 x = ((-1 : ℝ) * a).1 x + a.1 x by rfl]
  rw [show ((-1 : ℝ) * a).1 x = (-1 : ℝ) * a.1 x by rfl]
  rw [show (0 : H v e μ).1 x = 0 by rfl]
  ring

noncomputable instance : Dist (H v e μ) where
  dist := λ f g ↦ norm (f - g)

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
  rw [show norm (0 : H v e μ) = Real.sqrt (H_inner 0 0) by rfl]
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
      ⟨prod_f_repr b (-1), prod_f_summable b (-1)⟩

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
  rw [show norm (a - b) = Real.sqrt (H_inner (a - b) (a - b)) by rfl] at zero_dist
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
  let a_r := (set_repr_ne a).some
  let b_r := (set_repr_ne b).some
  let c_r := (set_repr_ne c).some

  have apply_sq : (dist a c)^2 ≤ (dist a b + dist b c)^2 → dist a c ≤ dist a b + dist b c := by {
    intro h
    rw [show (dist a c)^2 = (dist a c) * (dist a c) by ring] at h
    rw [show (dist a b + dist b c)^2 = (dist a b + dist b c) * (dist a b + dist b c) by ring] at h
    exact nonneg_le_nonneg_of_sq_le_sq (Left.add_nonneg (H_dist_nonneg a b) (H_dist_nonneg b c)) h
  }
  apply apply_sq

  rw [dist_rw a c, dist_rw a b, dist_rw b c]
  rw [show (set_repr_ne a).some = a_r by rfl]
  rw [show (set_repr_ne b).some = b_r by rfl]
  rw [show (set_repr_ne c).some = c_r by rfl]

  have sum_nonneg : (0 : ℝ) ≤ ∑' (i : ℕ), v.1 i * (a_r i - c_r i)^2 := by {
    have nonneg : ∀ i, (0 : ℝ) <= v.1 i * (a_r i - c_r i)^2 := by {
      intro i
      exact Left.mul_nonneg (v.2 i) (sq_nonneg _)
    }
    exact tsum_nonneg nonneg
  }
  rw [Real.sq_sqrt sum_nonneg]

  have trans1 : ∀ i, v.1 i * (a_r i - c_r i)^2 = v.1 i * (a_r i - b_r i)^2 +( v.1 i * (2:ℝ) * (a_r i - b_r i) * (b_r i - c_r i) + v.1 i * (b_r i - c_r i)^2) := by intro i; ring

  have s1 : Summable (λ i ↦ v.1 i * (a_r i - b_r i)^2) := by sorry
  have s2 : Summable (λ i ↦ v.1 i * (2:ℝ) * (a_r i - b_r i) * (b_r i - c_r i) + v.1 i * (b_r i - c_r i)^2) := by sorry

  simp_rw [trans1]
  rw [tsum_add s1 s2]
  have s3 : Summable (λ i ↦ v.1 i * 2 * (a_r i - b_r i) * (b_r i - c_r i)) := by sorry
  have s4 : Summable (λ i ↦ v.1 i * (b_r i - c_r i)^2) := by sorry
  rw [tsum_add s3 s4]

  simp_rw [show ∀ b : ℕ, v.1 b * 2 * (a_r b - b_r b) * (b_r b - c_r b) = 2 * v.1 b * (a_r b - b_r b) * (b_r b - c_r b) by intro b; ring]



  --tsum_mul_left

  sorry

lemma H_nsmul_zero : ∀ (x : ↑(H v e μ)), (fun (n:ℤ) (f : H v e μ) ↦ (n:ℝ) * f) 0 x = (0 : H v e μ) := by sorry

lemma H_nsmul_succ : ∀ (n : ℕ) (x : ↑(H v e μ)), (fun (n : ℤ) (f : H v e μ) ↦ (n:ℝ) * f) (n + 1) x = (fun (n : ℤ) (f : H v e μ) ↦ (n:ℝ) * f) lemma H_zsmul_zero' : ∀ (a : ↑(H v e μ)), (fun (z:ℤ) (f : H v e μ) ↦ (z:ℝ) * f) 0 a = 0 := by sorry

lemma H_zsmul_succ' : ∀ (n : ℕ) (a : ↑(H v e μ)), (fun (z:ℤ) (f : H v e μ) ↦ (z:ℝ) * f) (Int.ofNat (Nat.succ n)) a = (fun (z:ℤ) (f : H v e μ) ↦ (z:ℝ) * f) (Int.ofNat n) a + a := by sorry

lemma H_zsmul_neg' : ∀ (n : ℕ) (a : ↑(H v e μ)), (fun (z:ℤ) (f : H v e μ) ↦ (z:ℝ) * f) (Int.negSucc n) a = -(fun (z:ℤ) (f : H v e μ) ↦ (z:ℝ) * f) (↑(Nat.succ n)) a := by sorry

noncomputable instance : NormedAddCommGroup (H v e μ) where
  dist := λ f g ↦ dist f g
  edist := λ f g ↦ ENNReal.ofReal (dist f g)
  norm := λ f ↦ norm f
  add := λ f g ↦ f + g
  add_assoc := H_add_assoc
  zero_add := H_zero_add
  add_zero := H_add_zero
  nsmul := λ n f ↦ (n : ℝ) * f
  neg := λ f ↦ -f
  zsmul := λ z f ↦ (z : ℝ) * f
  add_left_neg := H_add_left_neg
  add_comm := H_add_comm
  dist_self := H_dist_self
  dist_comm := H_dist_comm
  dist_triangle := H_dist_triangle
  edist_dist := λ f g ↦ rfl
  eq_of_dist_eq_zero := H_eq_of_dist_eq_zero
  nsmul_zero := H_nsmul_zero
  nsmul_succ := H_nsmul_succ
  zsmul_zero' := H_zsmul_zero'
  zsmul_succ' := H_zsmul_succ'
  zsmul_neg' := H_zsmul_neg'
  toUniformSpace := by sorry
  uniformity_dist := by sorry
  toBornology := by sorry
  cobounded_sets := by sorry
  dist_eq := by sorry

noncomputable instance : InnerProductSpace ℝ (H v e μ) where
smul := λ a f ↦ a * f
one_smul := by sorry
mul_smul := by sorry
smul_zero := by sorry
smul_add := by sorry
add_smul := by sorry
zero_smul := by sorry
norm_smul_le := by sorry
inner := H_inner
norm_sq_eq_inner := by sorry
conj_symm := by sorry
add_left := by sorry
smul_left := by sorry
