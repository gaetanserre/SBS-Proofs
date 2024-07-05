/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/SBS-Proofs
-/

import Mathlib.Data.Real.EReal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner

import SBSProofs.Utils
import SBSProofs.Measure
import SBSProofs.RKHS.Basic

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open scoped RealInnerProductSpace
open BigOperators Finset ENNReal NNReal MeasureTheory RKHS

set_option maxHeartbeats 400000

/-
  We defined measures μ and π (ν is considered as the standard Lebesgue measure) along with their densities (finite and non-zero on the entire space)
-/
variable {d : ℕ} (hd : d ≠ 0) {Ω : Set (Vector ℝ d)}

variable [MeasureSpace Ω]

variable (μ π : DensityMeasure Ω) [IsProbabilityMeasure μ.toMeasure] [IsProbabilityMeasure π.toMeasure]

variable (hdμ : ∀x, μ.d x ≠ 0) (hdπ : ∀x, π.d x ≠ 0)

/-
  We define a RKHS of Ω → ℝ functions.
-/
variable (H₀ : Set (Ω → ℝ)) [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [s : RKHS H₀]

/--
We consider that the left-hand side of the equivalence holds for all x. In the future, we want to take into account that it only holds for almost all x w.r.t. μ.
-/
def positive_definite_kernel := ∀ (f : range d → Ω → ℝ), (0 ≤ ∫ x in Set.univ, (∫ x' in Set.univ, (∑ i ∈ Set.univ, f i x * s.k x x' * f i x') ∂μ.toMeasure) ∂μ.toMeasure) ∧ (∫ x in Set.univ, (∫ x' in Set.univ, (∑ i ∈ Set.univ, f i x * s.k x x' * f i x') ∂μ.toMeasure) ∂μ.toMeasure = 0 ↔ ∀i, ∀ᵐ x ∂ μ.toMeasure, f i x = 0)

variable (h_kernel_positive : positive_definite_kernel μ H₀)

/-===============================KERNEL STEIN DISCREPANCY===============================-/
/-
Here, we prove that KSD(μ | π) is a valid discrepancy measure and that π is the only fixed point of Φₜ(μ).
-/

/-
  From here, as the derivative of multivariate function are hard to define and to manipulate (defining the gradient, the divergence...), we define the gradient of *f* as follows:
  f  : Ω → ℝ
  df : range d → Ω → ℝ
       i ↦ x ↦ ∂xⁱ f(x)

  For vector-valued function, we defined them as follows:
  f  : range d → Ω → ℝ
       i ↦ x ↦ f(x)ⁱ
  df : range d → Ω → ℝ
       i ↦ x ↦ ∂xⁱ f(x)ⁱ

  Also, we assume some simple lemmas using the above formalism. Sometimes, these lemmas are not rigorously defined but, in our framework, it is more than enough.
-/

/- dk : x ↦ i ↦ y ↦ ∂xⁱ k(x, y) -/
variable (dk : Ω → range d → Ω → ℝ)

/- d_ln_π : i ↦ x ↦ ∂xⁱ ln (μ(x) / π(x)) -/
variable (d_ln_π : range d → Ω → ℝ)

/-
  Definition of the steepest direction ϕ and its derivative.
-/
variable (ϕ : product_RKHS H₀ hd) (dϕ : range d → Ω → ℝ)

/- As Ω is supposed to be compact, we will use this assumption only when the function is trivially integrable (e.g. continuous). -/
axiom is_integrable_H₀ : ∀ (f : Ω → ℝ), Integrable f μ.toMeasure
axiom is_integrable_H₀_volume : ∀ (f : Ω → ℝ), Integrable f
axiom is_measurable_H₀ : ∀ (f : Ω → ℝ), Measurable f
axiom is_measurable_H₀_enn : ∀ (f : Ω → ℝ≥0∞), Measurable f

/-
d_ln_π_μ : i ↦ x ↦ ∂xⁱ ln (π(x) / μ(x))
-/
variable (d_ln_π_μ : range d → Ω → ℝ)

/-
Simple derivative rule: if the derivative is 0 ∀x, then the function is constant.
-/
variable (hd_ln_π_μ : ∀ (ν : Measure Ω), (∀i, ∀ᵐ x ∂ν, d_ln_π_μ i x = 0) → (∃ c, ∀ᵐ x ∂ν, log (μ.d x / π.d x) = c))

/-
dπ' : i ↦ x ↦ ∂xⁱ π(x)
-/
variable (dπ' : range d → Ω → ℝ)

/-
Log-trick: ∂xⁱ ln (π(x)) * π(x) = ∂xⁱ π(x).
-/
variable (hπ' : ∀x, ∀i, ENNReal.toReal (π.d x) * d_ln_π i x = dπ' i x)


variable [Norm Ω]
/--
  Stein class of measure. f is in the Stein class of μ if, ∀i ∈ Set.univ, lim_(‖x‖ → ∞) μ(x) * ϕ(x)ⁱ = 0.
-/
def SteinClass (f : range d → Ω → ℝ) := ∀ x, tends_to_infty (λ (x : Ω) ↦ ‖x‖) → ∀i, ENNReal.toReal (μ.d x) * f i x = 0


/-
  Kernel Stein Discrepancy
-/
variable (KSD : Measure Ω → Measure Ω → ℝ)

/--
KSD(μ | π) = ⟪∇ln π/μ, Pμ ∇ln π/μ⟫_L²(μ). We assume here that KSD is also equal to ∫ x, ∑ i ∈ Set.univ, (d_ln_π i x * ϕ i x + dϕ i x) ∂μ.
-/
def is_ksd := KSD μ.toMeasure π.toMeasure = (∫ x in Set.univ, (∫ x' in Set.univ, (∑ i ∈ Set.univ, d_ln_π_μ i x * s.k x x' * d_ln_π_μ i x') ∂μ.toMeasure) ∂μ.toMeasure) ∧ (KSD μ.toMeasure π.toMeasure = ∫ x, ∑ i ∈ Set.univ, (d_ln_π i x * (ϕ i).1 x + dϕ i x) ∂μ.toMeasure)

/-
  KSD(μ | π) is originally defined as ‖ϕ^⋆‖²_H, it is therefore non-negative.
-/
def is_ksd_norm := KSD μ.toMeasure π.toMeasure = ‖ϕ‖^2

/-
  ϕ is in the Stein class of π
-/
variable (hstein : SteinClass π (λ i ↦ (ϕ i).1))

/--
  We show that, if ϕ is in the Stein class of π, KSD is a valid discrepancy measure i.e. μ = π ↔ KSD(μ | π) = 0.
-/
lemma KSD_is_valid_discrepancy (hksd : is_ksd hd μ π H₀ d_ln_π ϕ dϕ d_ln_π_μ KSD) : μ.toMeasure = π.toMeasure ↔ KSD μ.toMeasure π.toMeasure = 0 :=
by
  constructor
  -- μ = π ↦ KSD(μ | π) = 0.
  · intro h

    rw [hksd.right]

    -- ∑ i, f i + g i = ∑ i, f i + ∑ i, g i.
    have split_sum : ∀x, ∑ i ∈ Set.univ, (d_ln_π i x * (ϕ i).1 x + dϕ i x) = (∑ i ∈ Set.univ, d_ln_π i x * (ϕ i).1 x) + (∑ i ∈ Set.univ, dϕ i x) := λ x ↦ sum_add_distrib
    simp_rw [split_sum]

    -- Split the integral of sum into sum of integral.
    have h1 : Integrable (λ x ↦ (∑ i ∈ Set.univ, d_ln_π i x * (ϕ i).1 x)) μ.toMeasure := is_integrable_H₀ μ _
    have h2 : Integrable (λ x ↦ (∑ i ∈ Set.univ, dϕ i x)) μ.toMeasure := is_integrable_H₀ μ _
    rw [integral_add (h1) h2]

    -- Make the `Set.univ` appears for using the density later.
    have int_univ : ∫ a, ∑ i ∈ Set.univ, d_ln_π i a * (ϕ i).1 a ∂μ.toMeasure = ∫ a in Set.univ, ∑ i ∈ Set.univ, d_ln_π i a * (ϕ i).1 a ∂μ.toMeasure := by simp
    rw [int_univ]

    rw [remove_univ_integral μ.toMeasure (λ x ↦ ∑ i ∈ Set.univ, d_ln_π i x * (ϕ i).1 x)]

    -- Replace μ by π in the integration.
    rw [h]

    -- Replace by its density.
    have hi := is_integrable_H₀ π (λ x ↦ ∑ i ∈ Set.univ, d_ln_π i x * (ϕ i).1 x)

    rw [π.density_integration hi (is_measurable_H₀_enn _) (is_measurable_H₀_enn _) (is_integrable_H₀_volume _)]

    -- Get ENNReal.toReal (π.d x) in the sum (a * ∑ b = ∑ b * a).
    have mul_dist : ∀x, ENNReal.toReal (π.d x) * (∑ i ∈ Set.univ, (λ i ↦ d_ln_π i x * (ϕ i).1 x) i) = ∑ i ∈ Set.univ, (λ i ↦ d_ln_π i x * (ϕ i).1 x) i * ENNReal.toReal (π.d x) := by {

      have mul_dist_sum : ∀ (a : ℝ), ∀ (f : range d → ℝ), (∑ i ∈ Set.univ, f i) * a = ∑ i ∈ Set.univ, f i * a := λ a f ↦ sum_mul (Set.toFinset Set.univ) (λ i ↦ f i) a
      intro x
      rw [mul_comm]
      exact mul_dist_sum (ENNReal.toReal (π.d x)) (λ i ↦ d_ln_π i x * (ϕ i).1 x)
    }
    simp_rw [mul_dist]

    -- Make the product ENNReal.toReal (π.d x) * d_ln_π i x appears to use the ln derivative rule.
    have mul_comm : ∀x, ∀i, d_ln_π i x * (ϕ i).1 x * ENNReal.toReal (π.d x) = ENNReal.toReal (π.d x) * d_ln_π i x * (ϕ i).1 x := λ x i ↦ (mul_rotate (ENNReal.toReal (π.d x)) (d_ln_π i x) ((ϕ i).1 x)).symm
    simp_rw [mul_comm, hπ']

    -- Make the `Set.univ` appears to use the density.
    have int_univ : ∫ a, ∑ i ∈ Set.univ, dϕ i a ∂π.toMeasure = ∫ a in Set.univ, ∑ i ∈ Set.univ, dϕ i a ∂π.toMeasure := by simp
    rw [int_univ]

    rw [remove_univ_integral π.toMeasure (λ x ↦ ∑ i ∈ Set.univ, dϕ i x)]
    have hi := is_integrable_H₀ π (λ x ↦ ∑ i ∈ Set.univ, dϕ i x)
    rw [π.density_integration hi (is_measurable_H₀_enn _) (is_measurable_H₀_enn _) (is_integrable_H₀_volume _)]

    -- Use the integration by parts on the right-hand side integral.

    rw [mv_integration_by_parts volume (λ x ↦ ENNReal.toReal (π.d x)) (λ i ↦ (ϕ i).1) dπ' dϕ (hstein)]
    simp

  -- KSD(μ | π) = 0 ↦ μ = π.
  intro h
  rw [hksd.left] at h

  -- We use the fact that the kernel is positive-definite that implies that d_ln_π_μ = 0.
  have d_ln_π_μ_eq_0 := (h_kernel_positive d_ln_π_μ).right.mp h

  -- Simple derivative rule: ∂x f x = 0 → f x = c
  specialize hd_ln_π_μ μ.toMeasure d_ln_π_μ_eq_0

  rcases hd_ln_π_μ with ⟨c, h⟩

  -- We show that, since, for almost all x, log (μ.d x / π.d x) = c, then μ.d x = exp(x) * π.d x. We show that the two sets are equal to show that the right-hand side one of of null measure.
  have dμ_propor : ∀ᵐ x ∂μ.toMeasure, μ.d x = ENNReal.ofReal (Real.exp c) * π.d x := by {
    have eq_sets : {x | log (μ.d x / π.d x) = c} = {x | μ.d x = ENNReal.ofReal (Real.exp c) * π.d x} := by {
      ext x
      constructor
      · intro (hx : log (μ.d x / π.d x) = c)
        have frac_neq_zero : μ.d x / π.d x ≠ 0 := by {
          have frac_pos : 0 < μ.d x / π.d x := ENNReal.div_pos_iff.mpr ⟨hdμ x, π.d_neq_top x⟩
          exact zero_lt_iff.mp frac_pos
        }

        have frac_finite : μ.d x / π.d x ≠ ∞ := by {
          by_contra h
          rw [div_eq_top] at h
          cases h with
            | inl hp => {
              rcases hp with ⟨_, hpr⟩
              exact hdπ x hpr
            }
            | inr hq => {
              rcases hq with ⟨hql, _⟩
              exact μ.d_neq_top x hql
            }
        }

        have cancel_log_exp : μ.d x / π.d x = ENNReal.ofReal (Real.exp c) := cancel_log_exp (μ.d x / π.d x) frac_neq_zero frac_finite c hx
        simp [←cancel_log_exp, ENNReal.div_eq_inv_mul, mul_right_comm (π.d x)⁻¹ (μ.d x) (π.d x), ENNReal.inv_mul_cancel (hdπ x) (π.d_neq_top x)]

      intro (hx : μ.d x = ENNReal.ofReal (Real.exp c) * π.d x)

      have log_exp := enn_comp_log_exp c

      have frac : μ.d x / π.d x = ENNReal.ofReal (Real.exp c) := by {
        rw [hx, mul_div_assoc (ENNReal.ofReal (Real.exp c)) (π.d x) (π.d x)]
        rw [show (π.d x) / (π.d x) = (π.d x) * (π.d x)⁻¹ by rfl]
        rw [ENNReal.mul_inv_cancel (hdπ x) (π.d_neq_top x)]
        simp
      }

      rwa [←frac] at log_exp
    }
    have null_measure : μ {x | log (μ.d x / π.d x) = c}ᶜ = 0 := h
    rwa [congrArg compl eq_sets] at null_measure
  }

  -- We show by contradiction that ENNReal.ofReal (Real.exp c) = 1. If it is ≠ 1, this implies a contradiction as μ.d x = ENNReal.ofReal (Real.exp c) * π.d x and ∫⁻ x, μ.d x ∂ν = 1.
  have exp_c_eq_one : ENNReal.ofReal (Real.exp c) = 1 := by {
    by_contra hc; push_neg at hc
    have univ_eq_one_μ : ∫⁻ _, 1 ∂μ.toMeasure = 1 := by simp
    have univ_eq_one_π : ∫⁻ _, 1 ∂π.toMeasure = 1 := by simp

    rw [μ.density_lintegration (λ _ ↦ 1) (is_measurable_H₀_enn (λ _ ↦ 1))] at univ_eq_one_μ

    have ae_μ_to_ae_volume := (DensityMeasure.ae_density_measure_iff_ae_volume (ae_of_all _ hdμ)).mp dμ_propor

    simp_rw [mul_one] at univ_eq_one_μ
    rw [lintegral_congr_ae ae_μ_to_ae_volume] at univ_eq_one_μ

    rw [π.density_lintegration (λ _ ↦ 1) (is_measurable_H₀_enn (λ _ ↦ 1))] at univ_eq_one_π
    simp_rw [mul_one] at univ_eq_one_π

    rw [lintegral_const_mul (ENNReal.ofReal (Real.exp c)) (π.d_measurable), univ_eq_one_π, mul_one] at univ_eq_one_μ
    exfalso
    exact hc univ_eq_one_μ
  }

  -- We rewrite μ = π as ∀s, ∫⁻ x in s, μ.d ∂ν = ∀s, ∫⁻ x in s, π.d ∂ν and use μ.d = 1 * π.d.
  simp_rw [exp_c_eq_one, one_mul] at dμ_propor
  have d_volume_propor : ∀ᵐ x, μ.d x = π.d x := (μ.ae_density_measure_iff_ae_volume (ae_of_all _ hdμ)).mp dμ_propor
  exact DensityMeasure.densities_ae_eq_iff_eq_measure.mp d_volume_propor

/--
  π is the only fixed point of Φₜ(μ). We proved that by showing that, if μ = π, ϕ^* = 0 and ϕ^* ≠ 0 otherwise.
-/
lemma π_unique_fixed_point (hksd : is_ksd hd μ π H₀ d_ln_π ϕ dϕ d_ln_π_μ KSD) (ksd_norm : is_ksd_norm hd μ π H₀ ϕ KSD) : (μ.toMeasure = π.toMeasure → ∀ i, ϕ i = 0) ∧ (μ.toMeasure ≠ π.toMeasure → ∃ i, ϕ i ≠ 0) :=
by
  have KSD_discrepancy := KSD_is_valid_discrepancy hd μ π hdμ hdπ H₀ h_kernel_positive d_ln_π ϕ dϕ d_ln_π_μ hd_ln_π_μ dπ' hπ' KSD hstein hksd
  constructor
  {
    -- μ = π → ϕ^* = 0
    intro μ_eq_π

    rw [ksd_norm, sq_eq_zero_iff, norm_eq_zero_iff ϕ] at KSD_discrepancy
    exact KSD_discrepancy.mp μ_eq_π
  }
  {
    -- μ ≠ π → ϕ^* ≠ 0
    intro μ_neq_π
    by_contra h; push_neg at h

    rw [←norm_eq_zero_iff ϕ, ←sq_eq_zero_iff, ←ksd_norm] at h
    exact μ_neq_π (KSD_discrepancy.mpr h)
  }
