import LeanVerification.StieltjesMoments
import Mathlib.MeasureTheory.Measure.Typeclasses.NoAtoms
import Mathlib.Analysis.Complex.Basic

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace LeanVerification.SpectralAtoms

/-- A positive reference measure that retains both the continuous input
and every pole location. The signed coefficients reside in its density. -/
def reference {N : ℕ} (μ : Measure ℝ) (t : Fin N → ℝ) : Measure ℝ :=
  μ + ∑ j : Fin N, Measure.dirac (t j)

def density {N : ℕ} (ν : ℝ → ℝ) (t A : Fin N → ℝ) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ Set.range t then ∑ j : Fin N, if t j = x then A j else 0 else ν x

theorem measurable_density {N : ℕ} {ν : ℝ → ℝ} (hν : Measurable ν) (t A : Fin N → ℝ) :
    Measurable (density ν t A) := by
  classical
  unfold density
  apply Measurable.ite (Set.finite_range t).measurableSet _ hν
  apply Finset.measurable_sum
  intro j hj
  exact Measurable.ite (measurableSet_eq_fun measurable_const measurable_id)
    measurable_const measurable_const

theorem density_at_atom {N : ℕ} (ν : ℝ → ℝ) {t : Fin N → ℝ}
    (ht : Function.Injective t) (A : Fin N → ℝ) (j : Fin N) :
    density ν t A (t j) = A j := by
  classical
  simp only [density, Set.mem_range_self, if_true, ht.eq_iff]
  simp

theorem density_eq_ae {N : ℕ} (μ : Measure ℝ) [NoAtoms μ]
    (ν : ℝ → ℝ) (t A : Fin N → ℝ) : density ν t A =ᵐ[μ] ν := by
  have hn : ∀ᵐ x ∂μ, x ∉ Set.range t := by
    rw [ae_iff]
    simpa only [not_not] using (Set.finite_range t).measure_zero μ
  filter_upwards [hn] with x hx
  simp only [density, if_neg hx]

theorem integrable_completed {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure ℝ) [NoAtoms μ]
    (ν : ℝ → ℝ) (t A : Fin N → ℝ) (g : ℝ → E)
    (hcont : Integrable (fun x => ν x • g x) μ) :
    Integrable (fun x => density ν t A x • g x) (reference μ t) := by
  rw [reference, integrable_add_measure]
  constructor
  · apply hcont.congr
    filter_upwards [density_eq_ae μ ν t A] with x hx
    rw [hx]
  · apply integrable_finset_sum_measure.mpr
    intro j hj
    exact integrable_dirac

/-- The constructed complete input has exactly the continuous integral
plus the signed finite atom sum, for any integrable vector-valued kernel. -/
theorem integral_completed {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure ℝ) [NoAtoms μ]
    (ν : ℝ → ℝ) {t : Fin N → ℝ} (ht : Function.Injective t) (A : Fin N → ℝ)
    (g : ℝ → E) (hcont : Integrable (fun x => ν x • g x) μ) :
    (∫ x, density ν t A x • g x ∂(reference μ t)) =
      (∫ x, ν x • g x ∂μ) + ∑ j, A j • g (t j) := by
  have hi := integrable_completed μ ν t A g hcont
  unfold reference at hi ⊢
  rw [integral_add_measure (integrable_add_measure.mp hi).1 (integrable_add_measure.mp hi).2,
    integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  congr 1
  · apply integral_congr_ae
    filter_upwards [density_eq_ae μ ν t A] with x hx
    rw [hx]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_dirac, density_at_atom ν ht A j]

/-- Exact absolute mass, including the atom coefficients. Distinct pole
locations are combined before this construction, as required by injectivity. -/
theorem integral_norm_completed {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (μ : Measure ℝ) [NoAtoms μ]
    (ν : ℝ → ℝ) {t : Fin N → ℝ} (ht : Function.Injective t) (A : Fin N → ℝ)
    (g : ℝ → E) (hcont : Integrable (fun x => ν x • g x) μ) :
    (∫ x, ‖density ν t A x • g x‖ ∂(reference μ t)) =
      (∫ x, ‖ν x • g x‖ ∂μ) + ∑ j, ‖A j • g (t j)‖ := by
  have hi := (integrable_completed μ ν t A g hcont).norm
  unfold reference at hi ⊢
  rw [integral_add_measure (integrable_add_measure.mp hi).1 (integrable_add_measure.mp hi).2,
    integral_finset_sum_measure (fun _ _ => integrable_dirac)]
  congr 1
  · apply integral_congr_ae
    filter_upwards [density_eq_ae μ ν t A] with x hx
    rw [hx]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_dirac, density_at_atom ν ht A j]

def coefficient (A t : ℝ) : ℝ := Real.pi * A * Real.sqrt t

theorem coefficient_weight {A t : ℝ} (ht : 0 < t) :
    coefficient A t * t ^ (-(3 : ℝ) / 2) = Real.pi * A / t := by
  rw [coefficient, Real.sqrt_eq_rpow]
  rw [mul_assoc, ← Real.rpow_add ht]
  norm_num
  rw [Real.rpow_neg_one]
  ring

theorem coefficient_moment {A t r : ℝ} (ht : 0 < t) :
    (coefficient A t * t ^ (-r - (3 : ℝ) / 2)) / Real.pi = A * t ^ (-r - 1) := by
  rw [coefficient, Real.sqrt_eq_rpow]
  rw [mul_assoc, ← Real.rpow_add ht]
  have he : (1 : ℝ) / 2 + (-r - 3 / 2) = -r - 1 := by ring
  rw [he]
  field_simp
  ring

theorem coefficient_width_kernel {A t : ℝ} {z : ℂ} (ht : 0 < t) :
    ((coefficient A t : ℝ) : ℂ) /
      ((Real.pi : ℂ) * (Real.sqrt t : ℂ) * ((t : ℂ) - z)) =
      (A : ℂ) / ((t : ℂ) - z) := by
  unfold coefficient
  push_cast
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs : (Real.sqrt t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr ht).ne'
  by_cases hz : (t : ℂ) = z
  · rw [hz, sub_self]
    simp
  · field_simp [hp, hs, sub_ne_zero.mpr hz]
    <;> ring

theorem completed_weighted_mass {N : ℕ} (μ : Measure ℝ) [NoAtoms μ]
    (ν : ℝ → ℝ) {t : Fin N → ℝ} (ht : Function.Injective t) (hp : ∀ j, 0 < t j)
    (A : Fin N → ℝ)
    (hcont : Integrable (fun x => ν x * x ^ (-(3 : ℝ) / 2)) μ) :
    (∫ x, ‖density ν t (fun j => coefficient (A j) (t j)) x * x ^ (-(3 : ℝ) / 2)‖
      ∂(reference μ t)) =
      (∫ x, ‖ν x * x ^ (-(3 : ℝ) / 2)‖ ∂μ) +
        Real.pi * ∑ j, |A j| / t j := by
  have he := integral_norm_completed μ ν ht (fun j => coefficient (A j) (t j))
    (fun x => x ^ (-(3 : ℝ) / 2)) hcont
  simp only [smul_eq_mul, coefficient_weight] at he
  rw [he, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [coefficient_weight (hp j)]
  simp only [norm_div, norm_mul, Real.norm_of_nonneg Real.pi_pos.le,
    Real.norm_eq_abs, abs_of_pos (hp j)]
  ring

theorem completed_normalizedMoment {N : ℕ} (μ : Measure ℝ) [NoAtoms μ]
    {ν : ℝ → ℝ} {H r : ℝ} (hH : 0 < H) (hr : 0 ≤ r) (hν : Measurable ν)
    (hsupp : ∀ᵐ x ∂μ, H ≤ x) {t : Fin N → ℝ} (ht : Function.Injective t)
    (hp : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    (hcont : Integrable (fun x => ν x * x ^ (-(3 : ℝ) / 2)) μ) :
    Stieltjes.normalizedMoment (reference μ t)
      (density ν t (fun j => coefficient (A j) (t j))) r =
      Stieltjes.normalizedMoment μ ν r + ∑ j, A j * (t j) ^ (-r - 1) := by
  have hi := Stieltjes.integrable_weightedMoment hH hr hν hsupp hcont
  have he := integral_completed μ ν ht (fun j => coefficient (A j) (t j))
    (fun x => x ^ (-r - (3 : ℝ) / 2)) hi
  unfold Stieltjes.normalizedMoment Stieltjes.weightedMoment
  simp only [smul_eq_mul] at he
  rw [he, add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact coefficient_moment (hH.trans_le (hp j))

/-- The ordinary simple-pole residue, expressed by its defining punctured
limit, is minus the coefficient used in `A/(t-z)`. -/
theorem simple_pole_residue (A t : ℂ) :
    Tendsto (fun z : ℂ => (z - t) * (A / (t - z))) (𝓝[≠] t) (𝓝 (-A)) := by
  have he : (fun z : ℂ => (z - t) * (A / (t - z))) =ᶠ[𝓝[≠] t] fun _ => -A := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzt : z ≠ t := hz
    field_simp [sub_ne_zero.mpr hzt, sub_ne_zero.mpr hzt.symm]
    <;> ring
  exact Tendsto.congr' he.symm tendsto_const_nhds

end LeanVerification.SpectralAtoms
