import LeanVerification.StieltjesMoments
import Mathlib.MeasureTheory.Measure.MutuallySingular

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.Stieltjes

noncomputable section

/-- The sign of a signed input relative to the sum of its mutually singular
positive and negative variations. The variations may have infinite total mass. -/
def signedDensity {μ ν : Measure ℝ} (h : μ ⟂ₘ ν) (x : ℝ) : ℝ := by
  classical
  exact if x ∈ h.nullSet then -1 else 1

theorem measurable_signedDensity {μ ν : Measure ℝ} (h : μ ⟂ₘ ν) :
    Measurable (signedDensity h) := by
  classical
  unfold signedDensity
  exact Measurable.ite h.measurableSet_nullSet measurable_const measurable_const

theorem norm_signedDensity {μ ν : Measure ℝ} (h : μ ⟂ₘ ν) (x : ℝ) :
    ‖signedDensity h x‖ = 1 := by
  by_cases hx : x ∈ h.nullSet <;> simp [signedDensity, hx]

theorem signedDensity_mul_self {μ ν : Measure ℝ} (h : μ ⟂ₘ ν) (x : ℝ) :
    signedDensity h x * signedDensity h x = 1 := by
  by_cases hx : x ∈ h.nullSet <;> simp [signedDensity, hx]

theorem signedDensity_eq_one_ae {μ ν : Measure ℝ} (h : μ ⟂ₘ ν) :
    signedDensity h =ᶠ[ae μ] fun _ => 1 := by
  have hn : ∀ᵐ x ∂μ, x ∉ h.nullSet := by
    rw [ae_iff]
    simpa only [not_not] using h.measure_nullSet
  filter_upwards [hn] with x hx
  simp [signedDensity, hx]

theorem signedDensity_eq_neg_one_ae {μ ν : Measure ℝ} (h : μ ⟂ₘ ν) :
    signedDensity h =ᶠ[ae ν] fun _ => -1 := by
  have hn : ∀ᵐ x ∂ν, x ∈ h.nullSet := by
    rw [ae_iff]
    exact h.measure_compl_nullSet
  filter_upwards [hn] with x hx
  simp [signedDensity, hx]

/-- Multiplication by the sign preserves absolute integrability exactly. -/
theorem integrable_signedDensity_iff {μ ν ρ : Measure ℝ} (h : μ ⟂ₘ ν)
    (g : ℝ → ℝ) :
    Integrable (fun x => signedDensity h x * g x) ρ ↔ Integrable g ρ := by
  have forward (f : ℝ → ℝ) (hf : Integrable f ρ) :
      Integrable (fun x => signedDensity h x * f x) ρ :=
    hf.bdd_mul (measurable_signedDensity h).aestronglyMeasurable
      ⟨1, fun x => (norm_signedDensity h x).le⟩
  refine ⟨fun hg => ?_, forward g⟩
  have hgg := forward _ hg
  simpa only [← mul_assoc, signedDensity_mul_self, one_mul] using hgg

theorem norm_signedDensity_mul {μ ν : Measure ℝ} (h : μ ⟂ₘ ν)
    (g : ℝ → ℝ) (x : ℝ) :
    ‖signedDensity h x * g x‖ = ‖g x‖ := by
  rw [norm_mul, norm_signedDensity, one_mul]

/-- The density representation equals the Jordan positive-minus-negative
integral, including every atom and without subtracting divergent integrals. -/
theorem signed_integral_encoding {μ ν : Measure ℝ} (h : μ ⟂ₘ ν)
    {g : ℝ → ℝ} (hg : Integrable g (μ + ν)) :
    (∫ x, signedDensity h x * g x ∂(μ + ν)) =
      (∫ x, g x ∂μ) - ∫ x, g x ∂ν := by
  have hp := (integrable_add_measure.mp hg).1
  have hn := (integrable_add_measure.mp hg).2
  rw [integral_add_measure ((integrable_signedDensity_iff h g).mpr hp)
    ((integrable_signedDensity_iff h g).mpr hn)]
  have heqp : (∫ x, signedDensity h x * g x ∂μ) = ∫ x, g x ∂μ := by
    apply integral_congr_ae
    filter_upwards [signedDensity_eq_one_ae h] with x hx
    simp [hx]
  have heqn : (∫ x, signedDensity h x * g x ∂ν) = -∫ x, g x ∂ν := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [signedDensity_eq_neg_one_ae h] with x hx
    simp [hx]
  rw [heqp, heqn, sub_eq_add_neg]

/-- The positive reference measure for locally finite Jordan variations is
sigma-finite, as required by the product-integral theorems. -/
theorem sigmaFinite_jordan_reference (μ ν : Measure ℝ)
    [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] : SigmaFinite (μ + ν) := by
  infer_instance

/-- The complete signed Stieltjes input is represented by its unit sign
density against the sum of its positive and negative variations. -/
theorem cauchy_cumulative_jordan_pair {μ ν : Measure ℝ} [SFinite μ] [SFinite ν]
    (h : μ ⟂ₘ ν) {δ : ℝ} (hδ : 0 < δ)
    (hsupp : ∀ᵐ s ∂(μ + ν), 0 ≤ s)
    (hint : Integrable (fun s : ℝ => 1 / (1 + s)) (μ + ν)) :
    (∫ s, 1 / (δ + s) ∂μ) - (∫ s, 1 / (δ + s) ∂ν) =
      ∫ t in Ici 0, (∫ s in Iic t, signedDensity h s ∂(μ + ν)) / (δ + t)^2 := by
  have hi : Integrable (fun s : ℝ => 1 / (δ + s)) (μ + ν) :=
    integrable_cauchy_of_weighted hδ measurable_const hsupp hint
  have hie : Integrable (fun s => signedDensity h s / (1 + s)) (μ + ν) := by
    simpa only [mul_one_div] using (integrable_signedDensity_iff h _).mpr hint
  have he := signed_integral_encoding h hi
  simp only [mul_one_div] at he
  rw [← he]
  exact cauchy_cumulative_of_weighted hδ (measurable_signedDensity h) hsupp hie

end
end LeanVerification.Stieltjes
