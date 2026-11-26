import LeanVerification.CompleteSpectralRepresentation
import LeanVerification.SlitPrincipalParts

noncomputable section

open MeasureTheory Set

namespace LeanVerification.CompleteSpectral

theorem normalizedWidth_eq_add_polePart (F : ℂ → ℂ) {N : ℕ}
    (t A : Fin N → ℝ) :
    normalizedWidth F t A = fun z => F z + SlitContour.polePart t A z := rfl

theorem differentiableOn_normalizedWidth {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} (t A : Fin N → ℝ)
    (ht : ∀ j, H ≤ t j) :
    DifferentiableOn ℂ (normalizedWidth F t A) (SlitContour.domain H) :=
  d.holomorphic.add (SlitContour.differentiableOn_polePart t A ht)

theorem complex_density_measurable {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} (t A : Fin N → ℝ)
    (ht : ∀ j, H ≤ t j) :
    AEStronglyMeasurable (fun x => (density d t A x : ℂ)) (reference H t) :=
  (Complex.continuous_ofReal.measurable.comp_aemeasurable
    (aestronglyMeasurable_density d t A ht).aemeasurable).aestronglyMeasurable

theorem complex_density_mass {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} (t A : Fin N → ℝ)
    (ht : ∀ j, H ≤ t j) :
    Integrable (fun x => ‖(density d t A x : ℂ)‖ * x ^ (-((3 : ℝ) / 2)))
      (reference H t) := by
  apply (integrable_weighted_density d t A).norm.congr
  filter_upwards [support_reference ht] with x hx
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (d.height_pos.trans_le hx).le _)]
  simp only [Complex.norm_real, show -(3 : ℝ) / 2 = -(3 / 2) by ring]

def periodExtension {F : ℂ → ℂ} {H : ℝ} (d : SlitContour.PhysicalCutData F H)
    {N : ℕ} (t A : Fin N → ℝ) (z : ℂ) : ℂ :=
  ((Real.pi * d.constant / Real.sqrt 2 : ℝ) : ℂ) + (1 / (Real.sqrt 2 : ℂ)) *
    SlitContour.powerIntegral (reference H t) (fun x => (density d t A x : ℂ))
      ((3 : ℝ) / 2) z

/-- The full continuous-plus-atomic period is holomorphic on the whole
slit domain. The original residual hypotheses supply its weighted mass. -/
theorem analyticOnNhd_periodExtension {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} (t A : Fin N → ℝ)
    (ht : ∀ j, H ≤ t j) :
    AnalyticOnNhd ℂ (periodExtension d t A) (SlitContour.domain H) := by
  intro z hz
  exact analyticAt_const.add (analyticAt_const.mul
    (SlitContour.analyticOnNhd_powerIntegral d.height_pos (by norm_num : 0 < (3 : ℝ) / 2)
      (complex_density_measurable d t A ht) (support_reference ht)
      (complex_density_mass d t A ht) z hz))

theorem periodExtension_ofReal {F : ℂ → ℂ} {H h : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    (hh : h ∈ Ioo 0 H) :
    periodExtension d t A (h : ℂ) = (SpectralWidth.angularPeriod (width F t A) h : ℂ) := by
  rw [period_representation d hinj ht A hh, periodExtension,
    SlitContour.powerIntegral_ofReal hh.2 (support_reference ht)]
  simp only [← Complex.ofReal_mul, integral_complex_ofReal,
    show -((3 : ℝ) / 2) = -(3 : ℝ) / 2 by ring]
  push_cast
  rfl

/-- Every complete period derivative keeps all signed atoms and has the
positive rising-factor coefficient. No extra moments are assumed. -/
theorem iteratedDeriv_periodExtension {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} (t A : Fin N → ℝ)
    (ht : ∀ j, H ≤ t j) {k : ℕ} (hk : 0 < k) {z : ℂ}
    (hz : z ∈ SlitContour.domain H) :
    iteratedDeriv k (periodExtension d t A) z =
      ((Cauchy.risingFactor ((3 : ℝ) / 2) k : ℝ) : ℂ) / (Real.sqrt 2 : ℂ) *
        SlitContour.powerIntegral (reference H t) (fun x => (density d t A x : ℂ))
          ((3 : ℝ) / 2 + k) z := by
  have ha := SlitContour.analyticOnNhd_powerIntegral d.height_pos
    (by norm_num : 0 < (3 : ℝ) / 2) (complex_density_measurable d t A ht)
    (support_reference ht) (complex_density_mass d t A ht) z hz
  unfold periodExtension
  rw [iteratedDeriv_const_add hk, iteratedDeriv_const_mul ha.contDiffAt,
    SlitContour.iteratedDeriv_powerIntegral d.height_pos (by norm_num : 0 < (3 : ℝ) / 2)
      (complex_density_measurable d t A ht) (support_reference ht)
      (complex_density_mass d t A ht) k z hz]
  ring

end LeanVerification.CompleteSpectral
