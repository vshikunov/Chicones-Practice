import LeanVerification.SpectralWidth
import LeanVerification.SlitPhysicalRepresentation
import LeanVerification.SlitCauchyPower

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.SlitContour.PhysicalCutData

def physicalWidth {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) (v : ℝ) : ℝ :=
  Real.sqrt v * (F (v : ℂ)).re

def periodExtension {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) (z : ℂ) : ℂ :=
  ((Real.pi * d.constant / Real.sqrt 2 : ℝ) : ℂ) +
    (1 / (Real.sqrt 2 : ℂ)) * powerIntegral (volume.restrict (Ioi H))
      (fun t => (d.density t : ℂ)) ((3 : ℝ) / 2) z

theorem support_above_height {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) :
    ∀ᵐ t ∂volume.restrict (Ioi H), H ≤ t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact ht.le

theorem cauchyReal_eq_upper_im {F : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData F H) (v : ℝ) :
    SpectralWidth.cauchyReal (volume.restrict (Ioi H)) d.density v =
      ∫ t in Ioi H, (d.upper t).im / (t - v) := by
  unfold SpectralWidth.cauchyReal
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr (d.height_pos.trans ht)).ne'
  rw [density, mul_div_cancel_left₀ _ hs]

theorem physicalWidth_eq_spectralWidth {F : ℂ → ℂ} {H v : ℝ}
    (d : PhysicalCutData F H) (hv : v < H) :
    d.physicalWidth v = SpectralWidth.width (volume.restrict (Ioi H)) d.density d.constant v := by
  have he := congrArg Complex.re (d.real_width_representation hv)
  simp only [Complex.add_re, Complex.ofReal_re] at he
  rw [physicalWidth, SpectralWidth.width, d.cauchyReal_eq_upper_im, he]

/-- The physical Abel period of the width supplied in the contour
hypotheses equals its spectral integral. All derivative and Fubini
conditions are derived from the actual weighted boundary density. -/
theorem period_representation {F : ℂ → ℂ} {H h : ℝ}
    (d : PhysicalCutData F H) (hh : h ∈ Ioo 0 H) :
    SpectralWidth.angularPeriod d.physicalWidth h = Real.pi * d.constant / Real.sqrt 2 +
      (1 / Real.sqrt 2) * ∫ t in Ioi H, d.density t * (t - h) ^ (-(3 : ℝ) / 2) := by
  rw [SpectralWidth.angularPeriod_congrOn hh
    (show EqOn d.physicalWidth (SpectralWidth.width (volume.restrict (Ioi H))
      d.density d.constant) (Ioo 0 H) from fun v hv => d.physicalWidth_eq_spectralWidth hv.2)]
  exact SpectralWidth.angularPeriod_eq_ae d.height_pos hh d.aestronglyMeasurable_density
    d.support_above_height d.integrable_weighted_density

theorem complex_density_measurable {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) :
    AEStronglyMeasurable (fun t => (d.density t : ℂ)) (volume.restrict (Ioi H)) :=
  (Complex.continuous_ofReal.measurable.comp_aemeasurable
    d.aestronglyMeasurable_density.aemeasurable).aestronglyMeasurable

theorem complex_density_mass {F : ℂ → ℂ} {H : ℝ} (d : PhysicalCutData F H) :
    Integrable (fun t => ‖(d.density t : ℂ)‖ * t ^ (-((3 : ℝ) / 2)))
      (volume.restrict (Ioi H)) := by
  apply d.integrable_weighted_density.norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (d.height_pos.trans ht).le _)]
  simp only [Complex.norm_real, show -(3 : ℝ) / 2 = -(3 / 2) by ring]

theorem analyticOnNhd_periodExtension {F : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData F H) : AnalyticOnNhd ℂ d.periodExtension (domain H) := by
  intro z hz
  exact analyticAt_const.add (analyticAt_const.mul
    (analyticOnNhd_powerIntegral d.height_pos (by norm_num : 0 < (3 : ℝ) / 2)
      d.complex_density_measurable d.support_above_height d.complex_density_mass z hz))

theorem periodExtension_ofReal {F : ℂ → ℂ} {H h : ℝ}
    (d : PhysicalCutData F H) (hh : h ∈ Ioo 0 H) :
    d.periodExtension (h : ℂ) = (SpectralWidth.angularPeriod d.physicalWidth h : ℂ) := by
  rw [d.period_representation hh, periodExtension,
    powerIntegral_ofReal hh.2 d.support_above_height]
  simp only [← Complex.ofReal_mul, integral_complex_ofReal,
    show -((3 : ℝ) / 2) = -(3 : ℝ) / 2 by ring]
  push_cast
  rfl

/-- Every derivative of the physical holomorphic period is the raised
spectral kernel, with the actual positive rising-factor coefficient. -/
theorem iteratedDeriv_periodExtension {F : ℂ → ℂ} {H : ℝ}
    (d : PhysicalCutData F H) {k : ℕ} (hk : 0 < k) {z : ℂ} (hz : z ∈ domain H) :
    iteratedDeriv k d.periodExtension z =
      ((Cauchy.risingFactor ((3 : ℝ) / 2) k : ℝ) : ℂ) / (Real.sqrt 2 : ℂ) *
        powerIntegral (volume.restrict (Ioi H)) (fun t => (d.density t : ℂ))
          ((3 : ℝ) / 2 + k) z := by
  have ha := analyticOnNhd_powerIntegral d.height_pos (by norm_num : 0 < (3 : ℝ) / 2)
    d.complex_density_measurable d.support_above_height d.complex_density_mass z hz
  unfold periodExtension
  rw [iteratedDeriv_const_add hk, iteratedDeriv_const_mul ha.contDiffAt,
    iteratedDeriv_powerIntegral d.height_pos (by norm_num : 0 < (3 : ℝ) / 2)
      d.complex_density_measurable d.support_above_height d.complex_density_mass k z hz]
  ring

end LeanVerification.SlitContour.PhysicalCutData
