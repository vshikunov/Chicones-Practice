import LeanVerification.PhysicalCauchyPeriod
import LeanVerification.SpectralAtoms

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace LeanVerification.CompleteSpectral

def reference {N : ℕ} (H : ℝ) (t : Fin N → ℝ) : Measure ℝ :=
  SpectralAtoms.reference (volume.restrict (Ioi H)) t

def density {F : ℂ → ℂ} {H : ℝ} (d : SlitContour.PhysicalCutData F H)
    {N : ℕ} (t A : Fin N → ℝ) : ℝ → ℝ :=
  SpectralAtoms.density d.density t (fun j => SpectralAtoms.coefficient (A j) (t j))

def normalizedWidth (F : ℂ → ℂ) {N : ℕ} (t A : Fin N → ℝ) (z : ℂ) : ℂ :=
  F z + ∑ j, (A j : ℂ) / ((t j : ℂ) - z)

def width (F : ℂ → ℂ) {N : ℕ} (t A : Fin N → ℝ) (v : ℝ) : ℝ :=
  Real.sqrt v * (normalizedWidth F t A (v : ℂ)).re

theorem support_reference {H : ℝ} {N : ℕ} {t : Fin N → ℝ}
    (ht : ∀ j, H ≤ t j) : ∀ᵐ x ∂reference H t, H ≤ x := by
  classical
  have hs : ∀ s : Finset (Fin N), ∀ᵐ x ∂∑ j ∈ s, Measure.dirac (t j), H ≤ x := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, ae_add_measure_iff]
      exact ⟨by simpa only [ae_dirac_eq, Filter.eventually_pure] using ht j, ih⟩
  rw [reference, SpectralAtoms.reference, ae_add_measure_iff]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hx.le
  · exact hs Finset.univ

theorem integrable_weighted_density {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} (t A : Fin N → ℝ) :
    Integrable (fun x => density d t A x * x ^ (-(3 : ℝ) / 2)) (reference H t) := by
  exact SpectralAtoms.integrable_completed (volume.restrict (Ioi H)) d.density t
    (fun j => SpectralAtoms.coefficient (A j) (t j))
    (fun x => x ^ (-(3 : ℝ) / 2)) d.integrable_weighted_density

theorem aestronglyMeasurable_density {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} (t A : Fin N → ℝ)
    (ht : ∀ j, H ≤ t j) : AEStronglyMeasurable (density d t A) (reference H t) := by
  have hm : Measurable (fun x : ℝ => x ^ ((3 : ℝ) / 2)) := by fun_prop
  apply ((integrable_weighted_density d t A).aestronglyMeasurable.mul
    hm.aestronglyMeasurable).congr
  filter_upwards [support_reference ht] with x hx
  change density d t A x * x ^ (-(3 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) = density d t A x
  rw [mul_assoc, ← Real.rpow_add (d.height_pos.trans_le hx)]
  norm_num

/-- The total variation mass is computed from the actual residual bank
density and every signed pole coefficient. -/
theorem weighted_mass {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ) :
    (∫ x, ‖density d t A x * x ^ (-(3 : ℝ) / 2)‖ ∂reference H t) =
      (∫ x in Ioi H, ‖d.density x * x ^ (-(3 : ℝ) / 2)‖) +
        Real.pi * ∑ j, |A j| / t j := by
  exact SpectralAtoms.completed_weighted_mass (volume.restrict (Ioi H)) d.density hinj
    (fun j => d.height_pos.trans_le (ht j)) A d.integrable_weighted_density

theorem integrable_continuous_width_kernel {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {z : ℂ} (hz : z ∈ SlitContour.domain H) :
    Integrable (fun x => d.density x •
      (1 / ((Real.pi : ℂ) * (Real.sqrt x : ℂ) * ((x : ℂ) - z))))
      (volume.restrict (Ioi H)) := by
  have hm : AEStronglyMeasurable (fun x => ((d.upper x).im : ℂ))
      (volume.restrict (Ioi H)) :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable
      d.aestronglyMeasurable_upper_im.aemeasurable).aestronglyMeasurable
  have hi := (SlitContour.integrable_cauchyIntegral d.height_pos hz hm
    d.support_above_height d.integrable_upper_im_absolute_mass).const_mul (1 / (Real.pi : ℂ))
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hs : (Real.sqrt x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (d.height_pos.trans hx)).ne'
  simp only [SlitContour.PhysicalCutData.density, Complex.ofReal_mul, Complex.real_smul]
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  by_cases hden : (x : ℂ) - z = 0
  · simp [hden]
  · field_simp [hs, hp, hden]
    <;> ring

/-- Adding back the actual principal parts reconstructs one complete
Cauchy input, including the atoms omitted by the open-bank imaginary part. -/
theorem complex_width_representation {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    {z : ℂ} (hz : z ∈ SlitContour.domain H) :
    normalizedWidth F t A z = (d.constant : ℂ) + (1 / (Real.pi : ℂ)) *
      ∫ x, (density d t A x : ℂ) /
        ((Real.sqrt x : ℂ) * ((x : ℂ) - z)) ∂reference H t := by
  have he := SpectralAtoms.integral_completed (volume.restrict (Ioi H)) d.density hinj
    (fun j => SpectralAtoms.coefficient (A j) (t j))
    (fun x => 1 / ((Real.pi : ℂ) * (Real.sqrt x : ℂ) * ((x : ℂ) - z)))
    (integrable_continuous_width_kernel d hz)
  have hscalar : ∀ (u : ℝ → ℝ) (μ : Measure ℝ),
      (∫ x, u x • (1 / ((Real.pi : ℂ) * (Real.sqrt x : ℂ) * ((x : ℂ) - z))) ∂μ) =
      (1 / (Real.pi : ℂ)) * ∫ x, (u x : ℂ) /
        ((Real.sqrt x : ℂ) * ((x : ℂ) - z)) ∂μ := by
    intro u μ
    rw [← integral_const_mul]
    congr 1
    funext x
    simp only [Complex.real_smul, div_eq_mul_inv, mul_inv_rev]
    ring
  have hatom : (∑ j, SpectralAtoms.coefficient (A j) (t j) •
      (1 / ((Real.pi : ℂ) * (Real.sqrt (t j) : ℂ) * ((t j : ℂ) - z)))) =
      ∑ j, (A j : ℂ) / ((t j : ℂ) - z) := by
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Complex.real_smul, mul_one_div] using
      SpectralAtoms.coefficient_width_kernel (A := A j) (z := z)
        (d.height_pos.trans_le (ht j))
  rw [hscalar, hscalar, hatom] at he
  have hw := d.complex_width_density_representation hz
  change F z + ∑ j, (A j : ℂ) / ((t j : ℂ) - z) = _
  change (1 / (Real.pi : ℂ)) *
    (∫ x, (density d t A x : ℂ) / ((Real.sqrt x : ℂ) * ((x : ℂ) - z))
      ∂reference H t) = _ at he
  linear_combination hw - he

theorem width_eq_spectralWidth {F : ℂ → ℂ} {H v : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    (hv : v < H) :
    width F t A v = SpectralWidth.width (reference H t) (density d t A) d.constant v := by
  have hi : (∫ x, (density d t A x : ℂ) /
      ((Real.sqrt x : ℂ) * ((x : ℂ) - (v : ℂ))) ∂reference H t) =
      (SpectralWidth.cauchyReal (reference H t) (density d t A) v : ℂ) := by
    unfold SpectralWidth.cauchyReal
    simp only [div_mul_eq_div_div, ← Complex.ofReal_sub, ← Complex.ofReal_div]
    exact integral_complex_ofReal
  have he := complex_width_representation d hinj ht A
    (show (v : ℂ) ∈ SlitContour.domain H from Or.inl hv)
  rw [hi] at he
  have hr := congrArg Complex.re he
  simp only [← Complex.ofReal_div, ← Complex.ofReal_mul, Complex.add_re,
    Complex.ofReal_re, ← Complex.ofReal_one] at hr
  rw [width, SpectralWidth.width, hr]

/-- The period of the full physical width includes the actual finite
signed atoms. All Abel integrability hypotheses follow from the residual
contour conditions and finite pole data. -/
theorem period_representation {F : ℂ → ℂ} {H h : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    (hh : h ∈ Ioo 0 H) :
    SpectralWidth.angularPeriod (width F t A) h = Real.pi * d.constant / Real.sqrt 2 +
      (1 / Real.sqrt 2) * ∫ x, density d t A x * (x - h) ^ (-(3 : ℝ) / 2)
        ∂reference H t := by
  letI : SFinite (reference H t) := by
    dsimp only [reference, SpectralAtoms.reference]
    infer_instance
  rw [SpectralWidth.angularPeriod_congrOn hh
    (show EqOn (width F t A)
      (SpectralWidth.width (reference H t) (density d t A) d.constant) (Ioo 0 H) from
        fun v hv => width_eq_spectralWidth d hinj ht A hv.2)]
  exact SpectralWidth.angularPeriod_eq_ae d.height_pos hh
    (aestronglyMeasurable_density d t A ht) (support_reference ht)
    (integrable_weighted_density d t A)

theorem integrable_residual_period {F : ℂ → ℂ} {H h : ℝ}
    (d : SlitContour.PhysicalCutData F H) (hh : h ∈ Ioo 0 H) :
    Integrable (fun x => d.density x * (x - h) ^ (-(3 : ℝ) / 2))
      (volume.restrict (Ioi H)) := by
  have hm : Measurable (fun x : ℝ => (x - h) ^ (-(3 : ℝ) / 2)) := by fun_prop
  apply (d.integrable_weighted_density.norm.const_mul
    (((H - h) / H) ^ (-(3 : ℝ) / 2))).mono'
      (d.aestronglyMeasurable_density.mul hm.aestronglyMeasurable)
  filter_upwards [d.support_above_height] with x hx
  exact AbelCauchy.weighted_kernel_bound d.height_pos hh.1 hh.2 hx

/-- The discrete period terms have precisely the same coefficients as
the reconstructed Cauchy width. -/
theorem period_expanded {F : ℂ → ℂ} {H h : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    (hh : h ∈ Ioo 0 H) :
    SpectralWidth.angularPeriod (width F t A) h =
      SpectralWidth.angularPeriod d.physicalWidth h +
        (1 / Real.sqrt 2) * ∑ j,
          Real.pi * A j * Real.sqrt (t j) * (t j - h) ^ (-(3 : ℝ) / 2) := by
  have he := SpectralAtoms.integral_completed (volume.restrict (Ioi H)) d.density hinj
    (fun j => SpectralAtoms.coefficient (A j) (t j))
    (fun x => (x - h) ^ (-(3 : ℝ) / 2)) (integrable_residual_period d hh)
  simp only [smul_eq_mul, SpectralAtoms.coefficient] at he
  rw [period_representation d hinj ht A hh, d.period_representation hh]
  change (∫ x, density d t A x * (x - h) ^ (-(3 : ℝ) / 2) ∂reference H t) = _ at he
  rw [he]
  ring

theorem integrable_residual_moment {F : ℂ → ℂ} {H r : ℝ}
    (d : SlitContour.PhysicalCutData F H) (hr : 0 ≤ r) :
    Integrable (fun x => d.density x * x ^ (-r - (3 : ℝ) / 2))
      (volume.restrict (Ioi H)) := by
  let g := d.aestronglyMeasurable_density.aemeasurable.mk d.density
  have hg : Measurable g := d.aestronglyMeasurable_density.aemeasurable.measurable_mk
  have he : d.density =ᵐ[volume.restrict (Ioi H)] g :=
    d.aestronglyMeasurable_density.aemeasurable.ae_eq_mk
  have hi : Integrable (fun x => g x * x ^ (-(3 : ℝ) / 2))
      (volume.restrict (Ioi H)) := by
    apply d.integrable_weighted_density.congr
    filter_upwards [he] with x hx
    rw [hx]
  apply (Stieltjes.integrable_weightedMoment d.height_pos hr hg d.support_above_height hi).congr
  filter_upwards [he] with x hx
  rw [hx]

/-- Every normalized moment records the ordinary signed pole
coefficients with exactly the exponent appearing in the manuscript. -/
theorem normalizedMoment_expanded {F : ℂ → ℂ} {H r : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    (hr : 0 ≤ r) :
    Stieltjes.normalizedMoment (reference H t) (density d t A) r =
      Stieltjes.normalizedMoment (volume.restrict (Ioi H)) d.density r +
        ∑ j, A j * (t j) ^ (-r - 1) := by
  have he := SpectralAtoms.integral_completed (volume.restrict (Ioi H)) d.density hinj
    (fun j => SpectralAtoms.coefficient (A j) (t j))
    (fun x => x ^ (-r - (3 : ℝ) / 2)) (integrable_residual_moment d hr)
  simp only [smul_eq_mul] at he
  unfold Stieltjes.normalizedMoment Stieltjes.weightedMoment
  change (∫ x, density d t A x * x ^ (-r - (3 : ℝ) / 2) ∂reference H t) = _ at he
  rw [he, add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact SpectralAtoms.coefficient_moment (d.height_pos.trans_le (ht j))

end LeanVerification.CompleteSpectral
