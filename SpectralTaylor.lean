import LeanVerification.CompleteSpectralPeriod
import LeanVerification.MomentSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.SpectralTaylor

theorem coefficient_identity (f : ℝ → ℝ) {x : ℝ} (hx : 0 < x) (z : ℂ) (n : ℕ) :
    ((f x * x ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * (z / (x : ℂ)) ^ n =
      ((f x * x ^ (-(n : ℝ) - (3 : ℝ) / 2) : ℝ) : ℂ) * z ^ n := by
  rw [show -(n : ℝ) - (3 : ℝ) / 2 = -(3 : ℝ) / 2 + -(n : ℝ) by ring,
    Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_natCast, div_pow]
  push_cast
  ring

theorem geometric_kernel_identity (f : ℝ → ℝ) {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((f x * x ^ (-(3 : ℝ) / 2) : ℝ) : ℂ) * (1 - z / (x : ℂ))⁻¹ =
      (f x : ℂ) / ((Real.sqrt x : ℂ) * ((x : ℂ) - z)) := by
  rw [show -(3 : ℝ) / 2 = -(3 / 2) by ring, Real.rpow_neg hx.le,
    AbelCauchy.rpow_three_halves hx]
  push_cast
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hsc : (Real.sqrt x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  by_cases hz : (x : ℂ) - z = 0
  · have he : z = (x : ℂ) := (sub_eq_zero.mp hz).symm
    simp [he, hxc]
  · have hd : (1 : ℂ) - z / (x : ℂ) ≠ 0 := by
      intro he
      apply hz
      have he' := sub_eq_zero.mp he
      have hh := (eq_div_iff hxc).mp he'
      simpa only [one_mul] using sub_eq_zero.mpr hh
    field_simp [hxc, hsc, hz, hd]
    <;> ring

/-- The actual geometric expansion is integrated using the original
weighted mass. The majorant is a geometric sequence times that mass;
no higher moment or interchange assumption occurs. -/
theorem hasSum_cauchy_moments {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (hsupp : ∀ᵐ x ∂μ, H ≤ x)
    (hint : Integrable (fun x => f x * x ^ (-(3 : ℝ) / 2)) μ)
    {z : ℂ} (hz : ‖z‖ < H) :
    HasSum (fun n : ℕ => (Stieltjes.normalizedMoment μ f (n : ℝ) : ℂ) * z ^ n)
      ((1 / (Real.pi : ℂ)) *
        ∫ x, (f x : ℂ) / ((Real.sqrt x : ℂ) * ((x : ℂ) - z)) ∂μ) := by
  let G : ℝ → ℝ := fun x => f x * x ^ (-(3 : ℝ) / 2)
  let q : ℝ := ‖z‖ / H
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hH.le
  have hq1 : q < 1 := (div_lt_one hH).mpr hz
  have hqsum : Summable (fun n : ℕ => q ^ n) := summable_geometric_of_lt_one hq0 hq1
  have hG : AEStronglyMeasurable (fun x => (G x : ℂ)) μ :=
    (Complex.continuous_ofReal.measurable.comp_aemeasurable
      hint.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hm : ∀ n : ℕ, AEStronglyMeasurable
      (fun x => (G x : ℂ) * (z / (x : ℂ)) ^ n) μ := by
    intro n
    have hh : Measurable (fun x : ℝ => (z / (x : ℂ)) ^ n) := by fun_prop
    exact hG.mul hh.aestronglyMeasurable
  have hb : ∀ n : ℕ, ∀ᵐ x ∂μ,
      ‖(G x : ℂ) * (z / (x : ℂ)) ^ n‖ ≤ ‖G x‖ * q ^ n := by
    intro n
    filter_upwards [hsupp] with x hx
    have hxp := hH.trans_le hx
    simp only [norm_mul, norm_pow, norm_div, Complex.norm_real,
      Real.norm_of_nonneg hxp.le]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hxp.le)
    exact div_le_div_of_nonneg_left (norm_nonneg _) hH hx
  have hbi : Integrable (fun x => ∑' n : ℕ, ‖G x‖ * q ^ n) μ := by
    simp only [tsum_mul_left]
    exact hint.norm.mul_const _
  have hlim : ∀ᵐ x ∂μ,
      HasSum (fun n : ℕ => (G x : ℂ) * (z / (x : ℂ)) ^ n)
        ((f x : ℂ) / ((Real.sqrt x : ℂ) * ((x : ℂ) - z))) := by
    filter_upwards [hsupp] with x hx
    have hxp := hH.trans_le hx
    have hratio : ‖z / (x : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hxp.le]
      exact (div_lt_one hxp).mpr (hz.trans_le hx)
    convert (hasSum_geometric_of_norm_lt_one hratio).mul_left (G x : ℂ) using 1
    exact (geometric_kernel_identity f hxp z).symm
  have hi := hasSum_integral_of_dominated_convergence (fun n x => ‖G x‖ * q ^ n)
    hm hb (Eventually.of_forall fun x => hqsum.mul_left ‖G x‖) hbi hlim
  have hc : ∀ n : ℕ, (∫ x, (G x : ℂ) * (z / (x : ℂ)) ^ n ∂μ) =
      ((Stieltjes.weightedMoment μ f (n : ℝ) : ℝ) : ℂ) * z ^ n := by
    intro n
    rw [Stieltjes.weightedMoment, ← integral_complex_ofReal, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [hsupp] with x hx
    exact coefficient_identity f (hH.trans_le hx) z n
  have hs := hi.mul_left (1 / (Real.pi : ℂ))
  convert hs using 1
  ext n
  rw [hc, Stieltjes.normalizedMoment]
  push_cast
  ring

theorem residual_width_hasSum {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {z : ℂ} (hz : ‖z‖ < H) :
    HasSum (fun n : ℕ =>
      (Stieltjes.normalizedMoment (volume.restrict (Ioi H)) d.density (n : ℝ) : ℂ) * z ^ n)
      (F z - (d.constant : ℂ)) := by
  have hd : z ∈ SlitContour.domain H := Or.inl (z.re_le_norm.trans_lt hz)
  have hh := hasSum_cauchy_moments d.height_pos d.support_above_height
    d.integrable_weighted_density hz
  convert hh using 1
  have he := d.complex_width_density_representation hd
  linear_combination he

theorem complete_width_hasSum {F : ℂ → ℂ} {H : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    {z : ℂ} (hz : ‖z‖ < H) :
    HasSum (fun n : ℕ =>
      (Stieltjes.normalizedMoment (CompleteSpectral.reference H t)
        (CompleteSpectral.density d t A) (n : ℝ) : ℂ) * z ^ n)
      (CompleteSpectral.normalizedWidth F t A z - (d.constant : ℂ)) := by
  have hd : z ∈ SlitContour.domain H := Or.inl (z.re_le_norm.trans_lt hz)
  have hh := hasSum_cauchy_moments d.height_pos (CompleteSpectral.support_reference ht)
    (CompleteSpectral.integrable_weighted_density d t A) hz
  convert hh using 1
  have he := CompleteSpectral.complex_width_representation d hinj ht A hd
  linear_combination he

theorem moment_converges {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (hsupp : ∀ᵐ x ∂μ, H ≤ x)
    (hint : Integrable (fun x => f x * x ^ (-(3 : ℝ) / 2)) μ) :
    ScalarSeries.ConvergesOn (fun n : ℕ => Stieltjes.normalizedMoment μ f (n : ℝ)) H := by
  intro x hx
  have he := Complex.reCLM.hasSum (hasSum_cauchy_moments hH hsupp hint
    (show ‖(x : ℂ)‖ < H by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx))
  have hm : (fun n : ℕ => Complex.reCLM
      ((Stieltjes.normalizedMoment μ f (n : ℝ) : ℂ) * (x : ℂ) ^ n)) =
      (fun n : ℕ => Stieltjes.normalizedMoment μ f (n : ℝ) * x ^ n) := by
    funext n
    simp only [Complex.reCLM_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hm] at he
  exact he.summable

theorem residual_normalizedWidth_eq_series {F : ℂ → ℂ} {H v : ℝ}
    (d : SlitContour.PhysicalCutData F H) (hv : |v| < H) :
    (F (v : ℂ)).re = d.constant + ScalarSeries.sum
      (fun n : ℕ => Stieltjes.normalizedMoment (volume.restrict (Ioi H)) d.density (n : ℝ)) v := by
  have he := Complex.reCLM.hasSum (residual_width_hasSum d
    (show ‖(v : ℂ)‖ < H by simpa only [Complex.norm_real, Real.norm_eq_abs] using hv))
  simp only [Complex.reCLM_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.sub_re] at he
  have hh := he.tsum_eq
  change ScalarSeries.sum _ v = _ at hh
  linarith

theorem complete_normalizedWidth_eq_series {F : ℂ → ℂ} {H v : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    (hv : |v| < H) :
    (CompleteSpectral.normalizedWidth F t A (v : ℂ)).re = d.constant + ScalarSeries.sum
      (fun n : ℕ => Stieltjes.normalizedMoment (CompleteSpectral.reference H t)
        (CompleteSpectral.density d t A) (n : ℝ)) v := by
  have he := Complex.reCLM.hasSum (complete_width_hasSum d hinj ht A
    (show ‖(v : ℂ)‖ < H by simpa only [Complex.norm_real, Real.norm_eq_abs] using hv))
  simp only [Complex.reCLM_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.sub_re] at he
  have hh := he.tsum_eq
  change ScalarSeries.sum _ v = _ at hh
  linarith

end LeanVerification.SpectralTaylor
