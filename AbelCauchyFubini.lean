import LeanVerification.AbelCauchyKernel
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.AbelCauchy

def layer (h : ℝ) (f : ℝ → ℝ) (t v : ℝ) : ℝ := f t / Real.sqrt t * kernel h t v

theorem integralOn_kernel {h t : ℝ} (hh : 0 < h) (ht : h < t) :
    (∫ v in Ioo (0 : ℝ) h, kernel h t v) =
      Real.pi * Real.sqrt t / (2 * (t - h) ^ ((3 : ℝ) / 2)) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hh.le,
    integral_kernel hh ht, rpow_three_halves (sub_pos.mpr ht)]
  ring

theorem integrableOn_layer {h t : ℝ} (hh : 0 < h) (ht : h < t) (f : ℝ → ℝ) :
    IntegrableOn (layer h f t) (Ioo 0 h) :=
  ((intervalIntegrable_iff_integrableOn_Ioo_of_le hh.le).mp
    (intervalIntegrable_kernel hh ht)).const_mul (f t / Real.sqrt t)

theorem integral_layer {h t : ℝ} (hh : 0 < h) (ht : h < t) (f : ℝ → ℝ) :
    (∫ v in Ioo (0 : ℝ) h, layer h f t v) =
      (Real.pi / 2) * (f t * (t - h) ^ (-(3 : ℝ) / 2)) := by
  have htp : 0 < t := hh.trans ht
  have hth : 0 < t - h := sub_pos.mpr ht
  unfold layer
  rw [integral_const_mul, integralOn_kernel hh ht]
  have he : (t - h) ^ (-(3 : ℝ) / 2) = ((t - h) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [show -(3 : ℝ) / 2 = -(3 / 2) by ring, Real.rpow_neg hth.le]
  rw [he]
  field_simp [(Real.sqrt_pos.mpr htp).ne', (Real.rpow_pos_of_pos hth ((3 : ℝ) / 2)).ne']
  <;> ring

theorem integral_norm_layer {h t : ℝ} (hh : 0 < h) (ht : h < t) (f : ℝ → ℝ) :
    (∫ v in Ioo (0 : ℝ) h, ‖layer h f t v‖) =
      (Real.pi / 2) * ‖f t * (t - h) ^ (-(3 : ℝ) / 2)‖ := by
  have htp : 0 < t := hh.trans ht
  have he : (∫ v in Ioo (0 : ℝ) h, ‖layer h f t v‖) =
      ∫ v in Ioo (0 : ℝ) h, layer h (fun t => ‖f t‖) t v := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
    simp only [layer, norm_mul, norm_div,
      Real.norm_of_nonneg (Real.sqrt_nonneg t),
      Real.norm_of_nonneg (kernel_pos hh ht hv).le]
  rw [he, integral_layer hh ht]
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (sub_pos.mpr ht).le _)]

theorem weighted_kernel_bound {H h t A : ℝ} (hH : 0 < H) (hh : 0 < h)
    (hhH : h < H) (ht : H ≤ t) :
    ‖A * (t - h) ^ (-(3 : ℝ) / 2)‖ ≤
      ((H - h) / H) ^ (-(3 : ℝ) / 2) * ‖A * t ^ (-(3 : ℝ) / 2)‖ := by
  let c := (H - h) / H
  have hc : 0 < c := div_pos (sub_pos.mpr hhH) hH
  have htp : 0 < t := hH.trans_le ht
  have hth : 0 < t - h := by linarith
  have hlow : c * t ≤ t - h := by
    dsimp [c]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hH).mpr
    nlinarith [mul_nonneg hh.le (sub_nonneg.mpr ht)]
  have hk := Real.rpow_le_rpow_of_nonpos (mul_pos hc htp) hlow
    (by norm_num : -(3 : ℝ) / 2 ≤ 0)
  rw [Real.mul_rpow hc.le htp.le] at hk
  simp only [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hth.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg htp.le _)]
  calc
    _ ≤ ‖A‖ * (c ^ (-(3 : ℝ) / 2) * t ^ (-(3 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hk (norm_nonneg _)
    _ = _ := by ring

theorem integrable_spectral_period {μ : Measure ℝ} {H h : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hh : 0 < h) (hhH : h < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    Integrable (fun t => f t * (t - h) ^ (-(3 : ℝ) / 2)) μ := by
  apply (hint.norm.const_mul (((H - h) / H) ^ (-(3 : ℝ) / 2))).mono'
    (hf.mul ((measurable_id.sub_const h).pow_const _)).aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  exact weighted_kernel_bound hH hh hhH ht

theorem measurable_layer {h : ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => layer h f p.1 p.2) := by
  unfold layer kernel
  fun_prop

/-- The full two-variable absolute-integrability obligation is discharged
from the original physical weighted mass. Signed atoms are allowed. -/
theorem integrable_layer_product {μ : Measure ℝ} [SFinite μ]
    {H h : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hh : 0 < h) (hhH : h < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    Integrable (fun p : ℝ × ℝ => layer h f p.1 p.2)
      (μ.prod (volume.restrict (Ioo 0 h))) := by
  apply (integrable_prod_iff (measurable_layer hf).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hsupp] with t ht
    exact integrableOn_layer hh (hhH.trans_le ht) f
  · apply ((integrable_spectral_period hH hh hhH hf hsupp hint).norm.const_mul
      (Real.pi / 2)).congr
    filter_upwards [hsupp] with t ht
    exact (integral_norm_layer hh (hhH.trans_le ht) f).symm

theorem integral_layer_swap {μ : Measure ℝ} [SFinite μ]
    {H h : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hh : 0 < h) (hhH : h < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    (∫ v in Ioo (0 : ℝ) h, ∫ t, layer h f t v ∂μ) =
      (Real.pi / 2) * ∫ t, f t * (t - h) ^ (-(3 : ℝ) / 2) ∂μ := by
  rw [← integral_integral_swap (integrable_layer_product hH hh hhH hf hsupp hint),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hsupp] with t ht
  exact integral_layer hh (hhH.trans_le ht) f

/-- The signed Fubini identity uses the actual derivative of the physical
width kernel, not an abstract inner-integral hypothesis. -/
theorem integral_width_deriv_swap {μ : Measure ℝ} [SFinite μ]
    {H h : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hh : 0 < h) (hhH : h < H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    (∫ v in Ioo (0 : ℝ) h,
      (∫ t, f t / Real.sqrt t * deriv (fun w => Real.sqrt w / (t - w)) v ∂μ) /
        Real.sqrt (h - v)) =
      (Real.pi / 2) * ∫ t, f t * (t - h) ^ (-(3 : ℝ) / 2) ∂μ := by
  rw [← integral_layer_swap hH hh hhH hf hsupp hint]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with v hv
  rw [← integral_div]
  apply integral_congr_ae
  filter_upwards [hsupp] with t ht
  rw [layer, kernel_eq_width_deriv hv.1 (hv.2.trans (hhH.trans_le ht))]
  ring

end LeanVerification.AbelCauchy
