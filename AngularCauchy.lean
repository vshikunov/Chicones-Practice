import LeanVerification.AbelCauchyFubini
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.AbelCauchy

def angularKernel (h t θ : ℝ) : ℝ :=
  (t + h * Real.sin θ ^ 2) / (t - h * Real.sin θ ^ 2) ^ 2

theorem angular_energy_mem {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    h * Real.sin θ ^ 2 ∈ Icc 0 h := by
  exact ⟨mul_nonneg hh.le (sq_nonneg _), by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.sin_sq_le_one θ) hh.le⟩

theorem continuous_angularKernel {h t : ℝ} (hh : 0 < h) (ht : h < t) :
    Continuous (angularKernel h t) := by
  unfold angularKernel
  apply Continuous.div (by fun_prop) (by fun_prop)
  intro θ
  have hv := angular_energy_mem hh θ
  exact pow_ne_zero 2 (by linarith [hv.2] : t - h * Real.sin θ ^ 2 ≠ 0)

theorem angularKernel_pos {h t : ℝ} (hh : 0 < h) (ht : h < t) (θ : ℝ) :
    0 < angularKernel h t θ := by
  have hv := angular_energy_mem hh θ
  exact div_pos (by linarith [hv.1]) (sq_pos_of_pos (by linarith [hv.2]))

theorem hasDerivAt_primitive_angle {h t θ : ℝ} (hh : 0 < h) (ht : h < t)
    (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    HasDerivAt (fun x => primitive h t (h * Real.sin x ^ 2)) (angularKernel h t θ) θ := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hv : h * Real.sin θ ^ 2 ∈ Ioo 0 h := by
    refine ⟨mul_pos hh (sq_pos_of_pos hs), ?_⟩
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_pos_of_pos hc]
  have hdq : HasDerivAt (fun x => h * Real.sin x ^ 2)
      (2 * h * Real.sin θ * Real.cos θ) θ := by
    convert ((Real.hasDerivAt_sin θ).pow 2).const_mul h using 1 <;> ring
  have hd := (hasDerivAt_primitive hh ht hv).comp θ hdq
  have hsv : Real.sqrt (h * Real.sin θ ^ 2) = Real.sqrt h * Real.sin θ := by
    rw [Real.sqrt_mul hh.le, Real.sqrt_sq hs.le]
  have hsub : h - h * Real.sin θ ^ 2 = h * Real.cos θ ^ 2 := by
    linear_combination -h * Real.sin_sq_add_cos_sq θ
  have hsc : Real.sqrt (h - h * Real.sin θ ^ 2) = Real.sqrt h * Real.cos θ := by
    rw [hsub, Real.sqrt_mul hh.le, Real.sqrt_sq hc.le]
  apply hd.congr_deriv
  unfold kernel angularKernel
  rw [hsv, hsc]
  have hden : t - h * Real.sin θ ^ 2 ≠ 0 := by linarith [hv.2]
  field_simp [hs.ne', hc.ne', (Real.sqrt_pos.mpr hh).ne', hden]
  ring_nf
  rw [Real.sq_sqrt hh.le]
  ring

/-- The actual angular kernel integral is evaluated by composing the
already constructed Abel primitive. Both angular endpoints are included. -/
theorem integral_angularKernel {h t : ℝ} (hh : 0 < h) (ht : h < t) :
    (∫ θ in (0 : ℝ)..Real.pi / 2, angularKernel h t θ) =
      Real.pi * Real.sqrt t / (2 * (t - h) ^ ((3 : ℝ) / 2)) := by
  have hp : 0 ≤ Real.pi / 2 := by positivity
  have hc : ContinuousOn (fun θ => primitive h t (h * Real.sin θ ^ 2))
      (Icc 0 (Real.pi / 2)) :=
    (continuousOn_primitive hh ht).comp (by fun_prop)
      (fun θ _ => angular_energy_mem hh θ)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hp hc
    (fun θ hθ => hasDerivAt_primitive_angle hh ht hθ)
    ((continuous_angularKernel hh ht).intervalIntegrable 0 (Real.pi / 2))
  rw [he]
  simp only [Real.sin_pi_div_two, one_pow, mul_one, Real.sin_zero,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    primitive_zero, sub_zero, primitive_top hh ht]
  rw [rpow_three_halves (sub_pos.mpr ht)]
  ring

def angularLayer (h : ℝ) (f : ℝ → ℝ) (t θ : ℝ) : ℝ :=
  f t / Real.sqrt t * angularKernel h t θ

theorem integral_angularLayer {h t : ℝ} (hh : 0 < h) (ht : h < t) (f : ℝ → ℝ) :
    (∫ θ in Ioc (0 : ℝ) (Real.pi / 2), angularLayer h f t θ) =
      (Real.pi / 2) * (f t * (t - h) ^ (-(3 : ℝ) / 2)) := by
  rw [← intervalIntegral.integral_of_le (by positivity : 0 ≤ Real.pi / 2)]
  unfold angularLayer
  rw [intervalIntegral.integral_const_mul, integral_angularKernel hh ht]
  have htp : 0 < t := hh.trans ht
  have hth : 0 < t - h := sub_pos.mpr ht
  rw [show -(3 : ℝ) / 2 = -(3 / 2) by ring, Real.rpow_neg hth.le]
  field_simp [(Real.sqrt_pos.mpr htp).ne', (Real.rpow_pos_of_pos hth ((3 : ℝ) / 2)).ne']
  <;> ring

theorem integral_norm_angularLayer {h t : ℝ} (hh : 0 < h) (ht : h < t) (f : ℝ → ℝ) :
    (∫ θ in Ioc (0 : ℝ) (Real.pi / 2), ‖angularLayer h f t θ‖) =
      (Real.pi / 2) * ‖f t * (t - h) ^ (-(3 : ℝ) / 2)‖ := by
  have he : (fun θ => ‖angularLayer h f t θ‖) = angularLayer h (fun t => ‖f t‖) t := by
    funext θ
    simp only [angularLayer, norm_mul, norm_div,
      Real.norm_of_nonneg (Real.sqrt_nonneg t),
      Real.norm_of_nonneg (angularKernel_pos hh ht θ).le]
  rw [he, integral_angularLayer hh ht]
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (sub_pos.mpr ht).le _)]

theorem integrable_angularLayer_product {μ : Measure ℝ} [SFinite μ]
    {H h : ℝ} {f : ℝ → ℝ} (hH : 0 < H) (hh : 0 < h) (hhH : h < H)
    (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    Integrable (fun p : ℝ × ℝ => angularLayer h f p.1 p.2)
      (μ.prod (volume.restrict (Ioc 0 (Real.pi / 2)))) := by
  have hm : Measurable (fun p : ℝ × ℝ => angularLayer h f p.1 p.2) := by
    unfold angularLayer angularKernel
    fun_prop
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hsupp] with t ht
    exact ((continuous_const.mul (continuous_angularKernel hh (hhH.trans_le ht))).intervalIntegrable
      0 (Real.pi / 2)).1
  · apply ((integrable_spectral_period hH hh hhH hf hsupp hint).norm.const_mul
      (Real.pi / 2)).congr
    filter_upwards [hsupp] with t ht
    exact (integral_norm_angularLayer hh (hhH.trans_le ht) f).symm

theorem integral_angularLayer_swap {μ : Measure ℝ} [SFinite μ]
    {H h : ℝ} {f : ℝ → ℝ} (hH : 0 < H) (hh : 0 < h) (hhH : h < H)
    (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    (∫ θ in Ioc (0 : ℝ) (Real.pi / 2), ∫ t, angularLayer h f t θ ∂μ) =
      (Real.pi / 2) * ∫ t, f t * (t - h) ^ (-(3 : ℝ) / 2) ∂μ := by
  rw [← integral_integral_swap (integrable_angularLayer_product hH hh hhH hf hsupp hint),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hsupp] with t ht
  exact integral_angularLayer hh (hhH.trans_le ht) f

end LeanVerification.AbelCauchy
