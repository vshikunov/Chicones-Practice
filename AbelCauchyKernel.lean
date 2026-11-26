import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.AbelCauchy

def kernel (h t v : ℝ) : ℝ :=
  (t + v) / (2 * Real.sqrt v * (t - v) ^ 2 * Real.sqrt (h - v))

def angle (h t v : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt ((t - h) * v / (h * (t - v))))

def primitive (h t v : ℝ) : ℝ :=
  (t / ((t - h) * Real.sqrt (t * (t - h)))) * angle h t v -
    Real.sqrt v * Real.sqrt (h - v) / ((t - h) * (t - v))

theorem kernel_pos {h t v : ℝ} (hh : 0 < h) (ht : h < t) (hv : v ∈ Ioo 0 h) :
    0 < kernel h t v := by
  have htv : 0 < t - v := by linarith [hv.2]
  have hhv : 0 < h - v := sub_pos.mpr hv.2
  unfold kernel
  exact div_pos (by linarith [hv.1])
    (mul_pos (mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.mpr hv.1))
      (sq_pos_of_pos htv)) (Real.sqrt_pos.mpr hhv))

theorem hasDerivAt_angle {h t v : ℝ} (hh : 0 < h) (ht : h < t) (hv : v ∈ Ioo 0 h) :
    HasDerivAt (angle h t)
      (Real.sqrt (t * (t - h)) / (2 * (t - v) * Real.sqrt v * Real.sqrt (h - v))) v := by
  let q := (t - h) * v / (h * (t - v))
  let r := Real.sqrt (t * (t - h))
  have htp : 0 < t := hh.trans ht
  have hb : 0 < t - h := sub_pos.mpr ht
  have htv : 0 < t - v := by linarith [hv.2]
  have hhv : 0 < h - v := sub_pos.mpr hv.2
  have hden : 0 < h * (t - v) := mul_pos hh htv
  have hq : 0 < q := div_pos (mul_pos hb hv.1) hden
  have hq1 : q < 1 := by
    apply (div_lt_one hden).mpr
    nlinarith [mul_pos htp hhv]
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  have hr : 0 < r := Real.sqrt_pos.mpr (mul_pos htp hb)
  have hqformula : 1 - q = t * (h - v) / (h * (t - v)) := by
    dsimp [q]
    field_simp
    <;> ring
  have hprod : Real.sqrt q * Real.sqrt (1 - q) =
      r * Real.sqrt v * Real.sqrt (h - v) / (h * (t - v)) := by
    rw [← Real.sqrt_mul hq.le]
    have he : q * (1 - q) =
        (t * (t - h)) * (v * (h - v)) / (h * (t - v)) ^ 2 := by
      rw [hqformula]
      dsimp [q]
      field_simp
      <;> ring
    rw [he, Real.sqrt_div (mul_nonneg (mul_pos htp hb).le (mul_pos hv.1 hhv).le),
      Real.sqrt_sq_eq_abs, abs_of_pos hden,
      Real.sqrt_mul (mul_pos htp hb).le, Real.sqrt_mul hv.1.le]
    dsimp [r]
    ring
  have hdq : HasDerivAt (fun w => (t - h) * w / (h * (t - w)))
      ((t - h) * t / (h * (t - v) ^ 2)) v := by
    have hd := ((hasDerivAt_id v).const_mul (t - h)).div
      (((hasDerivAt_id v).const_sub t).const_mul h) hden.ne'
    convert hd using 1
    simp only [id_eq, mul_one]
    field_simp
    <;> ring
  have hsq0 : Real.sqrt q ≠ -1 := by nlinarith [Real.sqrt_nonneg q]
  have hsq1 : Real.sqrt q ≠ 1 := by
    intro he
    have hs := Real.sq_sqrt hq.le
    rw [he] at hs
    nlinarith
  have hd := (Real.hasDerivAt_arcsin hsq0 hsq1).comp v (hdq.sqrt hq.ne')
  convert hd using 1
  change r / (2 * (t - v) * Real.sqrt v * Real.sqrt (h - v)) =
      (1 / Real.sqrt (1 - (Real.sqrt q) ^ 2)) *
        (((t - h) * t / (h * (t - v) ^ 2)) / (2 * Real.sqrt q))
  rw [Real.sq_sqrt hq.le]
  have he : (1 / Real.sqrt (1 - q)) *
        (((t - h) * t / (h * (t - v) ^ 2)) / (2 * Real.sqrt q)) =
        ((t - h) * t) /
          (2 * h * (t - v) ^ 2 * (Real.sqrt q * Real.sqrt (1 - q))) := by
      field_simp
      <;> ring
  rw [he, hprod]
  have hrsq : (t - h) * t = r ^ 2 := by
      dsimp [r]
      rw [Real.sq_sqrt (mul_pos htp hb).le]
      ring
  rw [hrsq]
  field_simp [hh.ne', htv.ne', hr.ne', (Real.sqrt_pos.mpr hv.1).ne',
      (Real.sqrt_pos.mpr hhv).ne']
  <;> ring

theorem hasDerivAt_primitive {h t v : ℝ} (hh : 0 < h) (ht : h < t) (hv : v ∈ Ioo 0 h) :
    HasDerivAt (primitive h t) (kernel h t v) v := by
  have htp : 0 < t := hh.trans ht
  have hb : 0 < t - h := sub_pos.mpr ht
  have htv : 0 < t - v := by linarith [hv.2]
  have hhv : 0 < h - v := sub_pos.mpr hv.2
  have hsr : 0 < Real.sqrt (t * (t - h)) := Real.sqrt_pos.mpr (mul_pos htp hb)
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv.1
  have hsh : 0 < Real.sqrt (h - v) := Real.sqrt_pos.mpr hhv
  let W := Real.sqrt v * Real.sqrt (h - v)
  have hW : 0 < W := mul_pos hsv hsh
  have hWsq : W ^ 2 = v * (h - v) := by
    dsimp [W]
    rw [mul_pow, Real.sq_sqrt hv.1.le, Real.sq_sqrt hhv.le]
  have hd1raw := (hasDerivAt_angle hh ht hv).const_mul
    (t / ((t - h) * Real.sqrt (t * (t - h))))
  have hd1 : HasDerivAt (fun y =>
      (t / ((t - h) * Real.sqrt (t * (t - h)))) * angle h t y)
      (t / (2 * (t - h) * (t - v) * W)) v := by
    convert hd1raw using 1
    dsimp [W]
    field_simp [hb.ne', htv.ne', hsr.ne', hsv.ne', hsh.ne']
    <;> ring
  have hdWraw := ((hasDerivAt_id v).sqrt hv.1.ne').mul
    (((hasDerivAt_id v).const_sub h).sqrt hhv.ne')
  have hdW : HasDerivAt (fun y => Real.sqrt y * Real.sqrt (h - y))
      ((h - 2 * v) / (2 * W)) v := by
    convert hdWraw using 1
    simp only [id_eq]
    dsimp [W]
    rw [show h - 2 * v = (Real.sqrt (h - v)) ^ 2 - (Real.sqrt v) ^ 2 by
      rw [Real.sq_sqrt hhv.le, Real.sq_sqrt hv.1.le]
      ring]
    field_simp [hsv.ne', hsh.ne']
    ring_nf
    have hc : (Real.sqrt (h - v)) ^ 3 = (h - v) * Real.sqrt (h - v) := by
      calc
        _ = (Real.sqrt (h - v)) ^ 2 * Real.sqrt (h - v) := by ring
        _ = _ := by rw [Real.sq_sqrt hhv.le]
    rw [hc]
    ring
  have hd2raw := hdW.div
      (((hasDerivAt_id v).const_sub t).const_mul (t - h)) (mul_pos hb htv).ne'
  have hd2 : HasDerivAt (fun y => Real.sqrt y * Real.sqrt (h - y) /
      ((t - h) * (t - y)))
      ((h - 2 * v) / (2 * (t - h) * (t - v) * W) + W / ((t - h) * (t - v) ^ 2)) v := by
    convert hd2raw using 1
    change (h - 2 * v) / (2 * (t - h) * (t - v) * W) + W / ((t - h) * (t - v) ^ 2) =
      (((h - 2 * v) / (2 * W)) * ((t - h) * (t - v)) - W * ((t - h) * -1)) /
        ((t - h) * (t - v)) ^ 2
    field_simp [hb.ne', htv.ne', hW.ne']
    <;> ring
  convert hd1.sub hd2 using 1
  have hk : kernel h t v = (t + v) / (2 * (t - v) ^ 2 * W) := by
    unfold kernel W
    congr 1
    ring
  rw [hk]
  field_simp [hb.ne', htv.ne', hW.ne']
  ring_nf
  have hWfour : W ^ 4 = (v * (h - v)) ^ 2 := by
    calc
      W ^ 4 = (W ^ 2) ^ 2 := by ring
      _ = _ := by rw [hWsq]
  rw [hWsq, hWfour]
  ring

theorem continuousOn_primitive {h t : ℝ} (hh : 0 < h) (ht : h < t) :
    ContinuousOn (primitive h t) (Icc 0 h) := by
  have hden : ∀ v ∈ Icc (0 : ℝ) h, h * (t - v) ≠ 0 := by
    intro v hv
    exact (mul_pos hh (by linarith [hv.2] : 0 < t - v)).ne'
  have hden' : ∀ v ∈ Icc (0 : ℝ) h, (t - h) * (t - v) ≠ 0 := by
    intro v hv
    exact (mul_pos (sub_pos.mpr ht) (by linarith [hv.2] : 0 < t - v)).ne'
  have hq : ContinuousOn (fun v : ℝ => (t - h) * v / (h * (t - v))) (Icc 0 h) :=
    (continuous_const.mul continuous_id).continuousOn.div
      (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn hden
  have ha : ContinuousOn (angle h t) (Icc 0 h) :=
    Real.continuous_arcsin.comp_continuousOn (Real.continuous_sqrt.comp_continuousOn hq)
  exact ((continuousOn_const : ContinuousOn
      (fun _ : ℝ => t / ((t - h) * Real.sqrt (t * (t - h)))) (Icc 0 h)).mul ha).sub
    ((Real.continuous_sqrt.mul (Real.continuous_sqrt.comp
      (continuous_const.sub continuous_id))).continuousOn.div
        (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn hden')

theorem primitive_zero (h t : ℝ) : primitive h t 0 = 0 := by
  simp [primitive, angle]

theorem primitive_top {h t : ℝ} (hh : 0 < h) (ht : h < t) :
    primitive h t h = Real.pi * Real.sqrt t /
      (2 * (t - h) * Real.sqrt (t - h)) := by
  have hb : 0 < t - h := sub_pos.mpr ht
  have htp : 0 < t := hh.trans ht
  have he : (t - h) * h / (h * (t - h)) = 1 := by
    field_simp
    <;> ring
  simp only [primitive, angle, he, Real.sqrt_one, Real.arcsin_one, sub_self,
    Real.sqrt_zero, mul_zero, zero_div, sub_zero]
  rw [Real.sqrt_mul htp.le]
  field_simp [hb.ne', (Real.sqrt_pos.mpr htp).ne', (Real.sqrt_pos.mpr hb).ne']
  ring_nf
  rw [Real.sq_sqrt htp.le]
  ring

/-- Absolute integrability of the physical Abel--Cauchy kernel follows
from its continuous primitive and its positive derivative. -/
theorem intervalIntegrable_kernel {h t : ℝ} (hh : 0 < h) (ht : h < t) :
    IntervalIntegrable (kernel h t) volume 0 h := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    (g := primitive h t)
  · simpa only [uIcc_of_le hh.le] using continuousOn_primitive hh ht
  · intro v hv
    simp only [min_eq_left hh.le, max_eq_right hh.le] at hv
    exact hasDerivAt_primitive hh ht hv
  · intro v hv
    simp only [min_eq_left hh.le, max_eq_right hh.le] at hv
    exact (kernel_pos hh ht hv).le

theorem integral_kernel {h t : ℝ} (hh : 0 < h) (ht : h < t) :
    (∫ v in (0 : ℝ)..h, kernel h t v) =
      Real.pi * Real.sqrt t / (2 * (t - h) * Real.sqrt (t - h)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hh.le
    (continuousOn_primitive hh ht) (fun v hv => hasDerivAt_primitive hh ht hv)
      (intervalIntegrable_kernel hh ht), primitive_zero, sub_zero]
  exact primitive_top hh ht

theorem hasDerivAt_width_kernel {t v : ℝ} (hv : 0 < v) (ht : v < t) :
    HasDerivAt (fun w => Real.sqrt w / (t - w))
      ((t + v) / (2 * Real.sqrt v * (t - v) ^ 2)) v := by
  have hd := ((hasDerivAt_id v).sqrt hv.ne').div
    ((hasDerivAt_id v).const_sub t) (sub_pos.mpr ht).ne'
  convert hd using 1
  simp only [id_eq]
  have hn : t + v = t - v + 2 * (Real.sqrt v) ^ 2 := by rw [Real.sq_sqrt hv.le]; ring
  rw [hn]
  field_simp [(Real.sqrt_pos.mpr hv).ne', (sub_pos.mpr ht).ne']
  ring_nf
  rw [Real.sq_sqrt hv.le]

theorem kernel_eq_width_deriv {h t v : ℝ} (hv : 0 < v) (ht : v < t) :
    kernel h t v = deriv (fun w => Real.sqrt w / (t - w)) v / Real.sqrt (h - v) := by
  rw [(hasDerivAt_width_kernel hv ht).deriv]
  unfold kernel
  rw [div_div]

theorem rpow_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hx,
    Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Exact physical kernel identity, with its endpoint integrability
proved rather than supplied as a hypothesis. -/
theorem integral_width_deriv {h t : ℝ} (hh : 0 < h) (ht : h < t) :
    (∫ v in (0 : ℝ)..h,
      deriv (fun w => Real.sqrt w / (t - w)) v / Real.sqrt (h - v)) =
        Real.pi * Real.sqrt t / (2 * (t - h) ^ ((3 : ℝ) / 2)) := by
  have he : (∫ v in (0 : ℝ)..h,
      deriv (fun w => Real.sqrt w / (t - w)) v / Real.sqrt (h - v)) =
        ∫ v in (0 : ℝ)..h, kernel h t v := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with v
    intro hv
    have hm : v ∈ Ioc (0 : ℝ) h := by simpa only [uIoc_of_le hh.le] using hv
    exact (kernel_eq_width_deriv hm.1 (hm.2.trans_lt ht)).symm
  rw [he, integral_kernel hh ht, rpow_three_halves (sub_pos.mpr ht)]
  ring

end LeanVerification.AbelCauchy
