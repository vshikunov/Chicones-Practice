import LeanVerification.OneSignChangeConvolution
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# The explicit logarithmic kernel of the weighted-width transform

This module proves positivity, local integrability, differentiation, strict
logarithmic concavity, endpoint estimates, and the integrability of the exact
piecewise majorant used in revision 10. The density is initially written as
`exp ((a - 1) * s) / sqrt (exp (2 * s) - 1)`; its equality with the manuscript
formula is proved below.

These are kernel statements. They do not assert the physical weighted Fubini
identity or differentiation of the physical logarithmic convolution.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.WeightedWidth

def kernelDensity (a s : ℝ) : ℝ :=
  Real.exp ((a - 1) * s) / Real.sqrt (Real.exp (2 * s) - 1)

def kernelPrimitive (a s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, kernelDensity a t

def logKernel (a s : ℝ) : ℝ :=
  2 * Real.exp (-a * s) * kernelPrimitive a s

theorem exp_sub_one_pos {s : ℝ} (hs : 0 < s) :
    0 < Real.exp (2 * s) - 1 := by
  have h : Real.exp 0 < Real.exp (2 * s) := Real.exp_lt_exp.mpr (by linarith)
  simpa using sub_pos.mpr h

theorem kernelDensity_pos (a : ℝ) {s : ℝ} (hs : 0 < s) :
    0 < kernelDensity a s := by
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.mpr (exp_sub_one_pos hs))

theorem continuousAt_kernelDensity (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (kernelDensity a) s := by
  unfold kernelDensity
  fun_prop (disch := exact ne_of_gt (Real.sqrt_pos.mpr (exp_sub_one_pos hs)))

theorem measurable_kernelDensity (a : ℝ) : Measurable (kernelDensity a) := by
  unfold kernelDensity
  fun_prop

theorem kernelDensity_le_center_bound (a R s : ℝ) (hs : 0 < s) (hsR : s ≤ R) :
    kernelDensity a s ≤ Real.exp (|a - 1| * R) * s ^ (-(1 / 2 : ℝ)) := by
  have hbase : s ≤ Real.exp (2 * s) - 1 := by
    have h := Real.add_one_le_exp (2 * s)
    linarith
  have hsqrt : Real.sqrt s ≤ Real.sqrt (Real.exp (2 * s) - 1) := Real.sqrt_le_sqrt hbase
  have hn : Real.exp ((a - 1) * s) ≤ Real.exp (|a - 1| * R) := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (le_abs_self _) hs.le).trans
      (mul_le_mul_of_nonneg_left hsR (abs_nonneg _))
  have hden : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  calc
    kernelDensity a s ≤ Real.exp (|a - 1| * R) / Real.sqrt s :=
      div_le_div₀ (Real.exp_pos _).le hn hden hsqrt
    _ = Real.exp (|a - 1| * R) * s ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, Real.sqrt_eq_rpow, Real.rpow_neg hs.le]

theorem intervalIntegrable_kernelDensity (a : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    IntervalIntegrable (kernelDensity a) volume 0 s := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hs]
  have hi : IntegrableOn (fun t : ℝ => Real.exp (|a - 1| * s) * t ^ (-(1 / 2 : ℝ)))
      (Ioo 0 s) := by
    have ht : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 s :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le hs).mp ht).const_mul _
  apply hi.mono' (measurable_kernelDensity a).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (kernelDensity_pos a ht.1)]
  exact kernelDensity_le_center_bound a s t ht.1 ht.2.le

theorem hasDerivAt_kernelPrimitive (a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (kernelPrimitive a) (kernelDensity a s) s := by
  exact intervalIntegral.integral_hasDerivAt_right
    (intervalIntegrable_kernelDensity a hs.le)
    (measurable_kernelDensity a).aestronglyMeasurable.stronglyMeasurableAtFilter
    (continuousAt_kernelDensity a hs)

theorem kernelDensity_eq_manuscript (a : ℝ) {s : ℝ} (hs : 0 < s) :
    kernelDensity a s = Real.exp (-(2 - a) * s) /
      Real.sqrt (1 - Real.exp (-2 * s)) := by
  have hbase : 0 < Real.exp (2 * s) - 1 := exp_sub_one_pos hs
  have he : 1 - Real.exp (-2 * s) =
      (Real.exp (2 * s) - 1) / Real.exp (2 * s) := by
    rw [show -2 * s = -(2 * s) by ring, Real.exp_neg]
    field_simp
  have hroot : Real.sqrt (Real.exp (2 * s)) = Real.exp s := by
    rw [← Real.exp_half]
    congr 1
    ring
  rw [he, Real.sqrt_div hbase.le, hroot, div_div_eq_mul_div, ← Real.exp_add]
  unfold kernelDensity
  congr 2
  ring

theorem kernelPrimitive_le_center_bound (a R s : ℝ) (hs : 0 ≤ s) (hsR : s ≤ R) :
    kernelPrimitive a s ≤ 2 * Real.exp (|a - 1| * R) * Real.sqrt s := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (-(1 / 2 : ℝ))) volume 0 s :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  calc
    kernelPrimitive a s ≤ ∫ t in (0 : ℝ)..s,
        Real.exp (|a - 1| * R) * t ^ (-(1 / 2 : ℝ)) :=
      intervalIntegral.integral_mono_on_of_le_Ioo hs
        (intervalIntegrable_kernelDensity a hs) (hi.const_mul _)
        (fun t ht => kernelDensity_le_center_bound a R t ht.1 (ht.2.le.trans hsR))
    _ = 2 * Real.exp (|a - 1| * R) * Real.sqrt s := by
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
      norm_num [← Real.sqrt_eq_rpow]
      ring

theorem kernelPrimitive_pos (a : ℝ) {s : ℝ} (hs : 0 < s) :
    0 < kernelPrimitive a s := by
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_kernelDensity a hs.le)
    (fun t ht => kernelDensity_pos a ht.1) hs

theorem logKernel_pos (a : ℝ) {s : ℝ} (hs : 0 < s) :
    0 < logKernel a s := by
  exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) (kernelPrimitive_pos a hs)

theorem hasDerivAt_kernelDensity (a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (kernelDensity a)
      (kernelDensity a s * (a - 2 - 1 / (Real.exp (2 * s) - 1))) s := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (2 * t))
      (Real.exp (2 * s) * 2) s := by
    simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).exp
  have hn : HasDerivAt (fun t : ℝ => Real.exp ((a - 1) * t))
      (Real.exp ((a - 1) * s) * (a - 1)) s := by
    simpa using ((hasDerivAt_id s).const_mul (a - 1)).exp
  have hbase : 0 < Real.exp (2 * s) - 1 := exp_sub_one_pos hs
  have hroot : 0 < Real.sqrt (Real.exp (2 * s) - 1) := Real.sqrt_pos.mpr hbase
  have hsq := Real.sq_sqrt hbase.le
  convert hn.div ((he.sub_const 1).sqrt hbase.ne') hroot.ne' using 1
  unfold kernelDensity
  field_simp [hroot.ne', hbase.ne']
  linear_combination -
    (2 * Real.exp ((a - 1) * s) * Real.sqrt (Real.exp (2 * s) - 1) *
      (Real.exp (2 * s) - 1) * (a - 1)) * hsq

theorem kernelDensity_deriv_neg {a s : ℝ} (ha : a ≤ 2) (hs : 0 < s) :
    deriv (kernelDensity a) s < 0 := by
  rw [(hasDerivAt_kernelDensity a hs).deriv]
  exact mul_neg_of_pos_of_neg (kernelDensity_pos a hs)
    (by have hp := one_div_pos.mpr (exp_sub_one_pos hs); linarith)

theorem strictAntiOn_kernelDensity {a : ℝ} (ha : a ≤ 2) :
    StrictAntiOn (kernelDensity a) (Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun s hs => (continuousAt_kernelDensity a hs).continuousWithinAt
  · intro s hs
    exact kernelDensity_deriv_neg ha (by simpa using hs)

theorem kernelPrimitive_le_tail_bound {a s : ℝ} (ha : a ≤ 2) (hs : 1 ≤ s) :
    kernelPrimitive a s ≤ kernelPrimitive a 1 + (s - 1) * kernelDensity a 1 := by
  have hi : IntervalIntegrable (kernelDensity a) volume 1 s := by
    apply ContinuousOn.intervalIntegrable_of_Icc hs
    intro t ht
    exact (continuousAt_kernelDensity a (by linarith [ht.1])).continuousWithinAt
  unfold kernelPrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_kernelDensity a (by norm_num : (0 : ℝ) ≤ 1)) hi]
  apply add_le_add_left
  calc
    (∫ t in (1 : ℝ)..s, kernelDensity a t) ≤
        ∫ t in (1 : ℝ)..s, kernelDensity a 1 := by
      apply intervalIntegral.integral_mono_on hs hi intervalIntegrable_const
      intro t ht
      exact (strictAntiOn_kernelDensity ha).antitoneOn (show (1 : ℝ) ∈ Ioi 0 by norm_num)
        (show t ∈ Ioi 0 from lt_of_lt_of_le (by norm_num) ht.1) ht.1
    _ = (s - 1) * kernelDensity a 1 := by rw [intervalIntegral.integral_const]; rfl

theorem hasDerivAt_logKernel (a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (logKernel a)
      (2 * Real.exp (-a * s) * (kernelDensity a s - a * kernelPrimitive a s)) s := by
  have he : HasDerivAt (fun t : ℝ => Real.exp (-a * t))
      (Real.exp (-a * s) * -a) s := by
    simpa using ((hasDerivAt_id s).const_mul (-a)).exp
  convert (he.const_mul 2).mul (hasDerivAt_kernelPrimitive a hs) using 1 <;> ring

theorem abs_deriv_logKernel_le (a : ℝ) {s : ℝ} (hs : 0 < s) :
    |deriv (logKernel a) s| ≤ 2 * Real.exp (-a * s) *
      (kernelDensity a s + |a| * kernelPrimitive a s) := by
  rw [(hasDerivAt_logKernel a hs).deriv, abs_mul,
    abs_of_pos (mul_pos (by norm_num) (Real.exp_pos _))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    |kernelDensity a s - a * kernelPrimitive a s| ≤
        |kernelDensity a s| + |a * kernelPrimitive a s| := by
          simpa only [sub_zero, zero_sub, abs_neg] using
            abs_sub_le (kernelDensity a s) 0 (a * kernelPrimitive a s)
    _ = kernelDensity a s + |a| * kernelPrimitive a s := by
      rw [abs_of_pos (kernelDensity_pos a hs), abs_mul,
        abs_of_pos (kernelPrimitive_pos a hs)]

theorem exp_le_center_bound (a : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    Real.exp (-a * s) ≤ Real.exp |a| := by
  apply Real.exp_le_exp.mpr
  calc
    -a * s ≤ |a| * s := mul_le_mul_of_nonneg_right (neg_le_abs a) hs.le
    _ ≤ |a| := mul_le_of_le_one_right (abs_nonneg _) hs1

theorem logKernel_le_center_bound (a : ℝ) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    |logKernel a s| ≤
      (4 * Real.exp |a| * Real.exp |a - 1|) * Real.sqrt s := by
  rw [abs_of_pos (logKernel_pos a hs)]
  have hQ := kernelPrimitive_le_center_bound a 1 s hs.le hs1
  simp only [mul_one] at hQ
  calc
    logKernel a s ≤ (2 * Real.exp |a|) *
        (2 * Real.exp |a - 1| * Real.sqrt s) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (exp_le_center_bound a hs hs1) (by norm_num))
        hQ (kernelPrimitive_pos a hs).le (by positivity)
    _ = _ := by ring

theorem abs_deriv_logKernel_le_center_bound (a : ℝ) {s : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) :
    |deriv (logKernel a) s| ≤
      (2 * (1 + 2 * |a|) * Real.exp |a| * Real.exp |a - 1|) *
        s ^ (-(1 / 2 : ℝ)) := by
  have hq := kernelDensity_le_center_bound a 1 s hs hs1
  have hQ := kernelPrimitive_le_center_bound a 1 s hs.le hs1
  simp only [mul_one] at hq hQ
  have hpow : Real.sqrt s ≤ s ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hs.le, ← Real.sqrt_eq_rpow, ← one_div]
    apply (le_div_iff₀ (Real.sqrt_pos.mpr hs)).mpr
    simpa only [← pow_two, Real.sq_sqrt hs.le] using hs1
  have hQ' : kernelPrimitive a s ≤ 2 * Real.exp |a - 1| * s ^ (-(1 / 2 : ℝ)) :=
    hQ.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  calc
    |deriv (logKernel a) s| ≤ 2 * Real.exp (-a * s) *
        (kernelDensity a s + |a| * kernelPrimitive a s) := abs_deriv_logKernel_le a hs
    _ ≤ 2 * Real.exp |a| *
        (Real.exp |a - 1| * s ^ (-(1 / 2 : ℝ)) +
          |a| * (2 * Real.exp |a - 1| * s ^ (-(1 / 2 : ℝ)))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (exp_le_center_bound a hs hs1) (by norm_num)
      · exact add_le_add hq (mul_le_mul_of_nonneg_left hQ' (abs_nonneg _))
      · exact add_nonneg (kernelDensity_pos a hs).le
          (mul_nonneg (abs_nonneg _) (kernelPrimitive_pos a hs).le)
      · positivity
    _ = _ := by ring

theorem kernelPrimitive_le_linear {a s : ℝ} (ha : a ≤ 2) (hs : 1 ≤ s) :
    kernelPrimitive a s ≤ (kernelPrimitive a 1 + kernelDensity a 1) * (1 + s) := by
  have hq := kernelDensity_pos a (by norm_num : (0 : ℝ) < 1)
  have hQ := kernelPrimitive_pos a (by norm_num : (0 : ℝ) < 1)
  have hb := kernelPrimitive_le_tail_bound ha hs
  nlinarith

theorem logKernel_le_tail_bound {a s : ℝ} (ha : a ≤ 2) (hs : 1 ≤ s) :
    |logKernel a s| ≤ 2 * (kernelPrimitive a 1 + kernelDensity a 1) *
      (1 + s) * Real.exp (-a * s) := by
  have hs' : 0 < s := lt_of_lt_of_le (by norm_num) hs
  rw [abs_of_pos (logKernel_pos a hs')]
  calc
    logKernel a s ≤ 2 * Real.exp (-a * s) *
        ((kernelPrimitive a 1 + kernelDensity a 1) * (1 + s)) :=
      mul_le_mul_of_nonneg_left (kernelPrimitive_le_linear ha hs) (by positivity)
    _ = _ := by ring

theorem abs_deriv_logKernel_le_tail_bound {a s : ℝ} (ha : a ≤ 2) (hs : 1 ≤ s) :
    |deriv (logKernel a) s| ≤
      2 * (1 + |a|) * (kernelPrimitive a 1 + kernelDensity a 1) *
        (1 + s) * Real.exp (-a * s) := by
  have hs' : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hQ := kernelPrimitive_le_linear ha hs
  have hq1 := kernelDensity_pos a (by norm_num : (0 : ℝ) < 1)
  have hQ1 := kernelPrimitive_pos a (by norm_num : (0 : ℝ) < 1)
  have hq : kernelDensity a s ≤
      (kernelPrimitive a 1 + kernelDensity a 1) * (1 + s) := by
    have hqle := (strictAntiOn_kernelDensity ha).antitoneOn
      (show (1 : ℝ) ∈ Ioi 0 by norm_num) (show s ∈ Ioi 0 from hs') hs
    nlinarith
  calc
    |deriv (logKernel a) s| ≤ 2 * Real.exp (-a * s) *
        (kernelDensity a s + |a| * kernelPrimitive a s) := abs_deriv_logKernel_le a hs'
    _ ≤ 2 * Real.exp (-a * s) *
        ((kernelPrimitive a 1 + kernelDensity a 1) * (1 + s) +
          |a| * ((kernelPrimitive a 1 + kernelDensity a 1) * (1 + s))) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hq (mul_le_mul_of_nonneg_left hQ (abs_nonneg _))) (by positivity)
    _ = _ := by ring

theorem kernelLogDerivative_eq (a : ℝ) {s : ℝ} (hs : 0 < s) :
    Convolution.kernelLogDerivative (logKernel a) s =
      -a + kernelDensity a s / kernelPrimitive a s := by
  unfold Convolution.kernelLogDerivative
  rw [(hasDerivAt_logKernel a hs).deriv]
  unfold logKernel
  field_simp [(kernelPrimitive_pos a hs).ne', (Real.exp_pos (-a * s)).ne']
  <;> ring

theorem hasDerivAt_density_primitive_ratio (a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => -a + kernelDensity a t / kernelPrimitive a t)
      ((kernelDensity a s * (a - 2 - 1 / (Real.exp (2 * s) - 1)) *
        kernelPrimitive a s - kernelDensity a s * kernelDensity a s) /
        (kernelPrimitive a s) ^ 2) s := by
  exact ((hasDerivAt_kernelDensity a hs).div
    (hasDerivAt_kernelPrimitive a hs) (kernelPrimitive_pos a hs).ne').const_add (-a)

theorem strictAntiOn_kernelLogDerivative {a : ℝ} (ha : a ≤ 2) :
    StrictAntiOn (Convolution.kernelLogDerivative (logKernel a)) (Ioi 0) := by
  have hd : StrictAntiOn (fun t => -a + kernelDensity a t / kernelPrimitive a t)
      (Ioi 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
    · exact fun s hs => (hasDerivAt_density_primitive_ratio a hs).continuousAt.continuousWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa using hs
      rw [(hasDerivAt_density_primitive_ratio a hs').deriv]
      have hq := kernelDensity_pos a hs'
      have hQ := kernelPrimitive_pos a hs'
      have hn : kernelDensity a s * (a - 2 - 1 / (Real.exp (2 * s) - 1)) < 0 := by
        rw [← (hasDerivAt_kernelDensity a hs').deriv]
        exact kernelDensity_deriv_neg ha hs'
      exact div_neg_of_neg_of_pos
        (sub_neg.mpr ((mul_neg_of_neg_of_pos hn hQ).trans (mul_pos hq hq)))
        (sq_pos_of_pos hQ)
  intro x hx y hy hxy
  rw [kernelLogDerivative_eq a hx, kernelLogDerivative_eq a hy]
  exact hd hx hy hxy

theorem integrableOn_linear_exp_tail {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun s : ℝ => (1 + s) * Real.exp (-b * s)) (Ioi 1) := by
  have hb2 : 0 < b / 2 := by linarith
  have hp : (fun s : ℝ => 1 + s) =O[atTop] (fun s => Real.exp ((b / 2) * s)) := by
    simpa using ((isLittleO_pow_exp_pos_mul_atTop 0 hb2).add
      (isLittleO_pow_exp_pos_mul_atTop 1 hb2)).isBigO
  have ho : (fun s : ℝ => (1 + s) * Real.exp (-b * s)) =O[atTop]
      (fun s => Real.exp (-(b / 2) * s)) := by
    convert hp.mul (Asymptotics.isBigO_refl (fun s => Real.exp (-b * s)) atTop) using 1
    ext s
    rw [← Real.exp_add]
    congr 1
    ring
  exact integrable_of_isBigO_exp_neg hb2 (by fun_prop) ho

def endpointMajorant (a s : ℝ) : ℝ :=
  if s ≤ 1 then s ^ (-(1 / 2 : ℝ)) else (1 + s) * Real.exp (-(3 + a) * s)

theorem measurable_endpointMajorant (a : ℝ) : Measurable (endpointMajorant a) := by
  unfold endpointMajorant
  exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)

theorem integrableOn_endpointMajorant {a : ℝ} (ha : -3 < a) :
    IntegrableOn (endpointMajorant a) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 1 by norm_num), integrableOn_union]
  constructor
  · have hi : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) (Ioc 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num) :
        IntervalIntegrable (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) volume 0 1).1
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simp [endpointMajorant, hs.2]
  · apply (integrableOn_linear_exp_tail (show 0 < 3 + a by linarith)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    simp [endpointMajorant, not_le.mpr (show 1 < s from hs)]

@[simp] theorem logKernel_zero (a : ℝ) : logKernel a 0 = 0 := by
  simp [logKernel, kernelPrimitive]

theorem tendsto_logKernel_zero_right (a : ℝ) :
    Tendsto (logKernel a) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply squeeze_zero_norm'
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with s hs hs1
    exact logKernel_le_center_bound a hs (show s ≤ 1 from hs1.le)
  · have ht : Tendsto (fun s : ℝ =>
        (4 * Real.exp |a| * Real.exp |a - 1|) * Real.sqrt s) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using ((continuous_const.mul Real.continuous_sqrt).tendsto (0 : ℝ))
    exact ht.mono_left nhdsWithin_le_nhds

end LeanVerification.WeightedWidth
