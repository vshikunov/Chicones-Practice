import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A removable square-root quotient at a simple turn

If f and v vanish at c and v has nonzero derivative, f/sqrt(v) is
continuous at c with value zero. This is derived from the actual
derivatives and does not assume an endpoint bound.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification

theorem rpow_three_halves_eq_mul_sqrt {v : ℝ} (hv : 0 ≤ v) :
    v ^ ((3 : ℝ) / 2) = v * Real.sqrt v := by
  rcases hv.eq_or_lt with hv | hv
  · rw [← hv]
    norm_num
  · rw [show (3 : ℝ) / 2 = 1 + (1 : ℝ) / 2 by ring, Real.rpow_add hv,
      Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem rpow_three_halves_div_sq {v : ℝ} (hv : 0 ≤ v) :
    v ^ ((3 : ℝ) / 2) / v ^ 2 = 1 / Real.sqrt v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  · rw [rpow_three_halves_eq_mul_sqrt hv]
    calc
      _ = Real.sqrt v / v := by field_simp; ring
      _ = _ := Real.sqrt_div_self'

theorem continuousAt_div_sqrt_of_simple_zero {f v : ℝ → ℝ} {c f₁ v₁ : ℝ}
    (hf : HasDerivAt f f₁ c) (hv : HasDerivAt v v₁ c)
    (hfc : f c = 0) (hvc : v c = 0) (hv₁ : v₁ ≠ 0) :
    ContinuousAt (fun x => f x / Real.sqrt (v x)) c := by
  have hratio : Tendsto (fun x => f x / v x) (𝓝[≠] c) (𝓝 (f₁ / v₁)) := by
    apply ((hasDerivAt_iff_tendsto_slope.mp hf).div (hasDerivAt_iff_tendsto_slope.mp hv) hv₁).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxc : x - c ≠ 0 := sub_ne_zero.mpr (by simpa only [mem_compl_iff, mem_singleton_iff] using hx)
    change slope f c x / slope v c x = f x / v x
    rw [slope_def_field, slope_def_field, hfc, hvc, sub_zero, sub_zero, div_div_div_cancel_right₀ hxc]
  have hsqrt : Tendsto (fun x => Real.sqrt (v x)) (𝓝[≠] c) (𝓝 0) := by
    simpa only [hvc, Real.sqrt_zero] using hv.continuousAt.sqrt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] c ≤ 𝓝 c)
  have hprod : Tendsto (fun x => f x / v x * Real.sqrt (v x)) (𝓝[≠] c) (𝓝 0) := by
    simpa only [mul_zero] using hratio.mul hsqrt
  have hlim : Tendsto (fun x => f x / Real.sqrt (v x)) (𝓝[≠] c) (𝓝 0) := by
    apply hprod.congr
    intro x
    calc
      _ = f x * (Real.sqrt (v x) / v x) := by ring
      _ = _ := by rw [Real.sqrt_div_self']; ring
  apply continuousWithinAt_compl_self.mp
  change Tendsto (fun x => f x / Real.sqrt (v x)) (𝓝[≠] c) (𝓝 (f c / Real.sqrt (v c)))
  simpa only [hfc, zero_div] using hlim

end LeanVerification
