import LeanVerification.PairedCoefficients

/-!
# Expanded paired curvature coefficient

The displayed coefficient is derived from the actual first four
derivatives of sqrt(S-W), including all denominator conditions.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace LeanVerification.PairedMode

set_option maxHeartbeats 2200000

theorem hasDerivAt_auxiliary_second {W : ℝ → ℝ} {S x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x) :
    HasDerivAt (deriv (deriv (auxiliary W S)))
      (-deriv (deriv (deriv W)) x / (2 * auxiliary W S x) -
        3 * deriv W x * deriv (deriv W) x / (4 * auxiliary W S x ^ 3) -
        3 * deriv W x ^ 3 / (8 * auxiliary W S x ^ 5)) x := by
  have hs : 0 < auxiliary W S x := Real.sqrt_pos.mpr hSigma
  have he : deriv (deriv (auxiliary W S)) =ᶠ[𝓝 x] fun z =>
      -deriv (deriv W) z / (2 * auxiliary W S z) -
        deriv W z ^ 2 / (4 * auxiliary W S z ^ 3) := by
    filter_upwards [hW.eventually_analyticAt,
      (continuousAt_const.sub hW.continuousAt).eventually (Ioi_mem_nhds hSigma)] with z hzW hzSigma
    exact (hasDerivAt_auxiliary_deriv hzW hzSigma).deriv
  have ds := hasDerivAt_auxiliary hW hSigma
  have hd := ((hW.deriv.deriv.differentiableAt.hasDerivAt.neg.div
    (ds.const_mul 2) (mul_ne_zero (by norm_num) hs.ne')).sub
      ((hW.deriv.differentiableAt.hasDerivAt.pow 2).div ((ds.pow 3).const_mul 4)
        (mul_ne_zero (by norm_num) (pow_ne_zero 3 hs.ne')))).congr_of_eventuallyEq he
  convert hd using 1
  field_simp
  ring

theorem hasDerivAt_auxiliary_third {W : ℝ → ℝ} {S x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x) :
    HasDerivAt (deriv (deriv (deriv (auxiliary W S))))
      (-deriv (deriv (deriv (deriv W))) x / (2 * auxiliary W S x) -
        (4 * deriv W x * deriv (deriv (deriv W)) x + 3 * deriv (deriv W) x ^ 2) /
          (4 * auxiliary W S x ^ 3) -
        9 * deriv W x ^ 2 * deriv (deriv W) x / (4 * auxiliary W S x ^ 5) -
        15 * deriv W x ^ 4 / (16 * auxiliary W S x ^ 7)) x := by
  have hs : 0 < auxiliary W S x := Real.sqrt_pos.mpr hSigma
  have he : deriv (deriv (deriv (auxiliary W S))) =ᶠ[𝓝 x] fun z =>
      -deriv (deriv (deriv W)) z / (2 * auxiliary W S z) -
        3 * deriv W z * deriv (deriv W) z / (4 * auxiliary W S z ^ 3) -
        3 * deriv W z ^ 3 / (8 * auxiliary W S z ^ 5) := by
    filter_upwards [hW.eventually_analyticAt,
      (continuousAt_const.sub hW.continuousAt).eventually (Ioi_mem_nhds hSigma)] with z hzW hzSigma
    exact (hasDerivAt_auxiliary_second hzW hzSigma).deriv
  have ds := hasDerivAt_auxiliary hW hSigma
  have dg := hW.deriv.differentiableAt.hasDerivAt
  have dg₁ := hW.deriv.deriv.differentiableAt.hasDerivAt
  have dg₂ := hW.deriv.deriv.deriv.differentiableAt.hasDerivAt
  have hd := (((dg₂.neg.div (ds.const_mul 2) (mul_ne_zero (by norm_num) hs.ne')).sub
    (((dg.const_mul 3).mul dg₁).div ((ds.pow 3).const_mul 4)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hs.ne')))).sub
      (((dg.pow 3).const_mul 3).div ((ds.pow 5).const_mul 8)
        (mul_ne_zero (by norm_num) (pow_ne_zero 5 hs.ne')))).congr_of_eventuallyEq he
  convert hd using 1
  field_simp
  ring

def expandedCurvature (W : ℝ → ℝ) (S x : ℝ) : ℝ :=
  (6 * sigma W S x * denominator W S x * deriv (deriv (deriv (deriv W))) x -
    15 * deriv W x * denominator W S x * deriv (deriv (deriv W)) x -
    20 * sigma W S x ^ 2 * deriv (deriv (deriv W)) x ^ 2) /
      (9 * denominator W S x ^ 2)

theorem coefficientQ_eq_expanded {W : ℝ → ℝ} {S h x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x)
    (hδ : h < S) (hA : 0 < denominator W S x) :
    CriticalEnergy.coefficientQ W (auxiliary W S) h x = expandedCurvature W S x := by
  have hs : 0 < auxiliary W S x := Real.sqrt_pos.mpr hSigma
  have hsq : auxiliary W S x ^ 2 = S - W x := Real.sq_sqrt hSigma.le
  have h1 := (hasDerivAt_auxiliary hW hSigma).deriv
  have h2 := (hasDerivAt_auxiliary_deriv hW hSigma).deriv
  have h3 := (hasDerivAt_auxiliary_second hW hSigma).deriv
  have h4 := (hasDerivAt_auxiliary_third hW hSigma).deriv
  have hH := coefficientH_eq (h := h) hW hSigma
  dsimp only [CriticalEnergy.coefficientQ, CriticalMode.curvature]
  simp only [hH]
  dsimp only [CriticalEnergy.coefficientH1, CriticalEnergy.coefficientH2, CriticalEnergy.gap,
    CriticalEnergy.jet, Function.iterate_succ_apply']
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, h1, h2, h3, h4]
  dsimp only [expandedCurvature, denominator, sigma]
  have hAn : deriv W x ^ 2 + 2 * auxiliary W S x ^ 2 * deriv (deriv W) x ≠ 0 := by
    simpa only [denominator, sigma, ← hsq] using hA.ne'
  simp only [show h - W x = auxiliary W S x ^ 2 - (S - h) by linarith [hsq], ← hsq]
  have hdn : S - h ≠ 0 := (sub_pos.mpr hδ).ne'
  generalize hdvar : S - h = δ at hdn ⊢
  generalize hAvar : deriv W x ^ 2 + 2 * auxiliary W S x ^ 2 * deriv (deriv W) x = A at hAn ⊢
  field_simp [hs.ne', hdn, hAn]
  rw [← hAvar]
  ring

end LeanVerification.PairedMode
