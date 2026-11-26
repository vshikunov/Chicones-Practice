import LeanVerification.Loud.EnergyModeFamily

/-!
# Coefficients of the paired critical mode

For the actual auxiliary function sqrt(S-W), the auxiliary denominator
and its energy ratio are calculated from derivatives of that function.
The resulting curvature has zero energy derivative. The upper energy
S remains fixed throughout these derivatives.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace LeanVerification.PairedMode

set_option maxHeartbeats 1400000

def sigma (W : ℝ → ℝ) (S x : ℝ) : ℝ := S - W x

def auxiliary (W : ℝ → ℝ) (S x : ℝ) : ℝ := Real.sqrt (sigma W S x)

def denominator (W : ℝ → ℝ) (S x : ℝ) : ℝ :=
  deriv W x ^ 2 + 2 * sigma W S x * deriv (deriv W) x

theorem analyticAt_auxiliary {W : ℝ → ℝ} {S x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x) :
    AnalyticAt ℝ (auxiliary W S) x := by
  exact (Real.contDiffAt_sqrt (n := ω) hSigma.ne').analyticAt.comp_of_eq
    (f := sigma W S) (analyticAt_const.sub hW) rfl

theorem analyticAt_denominator {W : ℝ → ℝ} {S x : ℝ}
    (hW : AnalyticAt ℝ W x) : AnalyticAt ℝ (denominator W S) x :=
  (hW.deriv.pow 2).add ((analyticAt_const.mul (analyticAt_const.sub hW)).mul hW.deriv.deriv)

theorem hasDerivAt_auxiliary {W : ℝ → ℝ} {S x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x) :
    HasDerivAt (auxiliary W S) (-deriv W x / (2 * auxiliary W S x)) x :=
  hW.differentiableAt.hasDerivAt.const_sub S |>.sqrt hSigma.ne'

theorem hasDerivAt_auxiliary_deriv {W : ℝ → ℝ} {S x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x) :
    HasDerivAt (deriv (auxiliary W S))
      (-deriv (deriv W) x / (2 * auxiliary W S x) -
        deriv W x ^ 2 / (4 * auxiliary W S x ^ 3)) x := by
  have hs : 0 < auxiliary W S x := Real.sqrt_pos.mpr hSigma
  have he : deriv (auxiliary W S) =ᶠ[𝓝 x]
      fun z => -deriv W z / (2 * auxiliary W S z) := by
    filter_upwards [hW.eventually_analyticAt,
      (continuousAt_const.sub hW.continuousAt).eventually (Ioi_mem_nhds hSigma)] with z hzW hzSigma
    exact (hasDerivAt_auxiliary hzW hzSigma).deriv
  have hd := (hW.deriv.differentiableAt.hasDerivAt.neg.div
    ((hasDerivAt_auxiliary hW hSigma).const_mul 2) (mul_ne_zero (by norm_num) hs.ne')).congr_of_eventuallyEq he
  convert hd using 1
  field_simp
  ring

theorem coefficientH_eq {W : ℝ → ℝ} {S h x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x) :
    CriticalEnergy.coefficientH W (auxiliary W S) h x =
      (S - h) * denominator W S x / (2 * auxiliary W S x ^ 3) := by
  have hs : 0 < auxiliary W S x := Real.sqrt_pos.mpr hSigma
  have hsq : auxiliary W S x ^ 2 = S - W x := Real.sq_sqrt hSigma.le
  have h1 := (hasDerivAt_auxiliary hW hSigma).deriv
  have h2 := (hasDerivAt_auxiliary_deriv hW hSigma).deriv
  dsimp [CriticalEnergy.coefficientH, CriticalEnergy.gap, CriticalEnergy.jet,
    Function.iterate_succ_apply']
  rw [h1, h2]
  dsimp only [denominator, sigma]
  rw [show h - W x = auxiliary W S x ^ 2 - (S - h) by linarith [hsq], ← hsq]
  field_simp
  ring

theorem coefficientH_pos {W : ℝ → ℝ} {S h x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x)
    (hδ : h < S) (hA : 0 < denominator W S x) :
    0 < CriticalEnergy.coefficientH W (auxiliary W S) h x := by
  rw [coefficientH_eq hW hSigma]
  exact div_pos (mul_pos (sub_pos.mpr hδ) hA)
    (mul_pos (by norm_num) (pow_pos (Real.sqrt_pos.mpr hSigma) _))

theorem energyRatio_eq {W : ℝ → ℝ} {S h x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x)
    (hδ : h < S) (hA : 0 < denominator W S x) :
    CriticalEnergy.energyRatio W (auxiliary W S) h x = -1 / (S - h) := by
  have hs : 0 < auxiliary W S x := Real.sqrt_pos.mpr hSigma
  have hsq : auxiliary W S x ^ 2 = S - W x := Real.sq_sqrt hSigma.le
  have h2 := (hasDerivAt_auxiliary_deriv hW hSigma).deriv
  dsimp only [CriticalEnergy.energyRatio, CriticalEnergy.jet]
  change 2 * deriv (deriv (auxiliary W S)) x /
    CriticalEnergy.coefficientH W (auxiliary W S) h x = _
  rw [h2, coefficientH_eq hW hSigma]
  have hdn : S - h ≠ 0 := (sub_pos.mpr hδ).ne'
  have hAn := hA.ne'
  dsimp only [denominator, sigma] at hAn ⊢
  rw [← hsq] at hAn ⊢
  field_simp [hs.ne', hdn, hAn]
  ring

theorem hasDerivAt_curvature_energy_zero {W : ℝ → ℝ} {S h x : ℝ}
    (hW : AnalyticAt ℝ W x) (hSigma : 0 < sigma W S x)
    (hδ : h < S) (hA : 0 < denominator W S x) :
    HasDerivAt (fun E => CriticalEnergy.coefficientQ W (auxiliary W S) E x) 0 h := by
  have hφ := analyticAt_auxiliary hW hSigma
  have hH := coefficientH_pos hW hSigma hδ hA
  have he : CriticalEnergy.energyRatio W (auxiliary W S) h =ᶠ[𝓝 x]
      fun _ => -1 / (S - h) := by
    filter_upwards [hW.eventually_analyticAt,
      (continuousAt_const.sub hW.continuousAt).eventually (Ioi_mem_nhds hSigma),
      (analyticAt_denominator (S := S) hW).continuousAt.eventually (Ioi_mem_nhds hA)]
      with z hzW hzSigma hzA
    exact energyRatio_eq hzW hzSigma hδ hzA
  have h1 : deriv (CriticalEnergy.energyRatio W (auxiliary W S) h) x = 0 := by
    rw [he.deriv_eq, deriv_const]
  have h2 : deriv (deriv (CriticalEnergy.energyRatio W (auxiliary W S) h)) x = 0 := by
    rw [he.deriv.deriv_eq]
    simp
  have hd := CriticalEnergy.hasDerivAt_coefficientQ_energy_spatial hW hφ hH.ne'
    (Real.sqrt_pos.mpr hSigma).ne'
  simpa only [h1, h2, zero_div, mul_zero, sub_zero] using hd

end LeanVerification.PairedMode
