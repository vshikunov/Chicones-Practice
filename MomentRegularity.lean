import LeanVerification.StieltjesMoments
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.Stieltjes

noncomputable section

/-- One majorant controls every moment on a bounded interval of nonnegative
exponents, including exponent zero. -/
theorem moment_uniform_integrand_bound {H t r S A : ℝ}
    (hH : 0 < H) (ht : H ≤ t) (hr : 0 ≤ r) (hrS : r ≤ S) :
    ‖A * t ^ (-r - (3 : ℝ) / 2)‖ ≤
      (1 + H ^ (-S)) * ‖A * t ^ (-(3 : ℝ) / 2)‖ := by
  apply (moment_integrand_bound hH ht hr).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rcases le_or_lt 1 H with hH1 | hH1
  · have hp : H ^ (-r) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le hH1 (neg_nonpos.mpr hr)
    exact hp.trans (le_add_of_nonneg_right (Real.rpow_nonneg hH.le _))
  · have hp : H ^ (-r) ≤ H ^ (-S) :=
      Real.rpow_le_rpow_of_exponent_ge hH hH1.le (neg_le_neg hrS)
    exact hp.trans (le_add_of_nonneg_left zero_le_one)

/-- The actual weighted moment transform is continuous all the way to
exponent zero. No logarithmic moment at zero is assumed. -/
theorem continuousOn_weightedMoment {μ : Measure ℝ} {H : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    ContinuousOn (weightedMoment μ f) (Ici 0) := by
  intro r hr
  unfold weightedMoment
  apply continuousWithinAt_of_dominated
    (bound := fun t => (1 + H ^ (-(r+1))) * ‖f t * t ^ (-(3 : ℝ)/2)‖)
  · exact Eventually.of_forall fun s =>
      (hf.mul (measurable_id.pow_const _)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (lt_add_one r)).filter_mono nhdsWithin_le_nhds] with s hs hsR
    filter_upwards [hsupp] with t ht
    exact moment_uniform_integrand_bound hH ht hs hsR.le
  · exact hint.norm.const_mul _
  · filter_upwards [hsupp] with t ht
    have hp : t ≠ 0 := ne_of_gt (hH.trans_le ht)
    exact (continuous_const.mul ((Real.continuous_const_rpow hp).comp
      (continuous_id.neg.sub continuous_const))).continuousWithinAt

theorem continuousOn_normalizedMoment {μ : Measure ℝ} {H : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    ContinuousOn (normalizedMoment μ f) (Ici 0) := by
  exact (continuousOn_weightedMoment hH hf hsupp hint).div_const Real.pi

end
end LeanVerification.Stieltjes
