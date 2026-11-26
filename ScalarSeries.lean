import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Pow
import LeanVerification.SequenceSignBlocks

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace LeanVerification.ScalarSeries

def sum (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑' n, a n * x ^ n

/-- Convergence throughout a real disk, as supplied by a positive
power-series radius. No differentiability assumption is included. -/
def ConvergesOn (a : ℕ → ℝ) (R : ℝ) : Prop :=
  ∀ x : ℝ, |x| < R → Summable (fun n => a n * x ^ n)

theorem hasFPowerSeriesOnBall {a : ℕ → ℝ} {R : ℝ}
    (hR : 0 < R) (h : ConvergesOn a R) :
    HasFPowerSeriesOnBall (sum a) (FormalMultilinearSeries.ofScalars ℝ a)
      0 (ENNReal.ofReal R) := by
  refine ⟨?_, ENNReal.ofReal_pos.mpr hR, ?_⟩
  · apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hr' : (r : ℝ) < R := by
      have hh : r < R.toNNReal := ENNReal.coe_lt_coe.mp hr
      have hh' : (r : ℝ) < (R.toNNReal : ℝ) := hh
      simpa only [Real.coe_toNNReal _ hR.le] using hh'
    have hrabs : |(r : ℝ)| < R := by
      rw [NNReal.abs_eq]
      exact hr'
    have hc := (h (r : ℝ) hrabs).tendsto_atTop_zero
    have hn := (continuous_norm.tendsto 0).comp hc
    apply (FormalMultilinearSeries.ofScalars ℝ a).le_radius_of_tendsto (l := 0)
    simpa only [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow,
      NNReal.norm_eq, norm_zero, Function.comp_def] using hn
  · intro x hx
    have hxR : |x| < R := by
      simpa only [EMetric.mem_ball, edist_lt_ofReal, Real.dist_eq, sub_zero] using hx
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add, sum]
      using (h x hxR).hasSum

theorem analyticOnNhd {a : ℕ → ℝ} {R : ℝ}
    (hR : 0 < R) (h : ConvergesOn a R) :
    AnalyticOnNhd ℝ (sum a) (Ioo (-R) R) := by
  intro x hx
  apply (hasFPowerSeriesOnBall hR h).analyticAt_of_mem
  simpa only [EMetric.mem_ball, edist_lt_ofReal, Real.dist_eq, sub_zero, abs_lt] using hx

theorem ConvergesOn.const_mul {a : ℕ → ℝ} {R : ℝ}
    (h : ConvergesOn a R) (q : ℝ) : ConvergesOn (fun n => q * a n) R := by
  intro x hx
  simpa only [mul_assoc] using (h x hx).mul_left q

theorem sum_const_mul (a : ℕ → ℝ) (q x : ℝ) :
    sum (fun n => q * a n) x = q * sum a x := by
  simp only [sum, mul_assoc, tsum_mul_left]

theorem hasSum_euler {a : ℕ → ℝ} {R x : ℝ}
    (hR : 0 < R) (h : ConvergesOn a R) (hx : |x| < R) :
    HasSum (fun n : ℕ => (n : ℝ) * a n * x ^ n) (x * deriv (sum a) x) := by
  let p := FormalMultilinearSeries.ofScalars ℝ a
  have hp := hasFPowerSeriesOnBall hR h
  have hxB : x ∈ EMetric.ball (0 : ℝ) (ENNReal.ofReal R) := by
    simpa only [EMetric.mem_ball, edist_lt_ofReal, Real.dist_eq, sub_zero] using hx
  have hh := (ContinuousLinearMap.apply ℝ ℝ x).hasSum (hp.fderiv.hasSum hxB)
  have he : HasSum (fun n => ((n + 1 : ℕ) : ℝ) * a (n + 1) * x ^ (n + 1))
      (x * deriv (sum a) x) := by
    simpa only [ContinuousLinearMap.apply_apply, zero_add,
      FormalMultilinearSeries.derivSeries_apply_diag,
      FormalMultilinearSeries.ofScalars_apply_eq, nsmul_eq_mul, smul_eq_mul,
      fderiv_eq_smul_deriv, mul_assoc] using hh
  have ht := (hasSum_nat_add_iff 1 (f := fun n : ℕ => (n : ℝ) * a n * x ^ n)).mp he
  simpa only [Finset.sum_range_one, Nat.cast_zero, zero_mul, add_zero] using ht

theorem hasSum_factor {a : ℕ → ℝ} {R x : ℝ}
    (hR : 0 < R) (h : ConvergesOn a R) (hx : |x| < R) (c : ℝ) :
    HasSum (fun n => SequenceSigns.factorCoefficient c a n * x ^ n)
      (x * deriv (sum a) x - c * sum a x) := by
  convert (hasSum_euler hR h hx).sub ((h x hx).hasSum.mul_left c) using 1
  · ext n
    dsimp [SequenceSigns.factorCoefficient]
    ring

theorem ConvergesOn.factor {a : ℕ → ℝ} {R : ℝ}
    (h : ConvergesOn a R) (hR : 0 < R) (c : ℝ) :
    ConvergesOn (SequenceSigns.factorCoefficient c a) R :=
  fun x hx => (hasSum_factor hR h hx c).summable

theorem sum_factor {a : ℕ → ℝ} {R x : ℝ}
    (hR : 0 < R) (h : ConvergesOn a R) (hx : |x| < R) (c : ℝ) :
    sum (SequenceSigns.factorCoefficient c a) x =
      x * deriv (sum a) x - c * sum a x :=
  (hasSum_factor hR h hx c).tsum_eq

theorem sum_pos {a : ℕ → ℝ} {R x : ℝ} {k : ℕ}
    (h : ConvergesOn a R) (hx : x ∈ Ioo 0 R)
    (ha : ∀ n, 0 ≤ a n) (hk : 0 < a k) : 0 < sum a x := by
  apply (h x (by simpa only [abs_of_pos hx.1] using hx.2)).tsum_pos
    (fun n => mul_nonneg (ha n) (pow_nonneg hx.1.le n)) k
  exact mul_pos hk (pow_pos hx.1 k)

end LeanVerification.ScalarSeries
