import LeanVerification.SpectralTaylor
import LeanVerification.EulerSeries

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators NNReal ENNReal

namespace LeanVerification.UniformSpectralSeries

def complexSum (a : ℕ → ℝ) (z : ℂ) : ℂ := ∑' n, (a n : ℂ) * z ^ n

def derivativeCoefficient (a : ℕ → ℝ) (n : ℕ) : ℝ := (n + 1 : ℝ) * a (n + 1)

def iteratedCoefficient (a : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => a
  | k + 1 => derivativeCoefficient (iteratedCoefficient a k)

theorem hasFPowerSeriesOnBall {a : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) :
    HasFPowerSeriesOnBall (complexSum a)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))) 0 (ENNReal.ofReal H) := by
  let p := FormalMultilinearSeries.ofScalars ℂ (fun n => (a n : ℂ))
  have hradius : ENNReal.ofReal H ≤ p.radius := by
    apply ENNReal.le_of_forall_nnreal_lt
    intro r hr
    have hr' : (r : ℝ) < H := by
      have hh : r < H.toNNReal := ENNReal.coe_lt_coe.mp hr
      have hh' : (r : ℝ) < (H.toNNReal : ℝ) := hh
      simpa only [Real.coe_toNNReal _ hH.le] using hh'
    have ht := (continuous_norm.tendsto 0).comp
      (ha (r : ℝ) (by simpa only [NNReal.abs_eq] using hr')).tendsto_atTop_zero
    apply p.le_radius_of_tendsto (l := 0)
    simpa only [p, FormalMultilinearSeries.ofScalars_norm, Complex.norm_real,
      norm_mul, norm_pow, NNReal.norm_eq, norm_zero, Function.comp_def] using ht
  refine ⟨hradius, ENNReal.ofReal_pos.mpr hH, ?_⟩
  intro z hz
  have hzr : z ∈ EMetric.ball (0 : ℂ) p.radius :=
    EMetric.ball_subset_ball hradius hz
  have hs := (p.summable hzr).hasSum
  simpa only [p, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    zero_add, complexSum] using hs

theorem hasSum_derivative {a : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) {z : ℂ} (hz : ‖z‖ < H) :
    HasSum (fun n : ℕ => (derivativeCoefficient a n : ℂ) * z ^ n)
      (deriv (complexSum a) z) := by
  have hp := hasFPowerSeriesOnBall hH ha
  have hzB : z ∈ EMetric.ball (0 : ℂ) (ENNReal.ofReal H) := by
    simpa only [EMetric.mem_ball, edist_lt_ofReal, dist_zero_right] using hz
  have he := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum (hp.fderiv.hasSum hzB)
  convert he using 1
  · funext n
    simp only [ContinuousLinearMap.apply_apply, zero_add,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, ContinuousLinearMap.smul_apply,
      FormalMultilinearSeries.derivSeries_coeff_one, FormalMultilinearSeries.coeff_ofScalars,
      nsmul_eq_mul, smul_eq_mul, derivativeCoefficient]
    push_cast
    ring
  · simp only [ContinuousLinearMap.apply_apply, zero_add, fderiv_eq_smul_deriv,
      smul_eq_mul, one_mul]

theorem converges_derivative {a : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) :
    ScalarSeries.ConvergesOn (derivativeCoefficient a) H := by
  intro x hx
  have he := Complex.reCLM.hasSum (hasSum_derivative hH ha
    (show ‖(x : ℂ)‖ < H by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx))
  simp only [Complex.reCLM_apply, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re] at he
  exact he.summable

theorem converges_iteratedCoefficient {a : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) (k : ℕ) :
    ScalarSeries.ConvergesOn (iteratedCoefficient a k) H := by
  induction k with
  | zero => exact ha
  | succ k ih => exact converges_derivative hH ih

theorem converges_shift {a : ℕ → ℝ} {H : ℝ} (ha : ScalarSeries.ConvergesOn a H) :
    ScalarSeries.ConvergesOn (fun n => a (n + 1)) H := by
  intro x hx
  by_cases hx0 : x = 0
  · subst x
    apply summable_of_ne_finset_zero (s := {0})
    intro n hn
    have hn0 : n ≠ 0 := by simpa only [Finset.mem_singleton] using hn
    simp only [zero_pow hn0, mul_zero]
  · have hs := (summable_nat_add_iff 1).mpr (ha x hx)
    convert hs.div_const x using 1
    funext n
    rw [pow_succ]
    field_simp
    ring

theorem iteratedDeriv_eq_series {a : ℕ → ℝ} {H : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) (k : ℕ) {z : ℂ} (hz : ‖z‖ < H) :
    iteratedDeriv k (complexSum a) z = complexSum (iteratedCoefficient a k) z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    have he : iteratedDeriv k (complexSum a) =ᶠ[𝓝 z]
        complexSum (iteratedCoefficient a k) := by
      filter_upwards [(continuous_norm.tendsto z).eventually (Iio_mem_nhds hz)] with w hw
      exact ih hw
    rw [iteratedDeriv_succ, he.deriv_eq]
    exact (hasSum_derivative hH (converges_iteratedCoefficient hH ha k) hz).tsum_eq.symm

/-- Every actual differentiated Taylor series converges uniformly on
each closed complex disk strictly inside the original radius. -/
theorem uniform_iterated_series {a : ℕ → ℝ} {H ρ : ℝ} (hH : 0 < H)
    (ha : ScalarSeries.ConvergesOn a H) (hρ : 0 ≤ ρ) (hρH : ρ < H) (k : ℕ) :
    TendstoUniformlyOn
      (fun N z => ∑ n ∈ Finset.range N, (iteratedCoefficient a k n : ℂ) * z ^ n)
      (iteratedDeriv k (complexSum a)) atTop (Metric.closedBall 0 ρ) := by
  obtain ⟨r, hρr, hrH⟩ := exists_between hρH
  let r' : ℝ≥0 := ⟨r, hρ.trans hρr.le⟩
  have hr : (r' : ℝ≥0∞) < ENNReal.ofReal H := by
    exact ENNReal.coe_lt_coe.mpr (show r' < H.toNNReal by
      exact_mod_cast (show (r' : ℝ) < (H.toNNReal : ℝ) by
        simpa only [Real.coe_toNNReal _ hH.le] using hrH))
  have hu := (hasFPowerSeriesOnBall hH (converges_iteratedCoefficient hH ha k)).tendstoUniformlyOn hr
  have hs : Metric.closedBall (0 : ℂ) ρ ⊆ Metric.ball (0 : ℂ) r' :=
    Metric.closedBall_subset_ball hρr
  have hu' := hu.mono hs
  simp only [FormalMultilinearSeries.partialSum,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] at hu'
  apply hu'.congr_right
  intro z hz
  exact (iteratedDeriv_eq_series hH ha k
    ((by simpa only [Metric.mem_closedBall, dist_zero_right] using hz : ‖z‖ ≤ ρ).trans_lt hρH)).symm

theorem complete_width_uniform_derivatives {F : ℂ → ℂ} {H ρ : ℝ}
    (d : SlitContour.PhysicalCutData F H) {N : ℕ} {t : Fin N → ℝ}
    (hinj : Function.Injective t) (ht : ∀ j, H ≤ t j) (A : Fin N → ℝ)
    (hρ : 0 ≤ ρ) (hρH : ρ < H) (k : ℕ) :
    TendstoUniformlyOn
      (fun M z => ∑ n ∈ Finset.range M,
        (iteratedCoefficient
          (fun j : ℕ => Stieltjes.normalizedMoment (CompleteSpectral.reference H t)
            (CompleteSpectral.density d t A) (j : ℝ)) k n : ℂ) * z ^ n)
      (iteratedDeriv k (fun z => CompleteSpectral.normalizedWidth F t A z - (d.constant : ℂ)))
      atTop (Metric.closedBall 0 ρ) := by
  have ha := SpectralTaylor.moment_converges d.height_pos (CompleteSpectral.support_reference ht)
    (CompleteSpectral.integrable_weighted_density d t A)
  apply (uniform_iterated_series d.height_pos ha hρ hρH k).congr_right
  intro z hz
  have hzn : ‖z‖ < H :=
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz : ‖z‖ ≤ ρ).trans_lt hρH
  apply Filter.EventuallyEq.iteratedDeriv_eq
  filter_upwards [(continuous_norm.tendsto z).eventually (Iio_mem_nhds hzn)] with w hw
  exact (SpectralTaylor.complete_width_hasSum d hinj ht A hw).tsum_eq

/-- The normalized raised-input coefficient series, including its center
extension, has uniform convergence at every differentiated order on every
smaller disk. Its zero-index coefficient is a positive multiple of the
original first moment. -/
theorem raised_moment_uniform_derivatives {μ : Measure ℝ} {f : ℝ → ℝ} {H ρ : ℝ}
    (hH : 0 < H) (hsupp : ∀ᵐ x ∂μ, H ≤ x)
    (hint : Integrable (fun x => f x * x ^ (-(3 : ℝ) / 2)) μ)
    (hρ : 0 ≤ ρ) (hρH : ρ < H) (k : ℕ) :
    TendstoUniformlyOn
      (fun M z => ∑ n ∈ Finset.range M,
        (iteratedCoefficient (fun j => EulerSeries.raisedCoefficient
          (fun i : ℕ => Stieltjes.normalizedMoment μ f (i : ℝ)) (j + 1)) k n : ℂ) * z ^ n)
      (iteratedDeriv k (complexSum (fun j => EulerSeries.raisedCoefficient
        (fun i : ℕ => Stieltjes.normalizedMoment μ f (i : ℝ)) (j + 1))))
      atTop (Metric.closedBall 0 ρ) :=
  uniform_iterated_series hH
    (converges_shift (EulerSeries.raised_converges hH
      (SpectralTaylor.moment_converges hH hsupp hint))) hρ hρH k

end LeanVerification.UniformSpectralSeries
