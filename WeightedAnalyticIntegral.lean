import LeanVerification.AnalyticEvenDescent
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# Weighted analytic integration from a common convergent multilinear series

The weight is any integrable scalar function, including complex and signed weights.
The coefficient majorant controls one common radius, integration, and every order
of parameter derivative. No analyticity of the integral is assumed.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal

namespace LeanVerification.WeightedAnalyticIntegral

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {𝕜 E Ω : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [MeasurableSpace Ω] {μ : Measure Ω}

def weightedSeries (ω : Ω → 𝕜) (p : Ω → FormalMultilinearSeries 𝕜 E 𝕜)
    (μ : Measure Ω) : FormalMultilinearSeries 𝕜 E 𝕜 :=
  fun n => ∫ t, ω t • p t n ∂μ

theorem integrable_weightedCoefficient {ω : Ω → 𝕜}
    {p : Ω → FormalMultilinearSeries 𝕜 E 𝕜} {M : ℕ → ℝ}
    (hω : Integrable ω μ) (hm : ∀ n, AEStronglyMeasurable (fun t => p t n) μ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖p t n‖ ≤ M n) (n : ℕ) :
    Integrable (fun t => ω t • p t n) μ := by
  apply (hω.norm.mul_const (M n)).mono' (hω.aestronglyMeasurable.smul (hm n))
  filter_upwards [hb n] with t ht
  rw [norm_smul (ω t) (p t n)]
  exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

theorem norm_weightedSeries_le {ω : Ω → 𝕜}
    {p : Ω → FormalMultilinearSeries 𝕜 E 𝕜} {M : ℕ → ℝ}
    (hω : Integrable ω μ) (hm : ∀ n, AEStronglyMeasurable (fun t => p t n) μ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖p t n‖ ≤ M n) (n : ℕ) :
    ‖weightedSeries ω p μ n‖ ≤ (∫ t, ‖ω t‖ ∂μ) * M n := by
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_mul_const]
  apply integral_mono_ae (integrable_weightedCoefficient hω hm hb n).norm
    (hω.norm.mul_const (M n))
  filter_upwards [hb n] with t ht
  rw [norm_smul (ω t) (p t n)]
  exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)

theorem weightedSeries_apply {ω : Ω → 𝕜}
    {p : Ω → FormalMultilinearSeries 𝕜 E 𝕜} {M : ℕ → ℝ}
    (hω : Integrable ω μ) (hm : ∀ n, AEStronglyMeasurable (fun t => p t n) μ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖p t n‖ ≤ M n) (n : ℕ) (v : Fin n → E) :
    weightedSeries ω p μ n v = ∫ t, ω t • p t n v ∂μ := by
  exact ContinuousMultilinearMap.integral_apply
    (integrable_weightedCoefficient hω hm hb n) v

theorem radius_weightedSeries_le {ω : Ω → 𝕜}
    {p : Ω → FormalMultilinearSeries 𝕜 E 𝕜} {M : ℕ → ℝ} {r : ℝ≥0}
    (hω : Integrable ω μ) (hm : ∀ n, AEStronglyMeasurable (fun t => p t n) μ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖p t n‖ ≤ M n)
    (hs : Summable (fun n => M n * (r : ℝ) ^ n)) :
    (r : ℝ≥0∞) ≤ (weightedSeries ω p μ).radius := by
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg _))
    (fun n => mul_le_mul_of_nonneg_right (norm_weightedSeries_le hω hm hb n)
      (pow_nonneg r.coe_nonneg _))
  simpa only [mul_assoc] using hs.mul_left (∫ t, ‖ω t‖ ∂μ)

/-- A measurable common series with an integrable weight retains its radius
under coefficient integration. The pointwise sum and the majorant are explicit. -/
theorem hasFPowerSeriesOnBall_weightedIntegral
    {f : E → Ω → 𝕜} {p : Ω → FormalMultilinearSeries 𝕜 E 𝕜}
    {ω : Ω → 𝕜} {x₀ : E} {r : ℝ≥0} {M : ℕ → ℝ}
    (hr : 0 < r) (hω : Integrable ω μ)
    (hm : ∀ n, AEStronglyMeasurable (fun t => p t n) μ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖p t n‖ ≤ M n)
    (hM : ∀ n, 0 ≤ M n) (hMs : Summable (fun n => M n * (r : ℝ) ^ n))
    (hs : ∀ y : E, ‖y‖₊ < r →
      ∀ᵐ t ∂μ, HasSum (fun n => p t n (fun _ => y)) (f (x₀ + y) t)) :
    HasFPowerSeriesOnBall (fun x => ∫ t, ω t • f x t ∂μ)
      (weightedSeries ω p μ) x₀ r := by
  refine ⟨radius_weightedSeries_le hω hm hb hMs, ENNReal.coe_pos.mpr hr, ?_⟩
  intro y hy
  have hyr : ‖y‖₊ < r := ENNReal.coe_lt_coe.mp (mem_emetric_ball_zero_iff.mp hy)
  have hsum : Summable (fun n => M n * ‖y‖ ^ n) := by
    apply Summable.of_nonneg_of_le (fun n => mul_nonneg (hM n) (pow_nonneg (norm_nonneg _) _))
      (fun n => mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (show ‖y‖ ≤ (r : ℝ) from hyr.le) n) (hM n)) hMs
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun t => ω t • p t n (fun _ => y)) μ :=
    hω.aestronglyMeasurable.smul
      ((ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin n => E) 𝕜
        (fun _ => y)).continuous.comp_aestronglyMeasurable (hm n))
  have hbound (n : ℕ) : ∀ᵐ t ∂μ,
      ‖ω t • p t n (fun _ => y)‖ ≤ ‖ω t‖ * (M n * ‖y‖ ^ n) := by
    filter_upwards [hb n] with t ht
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply ((p t n).le_opNorm _).trans
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul_of_nonneg_right ht (pow_nonneg (norm_nonneg _) _)
  have hsum' : ∀ᵐ t ∂μ, Summable (fun n => ‖ω t‖ * (M n * ‖y‖ ^ n)) :=
    Filter.Eventually.of_forall fun t => hsum.mul_left ‖ω t‖
  have hmaj : Integrable (fun t => ∑' n, ‖ω t‖ * (M n * ‖y‖ ^ n)) μ := by
    simpa only [tsum_mul_left] using hω.norm.mul_const (∑' n, M n * ‖y‖ ^ n)
  have hlim : ∀ᵐ t ∂μ,
      HasSum (fun n => ω t • p t n (fun _ => y)) (ω t • f (x₀ + y) t) := by
    filter_upwards [hs y hyr] with t ht
    exact ht.const_smul (ω t)
  have hi := MeasureTheory.hasSum_integral_of_dominated_convergence
    (fun n t => ‖ω t‖ * (M n * ‖y‖ ^ n)) hmeas hbound hsum' hmaj hlim
  simpa only [← weightedSeries_apply hω hm hb] using hi

/-- Every multilinear parameter derivative at the center passes under the
weighted integral. Arbitrary ordered direction vectors include all mixed derivatives. -/
theorem iteratedFDeriv_weightedIntegral
    {f : E → Ω → 𝕜} {p : Ω → FormalMultilinearSeries 𝕜 E 𝕜}
    {ω : Ω → 𝕜} {x₀ : E} {r : ℝ≥0} {M : ℕ → ℝ}
    (hr : 0 < r) (hω : Integrable ω μ)
    (hm : ∀ n, AEStronglyMeasurable (fun t => p t n) μ)
    (hb : ∀ n, ∀ᵐ t ∂μ, ‖p t n‖ ≤ M n)
    (hM : ∀ n, 0 ≤ M n) (hMs : Summable (fun n => M n * (r : ℝ) ^ n))
    (hp : ∀ᵐ t ∂μ, HasFPowerSeriesOnBall (fun x => f x t) (p t) x₀ r)
    (n : ℕ) (v : Fin n → E) :
    iteratedFDeriv 𝕜 n (fun x => ∫ t, ω t • f x t ∂μ) x₀ v =
      ∫ t, ω t • iteratedFDeriv 𝕜 n (fun x => f x t) x₀ v ∂μ := by
  have hi := hasFPowerSeriesOnBall_weightedIntegral hr hω hm hb hM hMs
    (fun y hy => hp.mono fun t ht => ht.hasSum
      (by simpa only [mem_emetric_ball_zero_iff, enorm_eq_nnnorm] using ENNReal.coe_lt_coe.mpr hy))
  rw [hi.iteratedFDeriv_eq_sum_of_completeSpace v]
  simp_rw [weightedSeries_apply hω hm hb]
  rw [← integral_finset_sum]
  · apply integral_congr_ae
    filter_upwards [hp] with t ht
    rw [ht.iteratedFDeriv_eq_sum_of_completeSpace v, Finset.smul_sum]
  · intro σ _
    exact ((ContinuousMultilinearMap.apply 𝕜 (fun _ : Fin n => E) 𝕜
      (fun i => v (σ i))).integrable_comp (integrable_weightedCoefficient hω hm hb n))

end LeanVerification.WeightedAnalyticIntegral
