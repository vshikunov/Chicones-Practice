import LeanVerification.WeightedAnalyticIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Holomorphic compact families and arbitrary integrable complex weights

In one complex parameter, scalar holomorphy and continuity of the compact family
construct a convergent series with values in the Banach space of continuous
functions. No analytic hypothesis on that Banach-valued family is assumed.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal NNReal

namespace LeanVerification.HolomorphicCompactFamily

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- Point evaluation commutes with a genuinely integrable contour integral. -/
theorem circleIntegral_apply {f : ℂ → C(K, ℂ)} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (t : K) :
    (∮ z in C(c, R), f z) t = ∮ z in C(c, R), f z t := by
  have he := (ContinuousMap.evalCLM ℂ t).intervalIntegral_comp_comm hf.out
  simpa only [circleIntegral, map_smul, ContinuousMap.smul_apply] using he.symm

/-- Scalar holomorphy on every compact-family fiber constructs a common
Banach-valued Cauchy series on the entire disc. -/
theorem hasFPowerSeriesOnBall_continuousFamily
    {f : ℂ → C(K, ℂ)} {c : ℂ} {R : ℝ≥0} (hR : 0 < R)
    (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ t : K, DifferentiableOn ℂ (fun z => f z t) (ball c R)) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f c R) c R := by
  have hcircle : CircleIntegrable f c R :=
    (hc.mono sphere_subset_closedBall).circleIntegrable R.coe_nonneg
  apply (hasFPowerSeriesOn_cauchy_integral hcircle hR).congr
  intro w hw
  have hwb : w ∈ ball c (R : ℝ) := by simpa only [Metric.emetric_ball_nnreal] using hw
  have hne : ∀ z ∈ sphere c (R : ℝ), z - w ≠ 0 := by
    intro z hz
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem hz (ne_of_lt hwb))
  have hci : CircleIntegrable (fun z => (z - w)⁻¹ • f z) c R :=
    (((continuousOn_id.sub continuousOn_const).inv₀ hne).smul
      (hc.mono sphere_subset_closedBall)).circleIntegrable R.coe_nonneg
  ext t
  rw [ContinuousMap.smul_apply, circleIntegral_apply hci]
  have hct : ContinuousOn (fun z => f z t) (closedBall c (R : ℝ)) :=
    (ContinuousMap.evalCLM ℂ t).continuous.comp_continuousOn hc
  have hdt : ∀ z ∈ ball c (R : ℝ) \ (∅ : Set ℂ),
      DifferentiableAt ℂ (fun z => f z t) z := by
    intro z hz
    exact (hd t).differentiableAt (isOpen_ball.mem_nhds hz.1)
  simpa only [ContinuousMap.smul_apply] using
    Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      countable_empty hwb hct hdt

section Weighted

variable [MeasurableSpace K] [BorelSpace K] {μ : Measure K} {ω : K → ℂ}

theorem integrable_weightedContinuousMap (hω : Integrable ω μ) (g : C(K, ℂ)) :
    Integrable (fun t => ω t * g t) μ := by
  have hi := hω.bdd_mul' g.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => g.norm_coe_le_norm t)
  simpa only [mul_comm] using hi

theorem norm_weightedContinuousMap_integral_le (hω : Integrable ω μ) (g : C(K, ℂ)) :
    ‖∫ t, ω t * g t ∂μ‖ ≤ (∫ t, ‖ω t‖ ∂μ) * ‖g‖ := by
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_mul_const]
  apply integral_mono_ae (integrable_weightedContinuousMap hω g).norm (hω.norm.mul_const ‖g‖)
  exact Filter.Eventually.of_forall fun t => by
    dsimp only
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm t) (norm_nonneg _)

def weightedIntegralLinearMap (hω : Integrable ω μ) : C(K, ℂ) →ₗ[ℂ] ℂ where
  toFun g := ∫ t, ω t * g t ∂μ
  map_add' f g := by
    simpa only [ContinuousMap.add_apply, mul_add] using
      integral_add (integrable_weightedContinuousMap hω f) (integrable_weightedContinuousMap hω g)
  map_smul' a g := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [← mul_assoc (ω _) a, mul_comm (ω _) a, mul_assoc]
    exact integral_const_mul a _

def weightedIntegralCLM (hω : Integrable ω μ) : C(K, ℂ) →L[ℂ] ℂ :=
  (weightedIntegralLinearMap hω).mkContinuous (∫ t, ‖ω t‖ ∂μ)
    (norm_weightedContinuousMap_integral_le hω)

theorem weightedIntegralCLM_apply (hω : Integrable ω μ) (g : C(K, ℂ)) :
    weightedIntegralCLM hω g = ∫ t, ω t * g t ∂μ := rfl

/-- The weighted integral is holomorphic under scalar fiber holomorphy and
joint compact-family continuity. Complex and signed weights are allowed. -/
theorem analyticAt_weighted_holomorphicIntegral
    {f : ℂ → C(K, ℂ)} {c : ℂ} {R : ℝ≥0} (hR : 0 < R)
    (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ t : K, DifferentiableOn ℂ (fun z => f z t) (ball c R))
    (hω : Integrable ω μ) {z : ℂ} (hz : z ∈ ball c (R : ℝ)) :
    AnalyticAt ℂ (fun w => ∫ t, ω t * f w t ∂μ) z := by
  have ha := (hasFPowerSeriesOnBall_continuousFamily hR hc hd).analyticAt_of_mem
    (by simpa only [Metric.emetric_ball_nnreal] using hz)
  exact (weightedIntegralCLM hω).analyticAt _ |>.comp ha

/-- Every order of complex parameter differentiation passes under the weighted
integral; the derivative input is integrable as a consequence of the hypotheses. -/
theorem iteratedFDeriv_weighted_holomorphicIntegral
    {f : ℂ → C(K, ℂ)} {c : ℂ} {R : ℝ≥0} (hR : 0 < R)
    (hc : ContinuousOn f (closedBall c R))
    (hd : ∀ t : K, DifferentiableOn ℂ (fun z => f z t) (ball c R))
    (hω : Integrable ω μ) {z : ℂ} (hz : z ∈ ball c (R : ℝ))
    (n : ℕ) (v : Fin n → ℂ) :
    Integrable (fun t => ω t * iteratedFDeriv ℂ n (fun w => f w t) z v) μ ∧
    iteratedFDeriv ℂ n (fun w => ∫ t, ω t * f w t ∂μ) z v =
      ∫ t, ω t * iteratedFDeriv ℂ n (fun w => f w t) z v ∂μ := by
  have ha := (hasFPowerSeriesOnBall_continuousFamily hR hc hd).analyticAt_of_mem
    (by simpa only [Metric.emetric_ball_nnreal] using hz)
  have ht (t : K) : iteratedFDeriv ℂ n (fun w => f w t) z v =
      iteratedFDeriv ℂ n f z v t := by
    have he := (ContinuousMap.evalCLM ℂ t).iteratedFDeriv_comp_left
      (ha.contDiffAt : ContDiffAt ℂ (n : WithTop ℕ∞) f z) (le_refl (n : WithTop ℕ∞))
    exact congrArg (fun p : ℂ[×n]→L[ℂ] ℂ => p v) he
  have hi := (weightedIntegralCLM hω).iteratedFDeriv_comp_left
    (ha.contDiffAt : ContDiffAt ℂ (n : WithTop ℕ∞) f z) (le_refl (n : WithTop ℕ∞))
  constructor
  · simpa only [ht] using integrable_weightedContinuousMap hω (iteratedFDeriv ℂ n f z v)
  · simpa only [ht] using congrArg (fun p : ℂ[×n]→L[ℂ] ℂ => p v) hi

end Weighted

end LeanVerification.HolomorphicCompactFamily
