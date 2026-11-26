import LeanVerification.ZeroOrientation
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A one-sign-change convolution has positively oriented zeros

This is the abstract convolution argument in the weighted-width theorem.
The input has weak negative sign before a transition and weak positive sign
after it, up to null sets. The positive kernel has strictly decreasing
logarithmic derivative. Integrability and differentiation under the integral
are explicit hypotheses. The physical weighted-width representation and the
endpoint estimates of its particular kernel are not proved in this module.
-/

noncomputable section

namespace LeanVerification.Convolution

open MeasureTheory Set Filter
open scoped Topology

def leftConvolution (f K : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Iio x, f y * K (x - y)

def leftConvolutionSlope (f K : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y in Iio x, f y * deriv K (x - y)

def kernelLogDerivative (K : ℝ → ℝ) (σ : ℝ) : ℝ := deriv K σ / K σ

/-- Weak sign blocks, with the transition point itself unrestricted. -/
def NegativePositiveOn (f : ℝ → ℝ) (c : ℝ) (s : Set ℝ) : Prop :=
  ∀ᵐ y ∂volume.restrict s, (y < c → f y ≤ 0) ∧ (c < y → 0 ≤ f y)

theorem hasDerivAt_log_kernel {K : ℝ → ℝ} {σ : ℝ}
    (hK : 0 < K σ) (hd : DifferentiableAt ℝ K σ) :
    HasDerivAt (fun t => Real.log (K t)) (kernelLogDerivative K σ) σ := by
  exact hd.hasDerivAt.log (ne_of_gt hK)

private theorem positive_integral_of_ae_nonnegative_nonzero
    {f : ℝ → ℝ} {μ : Measure ℝ}
    (hi : Integrable f μ) (hn : 0 ≤ᵐ[μ] f) (hz : ¬f =ᵐ[μ] 0) :
    0 < ∫ y, f y ∂μ := by
  have hne : (∫ y, f y ∂μ) ≠ 0 := by
    intro he
    exact hz ((integral_eq_zero_iff_of_nonneg_ae hn hi).mp he)
  exact lt_of_le_of_ne (integral_nonneg_of_ae hn) hne.symm

/-- A nonzero nonnegative input has a strictly positive convolution. -/
theorem leftConvolution_pos_of_nonnegative_input {f K : ℝ → ℝ} {x : ℝ}
    (hK : ∀ σ ∈ Ioi 0, 0 < K σ)
    (hi : IntegrableOn (fun y => f y * K (x - y)) (Iio x))
    (hn : 0 ≤ᵐ[volume.restrict (Iio x)] f)
    (hz : ¬f =ᵐ[volume.restrict (Iio x)] 0) :
    0 < leftConvolution f K x := by
  apply positive_integral_of_ae_nonnegative_nonzero hi
  · filter_upwards [hn, ae_restrict_mem measurableSet_Iio] with y hy hyx
    exact mul_nonneg hy (hK (x - y) (show 0 < x - y from sub_pos.mpr hyx)).le
  · intro he
    apply hz
    filter_upwards [he, ae_restrict_mem measurableSet_Iio] with y hy hyx
    exact (mul_eq_zero.mp hy).resolve_right (ne_of_gt (hK (x - y) (show 0 < x - y from sub_pos.mpr hyx)))

/-- Before the transition, a nonzero truncated input gives a negative value. -/
theorem leftConvolution_neg_before_transition {f K : ℝ → ℝ} {x c : ℝ}
    (hxc : x ≤ c) (hK : ∀ σ ∈ Ioi 0, 0 < K σ)
    (hi : IntegrableOn (fun y => f y * K (x - y)) (Iio x))
    (hs : NegativePositiveOn f c (Iio x))
    (hz : ¬f =ᵐ[volume.restrict (Iio x)] 0) :
    leftConvolution f K x < 0 := by
  have hn : 0 ≤ᵐ[volume.restrict (Iio x)] (fun y => -f y) := by
    filter_upwards [hs, ae_restrict_mem measurableSet_Iio] with y hy hyx
    exact neg_nonneg.mpr (hy.1 (hyx.trans_le hxc))
  have hnz : ¬(fun y => -f y) =ᵐ[volume.restrict (Iio x)] 0 := by
    intro he
    apply hz
    exact he.mono fun y hy => neg_eq_zero.mp hy
  have hni : IntegrableOn (fun y => (-f y) * K (x - y)) (Iio x) := by
    simpa only [neg_mul] using hi.neg
  have hp := leftConvolution_pos_of_nonnegative_input hK hni hn hnz
  simpa only [leftConvolution, neg_mul, integral_neg, neg_pos] using hp

/-- At a zero after the sign transition, the derivative integral is positive.
The proof subtracts the transition logarithmic derivative times the zero
integral; strictness comes from the nonzero input, not from an extra integral
positivity hypothesis. -/
theorem leftConvolutionSlope_pos_at_zero {f K : ℝ → ℝ} {x c : ℝ}
    (hxc : c < x) (hK : ∀ σ ∈ Ioi 0, 0 < K σ)
    (hlog : StrictAntiOn (kernelLogDerivative K) (Ioi 0))
    (hi : IntegrableOn (fun y => f y * K (x - y)) (Iio x))
    (hdi : IntegrableOn (fun y => f y * deriv K (x - y)) (Iio x))
    (hs : NegativePositiveOn f c (Iio x))
    (hnz : ¬f =ᵐ[volume.restrict (Iio x)] 0)
    (hz : leftConvolution f K x = 0) :
    0 < leftConvolutionSlope f K x := by
  classical
  let L := kernelLogDerivative K (x - c)
  let R := fun y => f y * deriv K (x - y) - L * (f y * K (x - y))
  have hiR : Integrable R (volume.restrict (Iio x)) := hdi.sub (hi.const_mul L)
  have hformula : ∀ y < x, R y = f y * K (x - y) *
      (kernelLogDerivative K (x - y) - kernelLogDerivative K (x - c)) := by
    intro y hy
    have hk : K (x - y) ≠ 0 := ne_of_gt (hK (x - y) (sub_pos.mpr hy))
    have hcancel : K (x - y) * kernelLogDerivative K (x - y) = deriv K (x - y) := by
      unfold kernelLogDerivative
      exact mul_div_cancel₀ _ hk
    dsimp only [R, L]
    rw [mul_sub, mul_assoc (f y) (K (x - y)) (kernelLogDerivative K (x - y)), hcancel]
    ring
  have hnR : 0 ≤ᵐ[volume.restrict (Iio x)] R := by
    filter_upwards [hs, ae_restrict_mem measurableSet_Iio] with y hy hyx
    rw [hformula y hyx]
    rcases lt_trichotomy y c with hyc | rfl | hcy
    · have hlt := hlog (sub_pos.mpr hxc) (show 0 < x - y from sub_pos.mpr hyx) (by linarith : x - c < x - y)
      exact mul_nonneg_of_nonpos_of_nonpos
        (mul_nonpos_of_nonpos_of_nonneg (hy.1 hyc) (hK _ (show 0 < x - y from sub_pos.mpr hyx)).le)
        (sub_nonpos.mpr hlt.le)
    · simp
    · have hlt := hlog (show 0 < x - y from sub_pos.mpr hyx) (sub_pos.mpr hxc) (by linarith : x - y < x - c)
      exact mul_nonneg
        (mul_nonneg (hy.2 hcy) (hK _ (show 0 < x - y from sub_pos.mpr hyx)).le)
        (sub_nonneg.mpr hlt.le)
  have hnzR : ¬R =ᵐ[volume.restrict (Iio x)] 0 := by
    intro he
    apply hnz
    have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ c := by simp [ae_iff]
    filter_upwards [he, ae_restrict_mem measurableSet_Iio, ae_restrict_of_ae hne]
      with y hy hyx hyc
    rw [hformula y hyx] at hy
    have hdiff : kernelLogDerivative K (x - y) - kernelLogDerivative K (x - c) ≠ 0 := by
      intro heq
      have heq' := hlog.injOn (show 0 < x - y from sub_pos.mpr hyx) (sub_pos.mpr hxc) (sub_eq_zero.mp heq)
      apply hyc
      linarith
    have hprod := (mul_eq_zero.mp hy).resolve_right hdiff
    exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt (hK _ (show 0 < x - y from sub_pos.mpr hyx)))
  have hpositive := positive_integral_of_ae_nonnegative_nonzero hiR hnR hnzR
  have hint : (∫ y, R y ∂volume.restrict (Iio x)) = leftConvolutionSlope f K x := by
    rw [show R = (fun y => f y * deriv K (x - y) - L * (f y * K (x - y))) from rfl,
      integral_sub hdi (hi.const_mul L), integral_const_mul]
    change leftConvolutionSlope f K x - L * leftConvolution f K x = leftConvolutionSlope f K x
    rw [hz, mul_zero, sub_zero]
  rwa [hint] at hpositive

/-- The derivative-under-integral premise is explicit and concerns the
actual defined convolution, not an arbitrary function with an assumed sign. -/
theorem deriv_leftConvolution_pos_at_zero {f K : ℝ → ℝ} {x c : ℝ}
    (hxc : c < x) (hK : ∀ σ ∈ Ioi 0, 0 < K σ)
    (hlog : StrictAntiOn (kernelLogDerivative K) (Ioi 0))
    (hi : IntegrableOn (fun y => f y * K (x - y)) (Iio x))
    (hdi : IntegrableOn (fun y => f y * deriv K (x - y)) (Iio x))
    (hs : NegativePositiveOn f c (Iio x))
    (hnz : ¬f =ᵐ[volume.restrict (Iio x)] 0)
    (hd : HasDerivAt (leftConvolution f K) (leftConvolutionSlope f K x) x)
    (hz : leftConvolution f K x = 0) :
    0 < deriv (leftConvolution f K) x := by
  rw [hd.deriv]
  exact leftConvolutionSlope_pos_at_zero hxc hK hlog hi hdi hs hnz hz

/-- The complete abstract one-zero conclusion on a left-unbounded interval.
The nonzero-on-every-initial-interval hypothesis rules out an initial zero
plateau; in the manuscript that property is supplied by analytic nonzero input.
All integrability and differentiation hypotheses still require verification
for the physical weighted-width kernel. -/
theorem atMostOneZeroOn_leftConvolution_of_ratio_antitone {f K : ℝ → ℝ} {c b : ℝ}
    (hK : ∀ σ ∈ Ioi 0, 0 < K σ)
    (hlog : StrictAntiOn (kernelLogDerivative K) (Ioi 0))
    (hs : NegativePositiveOn f c (Iio b))
    (hi : ∀ x < b, IntegrableOn (fun y => f y * K (x - y)) (Iio x))
    (hdi : ∀ x < b, IntegrableOn (fun y => f y * deriv K (x - y)) (Iio x))
    (hnz : ∀ x < b, ¬f =ᵐ[volume.restrict (Iio x)] 0)
    (hd : ∀ x < b, HasDerivAt (leftConvolution f K) (leftConvolutionSlope f K x) x) :
    ZeroCounting.AtMostOneZeroOn (leftConvolution f K) (Iio b) ∧
      ∀ x < b, leftConvolution f K x = 0 → 0 < deriv (leftConvolution f K) x := by
  classical
  have hzero : ∀ x ∈ Iio b, leftConvolution f K x = 0 →
      0 < deriv (leftConvolution f K) x := by
    intro x hx hz
    have hsx : NegativePositiveOn f c (Iio x) :=
      ae_restrict_of_ae_restrict_of_subset (Iio_subset_Iio hx.le) hs
    have hxc : c < x := by
      by_contra hn
      exact (ne_of_lt (leftConvolution_neg_before_transition (le_of_not_gt hn)
        hK (hi x hx) hsx (hnz x hx))) hz
    exact deriv_leftConvolution_pos_at_zero hxc hK hlog (hi x hx) (hdi x hx)
      hsx (hnz x hx) (hd x hx) hz
  exact ⟨ZeroOrientation.atMostOneZeroOn_of_deriv_pos_at_zeros (convex_Iio b)
    (fun x hx => (hd x hx).differentiableAt) hzero, hzero⟩

/-- The same conclusion stated using the actual derivative of `log K`.
Kernel differentiability makes the logarithmic-derivative hypothesis literal.
This theorem is the abstract analytic step of the manuscript's weighted-width
zero-transfer argument; it does not supply that integral representation. -/
theorem atMostOneZeroOn_leftConvolution {f K : ℝ → ℝ} {c b : ℝ}
    (hK : ∀ σ ∈ Ioi 0, 0 < K σ)
    (hKd : DifferentiableOn ℝ K (Ioi 0))
    (hlog : StrictAntiOn (deriv (fun σ => Real.log (K σ))) (Ioi 0))
    (hs : NegativePositiveOn f c (Iio b))
    (hi : ∀ x < b, IntegrableOn (fun y => f y * K (x - y)) (Iio x))
    (hdi : ∀ x < b, IntegrableOn (fun y => f y * deriv K (x - y)) (Iio x))
    (hnz : ∀ x < b, ¬f =ᵐ[volume.restrict (Iio x)] 0)
    (hd : ∀ x < b, HasDerivAt (leftConvolution f K) (leftConvolutionSlope f K x) x) :
    ZeroCounting.AtMostOneZeroOn (leftConvolution f K) (Iio b) ∧
      ∀ x < b, leftConvolution f K x = 0 → 0 < deriv (leftConvolution f K) x := by
  have hratio : StrictAntiOn (kernelLogDerivative K) (Ioi 0) := by
    intro a ha d hd had
    rw [← (hasDerivAt_log_kernel (hK d hd)
      ((hKd d hd).differentiableAt (isOpen_Ioi.mem_nhds hd))).deriv,
      ← (hasDerivAt_log_kernel (hK a ha)
      ((hKd a ha).differentiableAt (isOpen_Ioi.mem_nhds ha))).deriv]
    exact hlog ha hd had
  exact atMostOneZeroOn_leftConvolution_of_ratio_antitone hK hratio hs hi hdi hnz hd

end LeanVerification.Convolution
