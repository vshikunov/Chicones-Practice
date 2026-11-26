import LeanVerification.CauchyDifferentiation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology BigOperators

namespace LeanVerification.Cauchy

def complexKernel (f : ℝ → ℝ) (β : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (f t : ℂ) * (z + (t : ℂ)) ^ ((-β : ℝ) : ℂ)

def complexTransform (μ : Measure ℝ) (f : ℝ → ℝ) (β : ℝ) (z : ℂ) : ℂ :=
  ∫ t, complexKernel f β z t ∂μ

theorem slitPlane_add_nonnegative {z : ℂ} (hz : z ∈ Complex.slitPlane)
    {t : ℝ} (ht : 0 ≤ t) : z + (t : ℂ) ∈ Complex.slitPlane := by
  rcases hz with hz | hz
  · left
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  · right
    simpa only [Complex.add_im, Complex.ofReal_im, add_zero] using hz

/-- A genuine common kernel bound on a neighborhood of every point of the
entire slit plane, including points with negative real part. -/
theorem exists_slit_kernel_lower_bound {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ ball z ε, ∀ t : ℝ, 0 ≤ t →
        x + (t : ℂ) ∈ Complex.slitPlane ∧ c * (1 + t) ≤ ‖x + (t : ℂ)‖ := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Complex.isOpen_slitPlane.mem_nhds hz)
  let a := r / 2
  let B := 1 + ‖z‖ + a
  let c := a / (a + B)
  have ha : 0 < a := by dsimp [a]; linarith
  have hB : 0 < B := by dsimp [B]; positivity
  have hc : 0 < c := div_pos ha (add_pos ha hB)
  refine ⟨a, ha, c, hc, ?_⟩
  intro x hx t ht
  have hxnorm : ‖x - z‖ < a := by simpa only [mem_ball_iff_norm] using hx
  have hxa : x ∈ ball z r := by
    rw [mem_ball_iff_norm]
    dsimp [a] at hxnorm
    linarith
  refine ⟨slitPlane_add_nonnegative (hball hxa) ht, ?_⟩
  have hzt : r ≤ ‖z + (t : ℂ)‖ := by
    by_contra hn
    have hh : -(t : ℂ) ∈ ball z r := by
      rw [mem_ball_iff_norm]
      have he : -(t : ℂ) - z = -(z + (t : ℂ)) := by ring
      rw [he, norm_neg]
      exact lt_of_not_ge hn
    have hneg := hball hh
    rw [Complex.neg_ofReal_mem_slitPlane] at hneg
    exact (not_lt_of_ge ht) hneg
  have hdist : ‖z - x‖ < a := by rwa [norm_sub_rev]
  have htri : ‖z + (t : ℂ)‖ ≤ ‖x + (t : ℂ)‖ + ‖z - x‖ := by
    have he : z + (t : ℂ) = (x + (t : ℂ)) + (z - x) := by ring
    rw [he]
    exact norm_add_le _ _
  have hlow : a ≤ ‖x + (t : ℂ)‖ := by
    dsimp [a] at *
    linarith
  have hxn : ‖x‖ ≤ ‖z‖ + a := by
    have hh : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
      simpa only [sub_add_cancel] using norm_add_le (x - z) z
    linarith
  have htn : t ≤ ‖x + (t : ℂ)‖ + ‖x‖ := by
    have hh := norm_sub_le (x + (t : ℂ)) x
    simpa only [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg ht] using hh
  have hsum : 1 + t ≤ ‖x + (t : ℂ)‖ + B := by dsimp [B]; linarith
  dsimp [c]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (add_pos ha hB)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsum ha.le,
    mul_le_mul_of_nonneg_left hlow hB.le]

theorem measurable_complexKernel {f : ℝ → ℝ} (hf : Measurable f) (β : ℝ) (z : ℂ) :
    Measurable (complexKernel f β z) := by
  have hm : Measurable (fun t : ℝ => z + (t : ℂ)) :=
    measurable_const.add Complex.continuous_ofReal.measurable
  have hp : Measurable (fun t : ℝ => (z + (t : ℂ)) ^ ((-β : ℝ) : ℂ)) := by
    simp only [Complex.cpow_def]
    apply Measurable.ite (measurableSet_eq_fun hm measurable_const) measurable_const
    exact ((Complex.measurable_log.comp hm).mul_const _).cexp
  exact (Complex.continuous_ofReal.measurable.comp hf).mul hp

theorem norm_complexKernel (f : ℝ → ℝ) (β : ℝ) (z : ℂ) (t : ℝ) :
    ‖complexKernel f β z t‖ = ‖f t‖ * ‖z + (t : ℂ)‖ ^ (-β) := by
  rw [complexKernel, norm_mul, Complex.norm_real, Complex.norm_cpow_real]

theorem complexKernel_bound {f : ℝ → ℝ} {β c t : ℝ} {z : ℂ}
    (hβ : 0 ≤ β) (hc : 0 < c) (ht : 0 ≤ t)
    (hb : c * (1 + t) ≤ ‖z + (t : ℂ)‖) :
    ‖complexKernel f β z t‖ ≤ c ^ (-β) * ‖f t * (1 + t) ^ (-β)‖ := by
  have hp : 0 < 1 + t := by linarith
  rw [norm_complexKernel]
  have hk := Real.rpow_le_rpow_of_nonpos (mul_pos hc hp) hb (neg_nonpos.mpr hβ)
  rw [Real.mul_rpow hc.le hp.le] at hk
  rw [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
  calc
    _ ≤ ‖f t‖ * (c ^ (-β) * (1 + t) ^ (-β)) :=
      mul_le_mul_of_nonneg_left hk (norm_nonneg _)
    _ = _ := by ring

theorem weighted_norm_mono {f : ℝ → ℝ} {β γ t : ℝ}
    (hβγ : β ≤ γ) (ht : 0 ≤ t) :
    ‖f t * (1 + t) ^ (-γ)‖ ≤ ‖f t * (1 + t) ^ (-β)‖ := by
  have hp : 0 ≤ 1 + t := by linarith
  simp only [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg hp _)]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (neg_le_neg hβγ)

theorem integrable_weighted_mono {μ : Measure ℝ} {f : ℝ → ℝ} {β γ : ℝ}
    (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) (hβγ : β ≤ γ)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    Integrable (fun t => f t * (1 + t) ^ (-γ)) μ := by
  apply hint.norm.mono' (hf.mul ((measurable_const.add measurable_id).pow_const _)).aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  exact weighted_norm_mono hβγ ht

theorem integrable_complexTransform {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ} {z : ℂ}
    (hβ : 0 ≤ β) (hz : z ∈ Complex.slitPlane) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    Integrable (complexKernel f β z) μ := by
  obtain ⟨ε, hε, c, hc, hb⟩ := exists_slit_kernel_lower_bound hz
  apply (hint.norm.const_mul (c ^ (-β))).mono' (measurable_complexKernel hf β z).aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  exact complexKernel_bound hβ hc ht (hb z (mem_ball_self hε) t ht).2

theorem hasDerivAt_complexKernel (f : ℝ → ℝ) (β : ℝ) {z : ℂ} {t : ℝ}
    (hz : z + (t : ℂ) ∈ Complex.slitPlane) :
    HasDerivAt (fun x => complexKernel f β x t)
      (((-β : ℝ) : ℂ) * complexKernel f (β + 1) z t) z := by
  have hd := (((hasDerivAt_id z).add_const (t : ℂ)).cpow_const
    (c := ((-β : ℝ) : ℂ)) hz).const_mul (f t : ℂ)
  convert hd using 1
  simp only [complexKernel, id_eq, mul_one]
  have he : ((-(β + 1) : ℝ) : ℂ) = ((-β : ℝ) : ℂ) - 1 := by push_cast; ring
  rw [he]
  ring

/-- Holomorphic differentiation follows on the full cut plane from the
original weighted absolute mass, with no extra decay hypothesis. -/
theorem hasDerivAt_complexTransform {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ} {z : ℂ}
    (hβ : 0 < β) (hz : z ∈ Complex.slitPlane) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    HasDerivAt (complexTransform μ f β)
      (((-β : ℝ) : ℂ) * complexTransform μ f (β + 1) z) z := by
  obtain ⟨ε, hε, c, hc, hb⟩ := exists_slit_kernel_lower_bound hz
  have hmeas : ∀ᶠ x : ℂ in 𝓝 z, AEStronglyMeasurable (complexKernel f β x) μ :=
    Eventually.of_forall fun x => (measurable_complexKernel hf β x).aestronglyMeasurable
  have hdm : AEStronglyMeasurable
      (fun t => (((-β : ℝ) : ℂ) * complexKernel f (β + 1) z t)) μ :=
    ((measurable_complexKernel hf (β + 1) z).const_mul _).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ x ∈ ball z ε,
      ‖(((-β : ℝ) : ℂ) * complexKernel f (β + 1) x t)‖ ≤
        (β * c ^ (-(β + 1))) * ‖f t * (1 + t) ^ (-β)‖ := by
    filter_upwards [hsupp] with t ht
    intro x hx
    rw [norm_mul, Complex.norm_real, norm_neg, Real.norm_of_nonneg hβ.le]
    have hk := complexKernel_bound (f := f) (by linarith : 0 ≤ β + 1) hc ht (hb x hx t ht).2
    have hw := weighted_norm_mono (f := f) (β := β) (γ := β + 1) (by linarith) ht
    calc
      _ ≤ β * (c ^ (-(β + 1)) * ‖f t * (1 + t) ^ (-(β + 1))‖) :=
        mul_le_mul_of_nonneg_left hk hβ.le
      _ ≤ β * (c ^ (-(β + 1)) * ‖f t * (1 + t) ^ (-β)‖) := by
        gcongr
      _ = _ := by ring
  have hd : ∀ᵐ t ∂μ, ∀ x ∈ ball z ε,
      HasDerivAt (fun x => complexKernel f β x t)
        (((-β : ℝ) : ℂ) * complexKernel f (β + 1) x t) x := by
    filter_upwards [hsupp] with t ht
    intro x hx
    exact hasDerivAt_complexKernel f β (hb x hx t ht).1
  have he := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hmeas
    (integrable_complexTransform hβ.le hz hf hsupp hint) hdm hbound
    (hint.norm.const_mul (β * c ^ (-(β + 1)))) hd).2
  simpa only [complexTransform, integral_const_mul] using he

theorem differentiableOn_complexTransform {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ}
    (hβ : 0 < β) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    DifferentiableOn ℂ (complexTransform μ f β) Complex.slitPlane := by
  intro z hz
  exact (hasDerivAt_complexTransform hβ hz hf hsupp hint).differentiableAt.differentiableWithinAt

theorem analyticAt_complexTransform {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ} {z : ℂ}
    (hβ : 0 < β) (hz : z ∈ Complex.slitPlane) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    AnalyticAt ℂ (complexTransform μ f β) z :=
  (differentiableOn_complexTransform hβ hf hsupp hint).analyticAt
    (Complex.isOpen_slitPlane.mem_nhds hz)

def risingFactor (β : ℝ) (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, (β + (j : ℝ))

theorem risingFactor_succ (β : ℝ) (k : ℕ) :
    risingFactor β (k + 1) = risingFactor β k * (β + (k : ℝ)) := by
  exact Finset.prod_range_succ _ _

/-- Every fixed complex derivative is the stated higher Cauchy integral,
with the exact rising-factorial coefficient. -/
theorem iteratedDeriv_complexTransform {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ}
    (hβ : 0 < β) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) (k : ℕ) :
    ∀ z ∈ Complex.slitPlane,
      iteratedDeriv k (complexTransform μ f β) z =
        (-1 : ℂ) ^ k * (risingFactor β k : ℂ) * complexTransform μ f (β + k) z := by
  induction k with
  | zero =>
      intro z hz
      simp [risingFactor]
  | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv k (complexTransform μ f β) =ᶠ[𝓝 z]
          fun w => (-1 : ℂ) ^ k * (risingFactor β k : ℂ) * complexTransform μ f (β + k) w := by
        filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
        exact ih w hw
      rw [he.deriv_eq]
      have hkn : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      have hki := integrable_weighted_mono hf hsupp
        (show β ≤ β + k by linarith) hint
      have hd := (hasDerivAt_complexTransform (by linarith : 0 < β + k) hz hf hsupp hki).const_mul
        ((-1 : ℂ) ^ k * (risingFactor β k : ℂ))
      rw [hd.deriv, risingFactor_succ, pow_succ]
      have hx : β + (k : ℝ) + 1 = β + ((k + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hx]
      push_cast
      ring

theorem complexTransform_ofReal {μ : Measure ℝ} {f : ℝ → ℝ} {β δ : ℝ}
    (hδ : 0 < δ) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t) :
    complexTransform μ f β (δ : ℂ) = (transform μ f β δ : ℂ) := by
  unfold complexTransform transform
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hsupp] with t ht
  dsimp [complexKernel]
  rw [← Complex.ofReal_add, ← Complex.ofReal_cpow (by linarith : 0 ≤ δ + t)]
  exact (Complex.ofReal_mul _ _).symm

theorem analyticAt_transform {μ : Measure ℝ} {f : ℝ → ℝ} {β δ : ℝ}
    (hβ : 0 < β) (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    AnalyticAt ℝ (transform μ f β) δ := by
  have ha := (analyticAt_complexTransform hβ (Complex.ofReal_mem_slitPlane.mpr hδ)
    hf hsupp hint).re_ofReal
  apply ha.congr
  filter_upwards [Ioi_mem_nhds hδ] with x hx
  rw [complexTransform_ofReal hx hsupp, Complex.ofReal_re]

end LeanVerification.Cauchy
