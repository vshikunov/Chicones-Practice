import LeanVerification.StieltjesMoments
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open MeasureTheory Set Filter Complex Metric
open scoped Topology

namespace LeanVerification.Stieltjes

noncomputable section

/-- Holomorphic power kernel, agreeing with the real moment integrand on
the positive support of the measure. -/
def complexMomentKernel (f : ℝ → ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  (f t : ℂ) * Complex.exp ((-z - (3 : ℂ)/2) * (Real.log t : ℂ))

def complexMoment (μ : Measure ℝ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t, complexMomentKernel f z t ∂μ

theorem norm_complexMomentKernel (f : ℝ → ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖complexMomentKernel f z t‖ = ‖f t * t ^ (-z.re - (3 : ℝ)/2)‖ := by
  simp [complexMomentKernel, norm_mul, Complex.norm_exp,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
    Real.rpow_def_of_pos ht, mul_comm]

theorem measurable_complexMomentKernel {f : ℝ → ℝ} (hf : Measurable f) (z : ℂ) :
    Measurable (complexMomentKernel f z) := by
  exact (Complex.continuous_ofReal.measurable.comp hf).mul
    ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp
      Real.measurable_log)).cexp)

theorem hasDerivAt_complexMomentKernel (f : ℝ → ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => complexMomentKernel f w t)
      (-(Real.log t : ℂ) * complexMomentKernel f z t) z := by
  have hd := (((hasDerivAt_id z).neg.sub_const ((3 : ℂ)/2)).mul_const
    (Real.log t : ℂ)).cexp
  convert hd.const_mul (f t : ℂ) using 1
  simp [complexMomentKernel]
  ring

/-- An explicit logarithmic bound on a compact strip of positive exponents. -/
theorem log_rpow_uniform_bound {H t σ S r : ℝ} (hH : 0 < H) (ht : H ≤ t)
    (hσ : 0 < σ) (hr : σ ≤ r) (hrS : r ≤ S) :
    |Real.log t| * t ^ (-r) ≤
      1/σ + |Real.log H| * H ^ (-S) := by
  have hp : 0 < t := hH.trans_le ht
  rcases le_or_lt 1 t with ht1 | ht1
  · rw [abs_of_nonneg (Real.log_nonneg ht1)]
    have hb := Real.log_le_rpow_div hp.le hσ
    have ha : Real.log t * t ^ (-r) ≤ (t ^ σ / σ) * t ^ (-r) :=
      mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hp.le _)
    have he : (t ^ σ / σ) * t ^ (-r) = t ^ (σ-r) / σ := by
      rw [sub_eq_add_neg, Real.rpow_add hp]
      ring
    have hx : t ^ (σ-r) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_exponent_le ht1 (sub_nonpos.mpr hr)
    apply ha.trans
    rw [he]
    exact (div_le_div_of_nonneg_right hx hσ.le).trans
      (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hH.le _)))
  · have hH1 : H ≤ 1 := ht.trans ht1.le
    have hl : |Real.log t| ≤ |Real.log H| := by
      rw [abs_of_nonpos (Real.log_nonpos hp.le ht1.le),
        abs_of_nonpos (Real.log_nonpos hH.le hH1)]
      exact neg_le_neg (Real.log_le_log hH ht)
    have hpow : t ^ (-r) ≤ H ^ (-S) := by
      exact (Real.rpow_le_rpow_of_nonpos hH ht (neg_nonpos.mpr (hσ.le.trans hr))).trans
        (Real.rpow_le_rpow_of_exponent_ge hH hH1 (neg_le_neg hrS))
    exact (mul_le_mul hl hpow (Real.rpow_nonneg hp.le _) (abs_nonneg _)).trans
      (le_add_of_nonneg_left (one_div_nonneg.mpr hσ.le))

theorem integrable_complexMoment {μ : Measure ℝ} {H : ℝ} {f : ℝ → ℝ} {z : ℂ}
    (hH : 0 < H) (hz : 0 ≤ z.re) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ)/2)) μ) :
    Integrable (complexMomentKernel f z) μ := by
  apply (hint.norm.const_mul (H ^ (-z.re))).mono'
    (measurable_complexMomentKernel hf z).aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  rw [norm_complexMomentKernel f z (hH.trans_le ht)]
  exact moment_integrand_bound hH ht hz

theorem norm_complexMoment_derivative (f : ℝ → ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖-(Real.log t : ℂ) * complexMomentKernel f z t‖ =
      (|Real.log t| * t ^ (-z.re)) * ‖f t * t ^ (-(3 : ℝ)/2)‖ := by
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    norm_complexMomentKernel f z ht]
  rw [show -z.re - (3 : ℝ)/2 = -z.re + (-(3 : ℝ)/2) by ring,
    Real.rpow_add ht]
  rw [show f t * (t ^ (-z.re) * t ^ (-(3 : ℝ)/2)) =
    t ^ (-z.re) * (f t * t ^ (-(3 : ℝ)/2)) by ring,
    norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  ring

/-- Differentiation of the actual complex moment integral on the positive
half-plane, with the logarithmic majorant proved from the original weighted
absolute-integrability hypothesis. -/
theorem hasDerivAt_complexMoment {μ : Measure ℝ} {H : ℝ} {f : ℝ → ℝ} {z : ℂ}
    (hH : 0 < H) (hz : 0 < z.re) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ)/2)) μ) :
    Integrable (fun t => -(Real.log t : ℂ) * complexMomentKernel f z t) μ ∧
    HasDerivAt (complexMoment μ f)
      (∫ t, -(Real.log t : ℂ) * complexMomentKernel f z t ∂μ) z := by
  let ε : ℝ := z.re/2
  let S : ℝ := z.re + ε
  let C : ℝ := 1/ε + |Real.log H| * H ^ (-S)
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hb : ∀ x ∈ ball z ε, ε ≤ x.re ∧ x.re ≤ S := by
    intro x hx
    rw [mem_ball_iff_norm] at hx
    have hu := (Complex.re_le_norm (x-z)).trans hx.le
    have hl : (z-x).re ≤ ε := by
      exact (Complex.re_le_norm (z-x)).trans (by simpa only [norm_sub_rev] using hx.le)
    simp only [Complex.sub_re] at hu hl
    dsimp [ε, S] at *
    constructor <;> linarith
  have hmeas : ∀ᶠ x : ℂ in 𝓝 z, AEStronglyMeasurable (complexMomentKernel f x) μ :=
    Eventually.of_forall fun x => (measurable_complexMomentKernel hf x).aestronglyMeasurable
  have hdm : AEStronglyMeasurable
      (fun t => -(Real.log t : ℂ) * complexMomentKernel f z t) μ :=
    ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg.mul
      (measurable_complexMomentKernel hf z)).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ x ∈ ball z ε,
      ‖-(Real.log t : ℂ) * complexMomentKernel f x t‖ ≤
        C * ‖f t * t ^ (-(3 : ℝ)/2)‖ := by
    filter_upwards [hsupp] with t ht
    intro x hx
    rw [norm_complexMoment_derivative f x (hH.trans_le ht)]
    exact mul_le_mul_of_nonneg_right
      (log_rpow_uniform_bound hH ht hε (hb x hx).1 (hb x hx).2) (norm_nonneg _)
  have hd : ∀ᵐ t ∂μ, ∀ x ∈ ball z ε,
      HasDerivAt (fun x => complexMomentKernel f x t)
        (-(Real.log t : ℂ) * complexMomentKernel f x t) x := by
    exact Eventually.of_forall fun t x _ => hasDerivAt_complexMomentKernel f x t
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hmeas
    (integrable_complexMoment hH hz.le hf hsupp hint) hdm hbound
    (hint.norm.const_mul C) hd

theorem differentiableOn_complexMoment {μ : Measure ℝ} {H : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ)/2)) μ) :
    DifferentiableOn ℂ (complexMoment μ f) {z : ℂ | 0 < z.re} := by
  intro z hz
  exact (hasDerivAt_complexMoment hH hz hf hsupp hint).2.differentiableAt.differentiableWithinAt

theorem analyticAt_complexMoment {μ : Measure ℝ} {H : ℝ} {f : ℝ → ℝ} {z : ℂ}
    (hH : 0 < H) (hz : 0 < z.re) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ)/2)) μ) :
    AnalyticAt ℂ (complexMoment μ f) z := by
  apply (differentiableOn_complexMoment hH hf hsupp hint).analyticAt
  exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz

theorem complexMoment_ofReal {μ : Measure ℝ} {H r : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hsupp : ∀ᵐ t ∂μ, H ≤ t) :
    complexMoment μ f (r : ℂ) = (weightedMoment μ f r : ℂ) := by
  unfold complexMoment weightedMoment
  rw [← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [hsupp] with t ht
  have hp : 0 < t := hH.trans_le ht
  simp [complexMomentKernel, Real.rpow_def_of_pos hp, Complex.ofReal_exp,
    mul_comm]

theorem analyticAt_weightedMoment {μ : Measure ℝ} {H r : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hr : 0 < r) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ)/2)) μ) :
    AnalyticAt ℝ (weightedMoment μ f) r := by
  have ha := (analyticAt_complexMoment (z := (r : ℂ)) hH (by simpa using hr)
    hf hsupp hint).re_ofReal
  simpa only [complexMoment_ofReal hH hsupp, Complex.ofReal_re] using ha

theorem analyticAt_normalizedMoment {μ : Measure ℝ} {H r : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hr : 0 < r) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ)/2)) μ) :
    AnalyticAt ℝ (normalizedMoment μ f) r := by
  have hc : AnalyticAt ℝ (fun _ : ℝ => Real.pi⁻¹) r := analyticAt_const
  simpa only [normalizedMoment, div_eq_mul_inv] using
    (analyticAt_weightedMoment hH hr hf hsupp hint).mul hc

/-- Every fixed logarithmic power is absorbed by a strictly positive power
at infinity; the lower support cutoff also controls the logarithm near zero. -/
theorem exists_log_pow_rpow_bound {H σ : ℝ} (hH : 0 < H) (hσ : 0 < σ)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, H ≤ t → |Real.log t| ^ k * t ^ (-σ) ≤ C := by
  induction k generalizing σ with
  | zero =>
      refine ⟨H ^ (-σ), Real.rpow_nonneg hH.le _, ?_⟩
      intro t ht
      simpa only [pow_zero, one_mul] using
        Real.rpow_le_rpow_of_nonpos hH ht (neg_nonpos.mpr hσ.le)
  | succ k ih =>
      have hh : 0 < σ / 2 := half_pos hσ
      obtain ⟨C, hC, hbound⟩ := ih hh
      let B : ℝ := 1 / (σ / 2) + |Real.log H| * H ^ (-(σ / 2))
      have hB : 0 ≤ B := by positivity
      refine ⟨C * B, mul_nonneg hC hB, ?_⟩
      intro t ht
      have hp : 0 < t := hH.trans_le ht
      have hb := log_rpow_uniform_bound hH ht hh (le_refl (σ / 2)) (le_refl (σ / 2))
      have he : |Real.log t| ^ (k + 1) * t ^ (-σ) =
          (|Real.log t| ^ k * t ^ (-(σ / 2))) *
            (|Real.log t| * t ^ (-(σ / 2))) := by
        rw [show -σ = -(σ / 2) + -(σ / 2) by ring, Real.rpow_add hp, pow_succ]
        ring
      rw [he]
      exact mul_le_mul (hbound t ht) hb
        (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hp.le _)) hC

theorem exists_log_pow_strip_bound {H σ S : ℝ} (hH : 0 < H) (hσ : 0 < σ)
    (hσS : σ ≤ S) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t r : ℝ, H ≤ t → σ ≤ r → r ≤ S →
      |Real.log t| ^ k * t ^ (-r) ≤ C := by
  obtain ⟨A, hA, ha⟩ := exists_log_pow_rpow_bound hH hσ k
  obtain ⟨B, hB, hb⟩ := exists_log_pow_rpow_bound hH (hσ.trans_le hσS) k
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro t r ht hsr hrs
  have hp : 0 < t := hH.trans_le ht
  have hpw : t ^ (-r) ≤ t ^ (-σ) + t ^ (-S) := by
    rcases le_or_lt 1 t with ht1 | ht1
    · exact (Real.rpow_le_rpow_of_exponent_le ht1 (neg_le_neg hsr)).trans
        (le_add_of_nonneg_right (Real.rpow_nonneg hp.le _))
    · exact (Real.rpow_le_rpow_of_exponent_ge hp ht1.le (neg_le_neg hrs)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg hp.le _))
  calc
    |Real.log t| ^ k * t ^ (-r) ≤
        |Real.log t| ^ k * (t ^ (-σ) + t ^ (-S)) :=
      mul_le_mul_of_nonneg_left hpw (pow_nonneg (abs_nonneg _) k)
    _ = |Real.log t| ^ k * t ^ (-σ) + |Real.log t| ^ k * t ^ (-S) := by ring
    _ ≤ A + B := add_le_add (ha t ht) (hb t ht)

def complexMomentJetKernel (f : ℝ → ℝ) (k : ℕ) (z : ℂ) (t : ℝ) : ℂ :=
  (-(Real.log t : ℂ)) ^ k * complexMomentKernel f z t

def complexMomentJet (μ : Measure ℝ) (f : ℝ → ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  ∫ t, complexMomentJetKernel f k z t ∂μ

theorem norm_complexMomentJetKernel (f : ℝ → ℝ) (k : ℕ) (z : ℂ) {t : ℝ}
    (ht : 0 < t) :
    ‖complexMomentJetKernel f k z t‖ =
      (|Real.log t| ^ k * t ^ (-z.re)) * ‖f t * t ^ (-(3 : ℝ) / 2)‖ := by
  rw [complexMomentJetKernel, norm_mul, norm_pow, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, norm_complexMomentKernel f z ht]
  rw [show -z.re - (3 : ℝ) / 2 = -z.re + (-(3 : ℝ) / 2) by ring,
    Real.rpow_add ht]
  rw [show f t * (t ^ (-z.re) * t ^ (-(3 : ℝ) / 2)) =
    t ^ (-z.re) * (f t * t ^ (-(3 : ℝ) / 2)) by ring,
    norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
  ring

theorem measurable_complexMomentJetKernel {f : ℝ → ℝ} (hf : Measurable f)
    (k : ℕ) (z : ℂ) : Measurable (complexMomentJetKernel f k z) := by
  exact (((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg.pow_const k).mul
    (measurable_complexMomentKernel hf z))

theorem hasDerivAt_complexMomentJetKernel (f : ℝ → ℝ) (k : ℕ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => complexMomentJetKernel f k w t)
      (complexMomentJetKernel f (k + 1) z t) z := by
  convert (hasDerivAt_complexMomentKernel f z t).const_mul
      ((-(Real.log t : ℂ)) ^ k) using 1
  simp only [complexMomentJetKernel, pow_succ]
  ring

theorem integrable_complexMomentJet {μ : Measure ℝ} {H : ℝ} {f : ℝ → ℝ} {z : ℂ}
    (hH : 0 < H) (hz : 0 < z.re) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) (k : ℕ) :
    Integrable (complexMomentJetKernel f k z) μ := by
  obtain ⟨C, _, hC⟩ := exists_log_pow_rpow_bound hH hz k
  apply (hint.norm.const_mul C).mono'
    (measurable_complexMomentJetKernel hf k z).aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  rw [norm_complexMomentJetKernel f k z (hH.trans_le ht)]
  exact mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg _)

/-- All derivatives of the actual complex moment are given by absolutely
convergent logarithmic moments on the open right half-plane. -/
theorem hasDerivAt_complexMomentJet {μ : Measure ℝ} {H : ℝ} {f : ℝ → ℝ} {z : ℂ}
    (hH : 0 < H) (hz : 0 < z.re) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) (k : ℕ) :
    HasDerivAt (complexMomentJet μ f k) (complexMomentJet μ f (k + 1) z) z := by
  let ε : ℝ := z.re / 2
  let S : ℝ := z.re + ε
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεS : ε ≤ S := by dsimp [S]; linarith
  obtain ⟨C, _, hC⟩ := exists_log_pow_strip_bound hH hε hεS (k + 1)
  have hb : ∀ x ∈ ball z ε, ε ≤ x.re ∧ x.re ≤ S := by
    intro x hx
    rw [mem_ball_iff_norm] at hx
    have hu := (Complex.re_le_norm (x - z)).trans hx.le
    have hl : (z - x).re ≤ ε := by
      exact (Complex.re_le_norm (z - x)).trans (by simpa only [norm_sub_rev] using hx.le)
    simp only [Complex.sub_re] at hu hl
    dsimp [ε, S] at *
    constructor <;> linarith
  have hmeas : ∀ᶠ x : ℂ in 𝓝 z,
      AEStronglyMeasurable (complexMomentJetKernel f k x) μ :=
    Eventually.of_forall fun x =>
      (measurable_complexMomentJetKernel hf k x).aestronglyMeasurable
  have hdm := (measurable_complexMomentJetKernel hf (k + 1) z).aestronglyMeasurable (μ := μ)
  have hbound : ∀ᵐ t ∂μ, ∀ x ∈ ball z ε,
      ‖complexMomentJetKernel f (k + 1) x t‖ ≤
        C * ‖f t * t ^ (-(3 : ℝ) / 2)‖ := by
    filter_upwards [hsupp] with t ht
    intro x hx
    rw [norm_complexMomentJetKernel f (k + 1) x (hH.trans_le ht)]
    exact mul_le_mul_of_nonneg_right (hC t x.re ht (hb x hx).1 (hb x hx).2) (norm_nonneg _)
  have hd : ∀ᵐ t ∂μ, ∀ x ∈ ball z ε,
      HasDerivAt (fun x => complexMomentJetKernel f k x t)
        (complexMomentJetKernel f (k + 1) x t) x := by
    exact Eventually.of_forall fun t x _ => hasDerivAt_complexMomentJetKernel f k x t
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hmeas
    (integrable_complexMomentJet hH hz hf hsupp hint k) hdm hbound
    (hint.norm.const_mul C) hd).2

theorem iteratedDeriv_complexMoment {μ : Measure ℝ} {H : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) (k : ℕ) :
    ∀ z : ℂ, 0 < z.re →
      iteratedDeriv k (complexMoment μ f) z = complexMomentJet μ f k z := by
  induction k with
  | zero =>
      intro z _
      simp [complexMomentJet, complexMomentJetKernel, complexMoment]
  | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv k (complexMoment μ f) =ᶠ[𝓝 z] complexMomentJet μ f k := by
        filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
        exact ih w hw
      rw [heq.deriv_eq]
      exact (hasDerivAt_complexMomentJet hH hz hf hsupp hint k).deriv

end
end LeanVerification.Stieltjes
