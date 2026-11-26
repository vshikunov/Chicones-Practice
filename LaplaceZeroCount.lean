import LeanVerification.ComplexMoment
import LeanVerification.FiniteZeroCounting

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace LeanVerification.Laplace

def transform (μ : Measure ℝ) (w f : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t, f t * Real.exp (-s * w t) ∂μ

def factorInput (w : ℝ → ℝ) (c : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  (w t - c) * f t

def factoredInput (w : ℝ → ℝ) : List ℝ → (ℝ → ℝ) → ℝ → ℝ
  | [], f => f
  | c :: cs, f => factoredInput w cs (factorInput w c f)

def HasDampedMoments (μ : Measure ℝ) (w f : ℝ → ℝ) : Prop :=
  ∀ k : ℕ, ∀ s : ℝ, 0 < s →
    Integrable (fun t => (w t) ^ k * f t * Real.exp (-s * w t)) μ

theorem factoredInput_eq_product (w : ℝ → ℝ) (cs : List ℝ) (f : ℝ → ℝ) (t : ℝ) :
    factoredInput w cs f t = (cs.map (fun c => w t - c)).prod * f t := by
  induction cs generalizing f with
  | nil => simp [factoredInput]
  | cons c cs ih =>
      simp only [factoredInput, ih, List.map_cons, List.prod_cons, factorInput]
      ring

/-- Integrability of the input itself supplies every polynomially damped
moment at positive exponents. No undamped polynomial moment is assumed. -/
theorem hasDampedMoments_of_integrable {μ : Measure ℝ} {w f : ℝ → ℝ}
    (hw : Measurable w) (hf : Measurable f) (hwp : ∀ᵐ t ∂μ, 0 ≤ w t)
    (hi : Integrable f μ) : HasDampedMoments μ w f := by
  intro k s hs
  obtain ⟨C, _, hC⟩ := Stieltjes.exists_log_pow_rpow_bound
    (by norm_num : (0 : ℝ) < 1) hs k
  apply (hi.norm.const_mul C).mono'
    ((((hw.pow_const k).mul hf).mul ((hw.const_mul (-s)).exp)).aestronglyMeasurable)
  filter_upwards [hwp] with t ht
  have he : 1 ≤ Real.exp (w t) := by simpa using Real.exp_le_exp.mpr ht
  have hb := hC (Real.exp (w t)) he
  have hr : (w t) ^ k * Real.exp (-s * w t) ≤ C := by
    simpa only [Real.log_exp, abs_of_nonneg ht,
      Real.rpow_def_of_pos (Real.exp_pos (w t)), Real.log_exp,
      mul_comm (w t) (-s)] using hb
  calc
    ‖(w t) ^ k * f t * Real.exp (-s * w t)‖ =
        ((w t) ^ k * Real.exp (-s * w t)) * ‖f t‖ := by
      rw [norm_mul, norm_mul, Real.norm_of_nonneg (pow_nonneg ht k),
        Real.norm_of_nonneg (Real.exp_pos _).le]
      ring
    _ ≤ C * ‖f t‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg _)

theorem HasDampedMoments.factor {μ : Measure ℝ} {w f : ℝ → ℝ}
    (hi : HasDampedMoments μ w f) (c : ℝ) : HasDampedMoments μ w (factorInput w c f) := by
  intro k s hs
  apply ((hi (k + 1) s hs).sub ((hi k s hs).const_mul c)).congr
  filter_upwards [] with t
  simp only [Pi.sub_apply, factorInput, pow_succ]
  ring

theorem hasDerivAt_transform {μ : Measure ℝ} {w f : ℝ → ℝ} {s : ℝ}
    (hw : Measurable w) (hf : Measurable f) (hwp : ∀ᵐ t ∂μ, 0 ≤ w t)
    (hi : HasDampedMoments μ w f) (hs : 0 < s) :
    Integrable (fun t => f t * (-w t) * Real.exp (-s * w t)) μ ∧
      HasDerivAt (transform μ w f)
        (∫ t, f t * (-w t) * Real.exp (-s * w t) ∂μ) s := by
  let d := s / 2
  have hd : 0 < d := half_pos hs
  have hball : ∀ x ∈ ball s d, d ≤ x := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have hl := (abs_lt.mp hx).1
    dsimp [d] at *
    linarith
  have hm : ∀ᶠ x : ℝ in 𝓝 s,
      AEStronglyMeasurable (fun t => f t * Real.exp (-x * w t)) μ :=
    Eventually.of_forall fun x => (hf.mul ((hw.const_mul (-x)).exp)).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun t => f t * (-w t) * Real.exp (-s * w t)) μ :=
    ((hf.mul hw.neg).mul ((hw.const_mul (-s)).exp)).aestronglyMeasurable
  have hbase : Integrable (fun t => f t * Real.exp (-s * w t)) μ := by
    simpa only [pow_zero, one_mul] using hi 0 s hs
  have hmajor : Integrable (fun t => ‖w t * f t * Real.exp (-d * w t)‖) μ := by
    simpa only [pow_one] using (hi 1 d hd).norm
  have hb : ∀ᵐ t ∂μ, ∀ x ∈ ball s d,
      ‖f t * (-w t) * Real.exp (-x * w t)‖ ≤
        ‖w t * f t * Real.exp (-d * w t)‖ := by
    filter_upwards [hwp] with t ht
    intro x hx
    have he : Real.exp (-x * w t) ≤ Real.exp (-d * w t) :=
      Real.exp_le_exp.mpr (by nlinarith [hball x hx])
    simp only [norm_mul, norm_neg, Real.norm_of_nonneg (Real.exp_pos _).le]
    have hb := mul_le_mul_of_nonneg_left he (mul_nonneg (norm_nonneg (w t)) (norm_nonneg (f t)))
    nlinarith
  have hdiff : ∀ᵐ t ∂μ, ∀ x ∈ ball s d,
      HasDerivAt (fun x => f t * Real.exp (-x * w t))
        (f t * (-w t) * Real.exp (-x * w t)) x := by
    exact Eventually.of_forall fun t x _ => by
      convert (((hasDerivAt_id x).neg.mul_const (w t)).exp).const_mul (f t) using 1
      simp only [id_eq, neg_mul, one_mul, neg_one_mul]
      ring
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hd hm hbase hdm hb hmajor hdiff

theorem hasDerivAt_normalized_transform {μ : Measure ℝ} {w f : ℝ → ℝ} {s : ℝ}
    (c : ℝ) (hw : Measurable w) (hf : Measurable f) (hwp : ∀ᵐ t ∂μ, 0 ≤ w t)
    (hi : HasDampedMoments μ w f) (hs : 0 < s) :
    HasDerivAt (fun x => Real.exp (c * x) * transform μ w f x)
      (-Real.exp (c * s) * transform μ w (factorInput w c f) s) s := by
  have hq := hasDerivAt_transform hw hf hwp hi hs
  have hd := (((hasDerivAt_id s).const_mul c).exp).mul hq.2
  apply hd.congr_deriv
  simp only [id_eq, mul_one]
  unfold transform
  have hif : Integrable (fun t => f t * Real.exp (-s * w t)) μ := by
    simpa only [pow_zero, one_mul] using hi 0 s hs
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hif.const_mul (Real.exp (c * s) * c))
      (hq.1.const_mul (Real.exp (c * s))), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [factorInput]
  ring

theorem transform_pos_of_nonnegative {μ : Measure ℝ} {w f : ℝ → ℝ} {s : ℝ}
    (hi : Integrable (fun t => f t * Real.exp (-s * w t)) μ)
    (hsign : ∀ᵐ t ∂μ, 0 ≤ f t) (hnz : ¬f =ᵐ[μ] 0) :
    0 < transform μ w f s := by
  have hn : ∀ᵐ t ∂μ, 0 ≤ f t * Real.exp (-s * w t) :=
    hsign.mono fun t ht => mul_nonneg ht (Real.exp_pos _).le
  have hne : (∫ t, f t * Real.exp (-s * w t) ∂μ) ≠ 0 := by
    intro hz
    apply hnz
    have he := (integral_eq_zero_iff_of_nonneg_ae hn hi).mp hz
    filter_upwards [he] with t ht
    exact (mul_eq_zero.mp ht).resolve_right (Real.exp_pos _).ne'
  exact lt_of_le_of_ne (integral_nonneg_of_ae hn) hne.symm

theorem atMostZeros_of_factor_certificate {μ : Measure ℝ} {w f : ℝ → ℝ}
    (cs : List ℝ) (hw : Measurable w) (hf : Measurable f)
    (hwp : ∀ᵐ t ∂μ, 0 ≤ w t) (hi : HasDampedMoments μ w f)
    (hsign : ∀ᵐ t ∂μ, 0 ≤ factoredInput w cs f t)
    (hnz : ¬factoredInput w cs f =ᵐ[μ] 0) :
    FiniteZeroCounting.AtMostZeros cs.length (transform μ w f) (Ioi 0) := by
  induction cs generalizing f with
  | nil =>
      apply FiniteZeroCounting.atMostZeros_zero_iff.mpr
      intro s hs
      have hint : Integrable (fun t => f t * Real.exp (-s * w t)) μ := by
        simpa only [pow_zero, one_mul] using hi 0 s hs
      exact (transform_pos_of_nonnegative hint hsign hnz).ne'
  | cons c cs ih =>
      have hnew := ih ((hw.sub_const c).mul hf) (hi.factor c) hsign hnz
      let N : ℝ → ℝ := fun s => Real.exp (c * s) * transform μ w f s
      have hd : ∀ s ∈ Ioi (0 : ℝ), HasDerivAt N
          (-Real.exp (c * s) * transform μ w (factorInput w c f) s) s :=
        fun s hs => hasDerivAt_normalized_transform c hw hf hwp hi hs
      have he : ∀ s ∈ Ioi (0 : ℝ),
          transform μ w (factorInput w c f) s = 0 ↔ deriv N s = 0 := by
        intro s hs
        rw [(hd s hs).deriv]
        simp only [mul_eq_zero, neg_ne_zero.mpr (Real.exp_pos _).ne', false_or]
      have hdn := FiniteZeroCounting.atMostZeros_of_same_zeros he hnew
      have hN := FiniteZeroCounting.atMostZeros_of_derivative (convex_Ioi (0 : ℝ))
        (fun s hs => (hd s hs).continuousAt.continuousWithinAt) hdn
      exact (FiniteZeroCounting.atMostZeros_mul_iff
        (fun s _ => (Real.exp_pos (c * s)).ne')).mp hN

theorem continuousOn_transform {μ : Measure ℝ} {w f : ℝ → ℝ}
    (hw : Measurable w) (hf : Measurable f) (hwp : ∀ᵐ t ∂μ, 0 ≤ w t)
    (hi : Integrable f μ) : ContinuousOn (transform μ w f) (Ici 0) := by
  intro s hs
  unfold transform
  apply continuousWithinAt_of_dominated (bound := fun t => ‖f t‖)
  · exact Eventually.of_forall fun x =>
      (hf.mul ((hw.const_mul (-x)).exp)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with x hx
    filter_upwards [hwp] with t ht
    have he : Real.exp (-x * w t) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr (show -x * w t ≤ 0 from mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hx) ht)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_of_le_one_right (norm_nonneg _) he
  · exact hi.norm
  · exact Eventually.of_forall fun t =>
      (continuous_const.mul (Real.continuous_exp.comp
        (continuous_id.neg.mul continuous_const))).continuousWithinAt

/-- The zero bound includes exponent zero, using only continuity there.
All derivative roots supplied by Rolle lie at strictly positive exponents. -/
theorem atMostZeros_Ici_of_factor_certificate {μ : Measure ℝ} {w f : ℝ → ℝ}
    (cs : List ℝ) (hw : Measurable w) (hf : Measurable f)
    (hwp : ∀ᵐ t ∂μ, 0 ≤ w t) (hi : Integrable f μ)
    (hsign : ∀ᵐ t ∂μ, 0 ≤ factoredInput w cs f t)
    (hnz : ¬factoredInput w cs f =ᵐ[μ] 0) :
    FiniteZeroCounting.AtMostZeros cs.length (transform μ w f) (Ici 0) := by
  have hdm := hasDampedMoments_of_integrable hw hf hwp hi
  cases cs with
  | nil =>
      apply FiniteZeroCounting.atMostZeros_zero_iff.mpr
      intro s hs
      have hint : Integrable (fun t => f t * Real.exp (-s * w t)) μ := by
        apply hi.norm.mono'
          (hf.mul ((hw.const_mul (-s)).exp)).aestronglyMeasurable
        filter_upwards [hwp] with t ht
        rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
        apply mul_le_of_le_one_right (norm_nonneg _)
        simpa using Real.exp_le_exp.mpr (show -s * w t ≤ 0 from
          mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) ht)
      exact (transform_pos_of_nonnegative hint hsign hnz).ne'
  | cons c cs =>
      have hnew := atMostZeros_of_factor_certificate cs hw ((hw.sub_const c).mul hf)
        hwp (hdm.factor c) hsign hnz
      let N : ℝ → ℝ := fun s => Real.exp (c * s) * transform μ w f s
      have hN : ContinuousOn N (Ici 0) :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
          (continuousOn_transform hw hf hwp hi)
      intro hz
      have hzm : FiniteZeroCounting.HasOrderedZeros (cs.length + 2) N (Ici 0) := by
        apply FiniteZeroCounting.orderedZeros_of_same_zeros (f := transform μ w f) ?_ hz
        intro s hs
        simp only [N, mul_eq_zero, (Real.exp_pos _).ne', false_or]
      have hdz := FiniteZeroCounting.orderedZeros_derivative_Ici hN hzm
      apply hnew
      apply FiniteZeroCounting.orderedZeros_of_same_zeros (f := deriv N) ?_ hdz
      intro s hs
      rw [(hasDerivAt_normalized_transform c hw hf hwp hdm hs).deriv]
      simp only [mul_eq_zero, neg_ne_zero.mpr (Real.exp_pos _).ne', false_or]
      rfl

end LeanVerification.Laplace
