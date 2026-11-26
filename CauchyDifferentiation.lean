import LeanVerification.StieltjesMoments
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace LeanVerification.Cauchy

def transform (μ : Measure ℝ) (f : ℝ → ℝ) (β δ : ℝ) : ℝ :=
  ∫ t, f t * (δ + t) ^ (-β) ∂μ

def factorDensity (c : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ := (t - c) * f t

theorem kernel_bound {β d δ t : ℝ} (hβ : 0 ≤ β) (hd : 0 < d)
    (hδ : d ≤ δ) (ht : 0 ≤ t) :
    (δ + t) ^ (-β) ≤ (min d 1) ^ (-β) * (1 + t) ^ (-β) := by
  have hm : 0 < min d 1 := lt_min hd zero_lt_one
  have hmul : min d 1 * (1 + t) ≤ δ + t := by
    have h1 := min_le_left d 1
    have h2 := min_le_right d 1
    nlinarith
  have hp : 0 < min d 1 * (1 + t) := mul_pos hm (by linarith)
  have he := Real.rpow_le_rpow_of_nonpos hp hmul (neg_nonpos.mpr hβ)
  rwa [Real.mul_rpow hm.le (by linarith : 0 ≤ 1 + t)] at he

theorem norm_integrand_bound {β d δ t A : ℝ} (hβ : 0 ≤ β) (hd : 0 < d)
    (hδ : d ≤ δ) (ht : 0 ≤ t) :
    ‖A * (δ + t) ^ (-β)‖ ≤
      (min d 1) ^ (-β) * ‖A * (1 + t) ^ (-β)‖ := by
  simp only [norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ δ + t) _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ 1 + t) _)]
  have h := mul_le_mul_of_nonneg_left (kernel_bound hβ hd hδ ht) (norm_nonneg A)
  nlinarith

theorem integrable_transform {μ : Measure ℝ} {f : ℝ → ℝ} {β δ : ℝ}
    (hβ : 0 ≤ β) (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    Integrable (fun t => f t * (δ + t) ^ (-β)) μ := by
  apply (hint.norm.const_mul ((min δ 1) ^ (-β))).mono'
    (hf.mul ((measurable_const.add measurable_id).pow_const _)).aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  exact norm_integrand_bound hβ hδ le_rfl ht

theorem hasDerivAt_kernel (f : ℝ → ℝ) (β δ t : ℝ) (hδt : 0 < δ + t) :
    HasDerivAt (fun x => f t * (x + t) ^ (-β))
      (f t * (-β) * (δ + t) ^ (-β - 1)) δ := by
  convert (((hasDerivAt_id δ).add_const t).rpow_const
    (p := -β) (Or.inl hδt.ne')).const_mul (f t) using 1
  simp only [id_eq, add_comm t δ]
  ring

theorem derivative_integrand_bound {β d δ t A : ℝ} (hβ : 0 ≤ β) (hd : 0 < d)
    (hδ : d ≤ δ) (ht : 0 ≤ t) :
    ‖A * (-β) * (δ + t) ^ (-β - 1)‖ ≤
      ((min d 1) ^ (-β) * (β / d)) * ‖A * (1 + t) ^ (-β)‖ := by
  have hp : 0 < δ + t := by linarith
  have he : ‖A * (-β) * (δ + t) ^ (-β - 1)‖ =
      ‖A * (δ + t) ^ (-β)‖ * (β / (δ + t)) := by
    rw [Real.rpow_sub_one hp.ne']
    simp only [norm_mul, norm_neg, Real.norm_of_nonneg hβ, norm_div,
      Real.norm_of_nonneg hp.le, Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)]
    ring
  rw [he]
  have hb := norm_integrand_bound (A := A) hβ hd hδ ht
  have hdv : β / (δ + t) ≤ β / d :=
    div_le_div_of_nonneg_left hβ hd (by linarith)
  calc
    _ ≤ ((min d 1) ^ (-β) * ‖A * (1 + t) ^ (-β)‖) * (β / d) :=
      mul_le_mul hb hdv (div_nonneg hβ hp.le) (by positivity)
    _ = _ := by ring

/-- Differentiation of the actual transform follows from its original
weighted integrability, using a common majorant on each positive neighborhood. -/
theorem hasDerivAt_transform {μ : Measure ℝ} {f : ℝ → ℝ} {β δ : ℝ}
    (hβ : 0 < β) (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    Integrable (fun t => f t * (-β) * (δ + t) ^ (-β - 1)) μ ∧
      HasDerivAt (transform μ f β)
        (∫ t, f t * (-β) * (δ + t) ^ (-β - 1) ∂μ) δ := by
  let d := δ / 2
  have hd : 0 < d := half_pos hδ
  have hball : ∀ x ∈ ball δ d, d ≤ x := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have hl := (abs_lt.mp hx).1
    dsimp [d] at *
    linarith
  have hm : ∀ᶠ x : ℝ in 𝓝 δ,
      AEStronglyMeasurable (fun t => f t * (x + t) ^ (-β)) μ :=
    Eventually.of_forall fun x =>
      (hf.mul ((measurable_const.add measurable_id).pow_const _)).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun t => f t * (-β) * (δ + t) ^ (-β - 1)) μ :=
    ((hf.mul_const _).mul ((measurable_const.add measurable_id).pow_const _)).aestronglyMeasurable
  have hb : ∀ᵐ t ∂μ, ∀ x ∈ ball δ d,
      ‖f t * (-β) * (x + t) ^ (-β - 1)‖ ≤
        ((min d 1) ^ (-β) * (β / d)) * ‖f t * (1 + t) ^ (-β)‖ := by
    filter_upwards [hsupp] with t ht
    intro x hx
    exact derivative_integrand_bound hβ.le hd (hball x hx) ht
  have hdiff : ∀ᵐ t ∂μ, ∀ x ∈ ball δ d,
      HasDerivAt (fun x => f t * (x + t) ^ (-β))
        (f t * (-β) * (x + t) ^ (-β - 1)) x := by
    filter_upwards [hsupp] with t ht
    intro x hx
    exact hasDerivAt_kernel f β x t (by linarith [hball x hx])
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hd hm
    (integrable_transform hβ.le hδ hf hsupp hint) hdm hb
    (hint.norm.const_mul ((min d 1) ^ (-β) * (β / d))) hdiff

theorem integrable_factorDensity {μ : Measure ℝ} {f : ℝ → ℝ} {β : ℝ}
    (c : ℝ) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    Integrable (fun t => factorDensity c f t * (1 + t) ^ (-(β + 1))) μ := by
  have hm : Measurable (factorDensity c f) := (measurable_id.sub_const c).mul hf
  apply (hint.norm.const_mul (1 + |c|)).mono'
    (hm.mul ((measurable_const.add measurable_id).pow_const _)).aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  have hp : 0 < 1 + t := by linarith
  have habs : |t - c| ≤ (1 + |c|) * (1 + t) := by
    have ha := abs_sub t c
    rw [abs_of_nonneg ht] at ha
    nlinarith [abs_nonneg c]
  have hratio : |t - c| / (1 + t) ≤ 1 + |c| := (div_le_iff₀ hp).mpr habs
  have he : ‖factorDensity c f t * (1 + t) ^ (-(β + 1))‖ =
      (|t - c| / (1 + t)) * ‖f t * (1 + t) ^ (-β)‖ := by
    rw [show -(β + 1) = -β - 1 by ring, Real.rpow_sub_one hp.ne']
    simp only [factorDensity, norm_mul, norm_div, Real.norm_eq_abs,
      abs_of_nonneg hp.le, abs_of_nonneg (Real.rpow_nonneg hp.le _)]
    ring
  change ‖factorDensity c f t * (1 + t) ^ (-(β + 1))‖ ≤ _
  rw [he]
  exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)

theorem hasDerivAt_normalized_transform {μ : Measure ℝ} {f : ℝ → ℝ} {β δ c : ℝ}
    (hβ : 0 < β) (hδ : 0 < δ) (hc : 0 ≤ c) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, 0 ≤ t)
    (hint : Integrable (fun t => f t * (1 + t) ^ (-β)) μ) :
    HasDerivAt (fun x => (x + c) ^ β * transform μ f β x)
      (β * (δ + c) ^ (β - 1) * transform μ (factorDensity c f) (β + 1) δ) δ := by
  have hpc : 0 < δ + c := by linarith
  have hq := hasDerivAt_transform hβ hδ hf hsupp hint
  have hd := (((hasDerivAt_id δ).add_const c).rpow_const
    (p := β) (Or.inl hpc.ne')).mul hq.2
  apply hd.congr_deriv
  simp only [id_eq, one_mul]
  unfold transform
  have hif := integrable_transform hβ.le hδ hf hsupp hint
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add
    (hif.const_mul (β * (δ + c) ^ (β - 1))) (hq.1.const_mul ((δ + c) ^ β)),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hsupp] with t ht
  have hpt : 0 < δ + t := by linarith
  have hp1 : (δ + c) ^ β = (δ + c) ^ (β - 1) * (δ + c) := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hpc.ne' (β - 1)
  have hp2 : (δ + t) ^ (-β) = (δ + t) ^ (-β - 1) * (δ + t) := by
    simpa only [sub_add_cancel] using Real.rpow_add_one hpt.ne' (-β - 1)
  rw [hp1, hp2, show -(β + 1) = -β - 1 by ring]
  dsimp only [factorDensity]
  ring

end LeanVerification.Cauchy
