import LeanVerification.StieltjesMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.Stieltjes

noncomputable section

/-- Weighted integrability makes the unweighted density integrable on each
bounded initial interval; no finite total reference mass is required. -/
theorem integrableOn_cumulative_of_weighted {μ : Measure ℝ}
    {R : ℝ} {f : ℝ → ℝ} (hf : Measurable f)
    (hsupp : ∀ᵐ s ∂μ, 0 ≤ s)
    (hint : Integrable (fun s => f s / (1 + s)) μ) :
    IntegrableOn f (Iic R) μ := by
  apply ((hint.norm.const_mul (1 + R)).integrableOn).mono'
    hf.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_of_ae hsupp, ae_restrict_mem measurableSet_Iic] with s hs hsR
  have h1 : 0 < 1 + s := by linarith
  have hle : 1 + s ≤ 1 + R := by linarith [hsR.out]
  rw [norm_div, Real.norm_of_nonneg h1.le]
  rw [← mul_div_assoc]
  exact (le_div_iff₀ h1).mpr (by nlinarith [norm_nonneg (f s)])

/-- The exact cutoff boundary contribution vanishes under the same weighted
absolute-integrability assumption as the cumulative representation. -/
theorem tendsto_cumulative_boundary_zero {μ : Measure ℝ}
    {δ : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ s ∂μ, 0 ≤ s)
    (hint : Integrable (fun s => f s / (1 + s)) μ) :
    Tendsto (fun R : ℝ => (∫ s in Iic R, f s ∂μ) / (δ + R))
      atTop (𝓝 0) := by
  let F : ℝ → ℝ → ℝ := fun R => (Iic R).indicator (fun s => f s / (δ + R))
  have hintδ := integrable_cauchy_of_weighted hδ hf hsupp hint
  have hmeas : ∀ R, AEStronglyMeasurable (F R) μ := by
    intro R
    exact ((hf.div_const (δ + R)).indicator measurableSet_Iic).aestronglyMeasurable
  have hbound : ∀ᶠ R : ℝ in atTop, ∀ᵐ s ∂μ,
      ‖F R s‖ ≤ ‖f s / (δ + s)‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
    filter_upwards [hsupp] with s hs
    by_cases hsR : s ≤ R
    · rw [show F R s = f s / (δ + R) by simp [F, hsR]]
      rw [norm_div, norm_div, Real.norm_of_nonneg (by linarith : 0 ≤ δ + R),
        Real.norm_of_nonneg (by linarith : 0 ≤ δ + s)]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (by linarith) (by linarith)
    · rw [show F R s = 0 by simp [F, hsR], norm_zero]
      exact norm_nonneg _
  have hlim : ∀ᵐ s ∂μ, Tendsto (fun R => F R s) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with s
    have ht : Tendsto (fun R : ℝ => δ + R) atTop atTop :=
      tendsto_atTop_add_const_left atTop δ tendsto_id
    have hl : Tendsto (fun R : ℝ => f s / (δ + R)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ht)
    apply hl.congr'
    filter_upwards [eventually_ge_atTop s] with R hR
    simp [F, hR]
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun s => ‖f s / (δ + s)‖) (Eventually.of_forall hmeas) hbound hintδ.norm hlim
  have heq : (fun R : ℝ => ∫ s, F R s ∂μ) =
      fun R : ℝ => (∫ s in Iic R, f s ∂μ) / (δ + R) := by
    funext R
    simp [F, integral_indicator measurableSet_Iic, div_eq_mul_inv, integral_mul_const]
  simpa only [heq, integral_zero] using h

/-- The finite Stieltjes formula retains both cutoff and origin atoms. -/
theorem cauchy_cumulative_finite {μ : Measure ℝ} [SFinite μ]
    {δ R : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (hf : Measurable f) (hsupp : ∀ᵐ s ∂μ, 0 ≤ s)
    (hint : Integrable (fun s => f s / (1 + s)) μ) :
    (∫ s in Iic R, f s / (δ + s) ∂μ) =
      (∫ s in Iic R, f s ∂μ) / (δ + R) +
        ∫ t in Icc 0 R, (∫ s in Iic t, f s ∂μ) / (δ + t)^2 := by
  let μR := μ.restrict (Iic R)
  let CR : ℝ → ℝ := fun t => ∫ s in Iic t, f s ∂μR
  let C : ℝ → ℝ := fun t => ∫ s in Iic t, f s ∂μ
  have hCR (t : ℝ) : CR t = C (min t R) := by
    simp [CR, C, μR, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Iic]
  have hiδ := integrable_cauchy_of_weighted hδ hf hsupp hint
  have hsR : ∀ᵐ s ∂μR, 0 ≤ s := ae_restrict_of_ae hsupp
  have hirep : IntegrableOn (fun t => CR t / (δ + t)^2) (Ici 0) :=
    integrable_cumulative_kernel hδ hf hsR hiδ.integrableOn
  have hsplit := intervalIntegral.integral_Iic_add_Ioi
    (b := R) hirep.integrableOn hirep.integrableOn
  have hleft :
      (∫ t in Iic R, CR t / (δ + t)^2 ∂volume.restrict (Ici 0)) =
      ∫ t in Icc 0 R, C t / (δ + t)^2 := by
    rw [Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ici]
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change CR t / (δ + t)^2 = C t / (δ + t)^2
    rw [hCR, min_eq_left ht.2]
  have hright :
      (∫ t in Ioi R, CR t / (δ + t)^2 ∂volume.restrict (Ici 0)) =
      C R / (δ + R) := by
    rw [Measure.restrict_restrict measurableSet_Ioi,
      inter_eq_left.mpr (show Ioi R ⊆ Ici 0 by intro t ht; exact hR.trans ht.le)]
    calc
      (∫ t in Ioi R, CR t / (δ + t)^2) =
          ∫ t in Ioi R, C R * kernel δ t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        change CR t / (δ + t)^2 = C R * kernel δ t
        rw [hCR, min_eq_right ht.le]
        simp [kernel, div_eq_mul_inv]
      _ = C R / (δ + R) := by
        rw [integral_const_mul, ← integral_Ici_eq_integral_Ioi,
          integral_kernel_tail (by linarith : 0 < δ + R)]
        ring
  have hrep := cauchy_cumulative_representation hδ hf hsR hiδ.integrableOn
  change (∫ s in Iic R, f s / (δ + s) ∂μ) =
    ∫ t in Ici 0, CR t / (δ + t)^2 at hrep
  rw [← hsplit, hleft, hright] at hrep
  simpa only [C, add_comm] using hrep

end
end LeanVerification.Stieltjes
