import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.Stieltjes

noncomputable section

/-- The positive Cauchy kernel; the arguments used below keep its denominator positive. -/
def kernel (δ t : ℝ) : ℝ := 1 / (δ + t) ^ 2

private lemma reciprocal_derivative {δ s x : ℝ} (hδs : 0 < δ + s)
    (hx : x ∈ Ici s) :
    HasDerivAt (fun t : ℝ => -(δ + t)⁻¹) (kernel δ x) x := by
  have hp : δ + x ≠ 0 := ne_of_gt (by linarith [hx.out])
  convert (((hasDerivAt_id x).const_add δ).inv hp).neg using 1
  simp [kernel, div_eq_mul_inv]

private lemma reciprocal_tendsto (δ : ℝ) :
    Tendsto (fun t : ℝ => -(δ + t)⁻¹) atTop (𝓝 0) := by
  have ht : Tendsto (fun t : ℝ => δ + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop δ tendsto_id
  simpa using (tendsto_inv_atTop_zero.comp ht).neg

theorem integrableOn_kernel_tail {δ s : ℝ} (hδs : 0 < δ + s) :
    IntegrableOn (kernel δ) (Ici s) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun x hx => reciprocal_derivative hδs hx)
    (fun x _ => by exact one_div_nonneg.mpr (sq_nonneg _))
    (reciprocal_tendsto δ)

theorem integral_kernel_tail {δ s : ℝ} (hδs : 0 < δ + s) :
    (∫ t in Ici s, kernel δ t) = 1 / (δ + s) := by
  rw [integral_Ici_eq_integral_Ioi]
  convert integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun x hx => reciprocal_derivative hδs hx)
    (fun x _ => by exact one_div_nonneg.mpr (sq_nonneg _))
    (reciprocal_tendsto δ) using 1
  simp [one_div]

/-- A layer retains the endpoint `s = 0`, hence also atoms there. -/
def layer (δ : ℝ) (f : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (Ici s).indicator (fun t => f s * kernel δ t) t

theorem integrableOn_layer {δ s : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (f : ℝ → ℝ) :
    IntegrableOn (layer δ f s) (Ici 0) := by
  unfold layer IntegrableOn
  rw [integrable_indicator_iff measurableSet_Ici, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ici,
    inter_eq_left.mpr (Ici_subset_Ici.mpr hs)]
  exact (integrableOn_kernel_tail (by linarith : 0 < δ + s)).const_mul (f s)

theorem integral_layer {δ s : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (f : ℝ → ℝ) :
    (∫ t in Ici 0, layer δ f s t) = f s / (δ + s) := by
  unfold layer
  rw [setIntegral_indicator measurableSet_Ici,
    inter_eq_right.mpr (Ici_subset_Ici.mpr hs), integral_const_mul,
    integral_kernel_tail (by linarith : 0 < δ + s)]
  ring

theorem integral_norm_layer {δ s : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (f : ℝ → ℝ) :
    (∫ t in Ici 0, ‖layer δ f s t‖) = ‖f s / (δ + s)‖ := by
  have heq : (fun t => ‖layer δ f s t‖) = layer δ (fun x => ‖f x‖) s := by
    funext t
    by_cases hst : s ≤ t
    · simp [layer, hst, norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (one_div_nonneg.mpr (sq_nonneg (δ + t))), kernel]
    · simp [layer, hst]
  rw [heq, integral_layer hδ hs]
  simp only [norm_div, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < δ + s)]

theorem measurable_layer {δ : ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun p : ℝ × ℝ => layer δ f p.1 p.2) := by
  have hk : Measurable (fun p : ℝ × ℝ => f p.1 * kernel δ p.2) :=
    (hf.comp measurable_fst).mul
      (measurable_const.div ((measurable_const.add measurable_snd).pow_const 2))
  simpa only [layer, indicator, mem_Ici] using
    Measurable.ite (measurableSet_le measurable_fst measurable_snd) hk measurable_const

theorem integrable_layer_product {μ : Measure ℝ} [SFinite μ]
    {δ : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ s ∂μ, 0 ≤ s)
    (hint : Integrable (fun s => f s / (δ + s)) μ) :
    Integrable (fun p : ℝ × ℝ => layer δ f p.1 p.2)
      (μ.prod (volume.restrict (Ici 0))) := by
  apply (integrable_prod_iff (measurable_layer hf).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hsupp] with s hs
    exact integrableOn_layer hδ hs f
  · apply hint.norm.congr
    filter_upwards [hsupp] with s hs
    exact (integral_norm_layer hδ hs f).symm

theorem integral_layer_in_first_variable {μ : Measure ℝ}
    (δ : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    (∫ s, layer δ f s t ∂μ) = (∫ s in Iic t, f s ∂μ) / (δ + t) ^ 2 := by
  have heq : (fun s => layer δ f s t) =
      (Iic t).indicator (fun s => f s * kernel δ t) := by
    funext s
    by_cases hst : s ≤ t <;> simp [layer, hst]
  rw [heq, integral_indicator measurableSet_Iic, integral_mul_const]
  simp [kernel, div_eq_mul_inv]

theorem integrable_cumulative_kernel {μ : Measure ℝ} [SFinite μ]
    {δ : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ s ∂μ, 0 ≤ s)
    (hint : Integrable (fun s => f s / (δ + s)) μ) :
    IntegrableOn (fun t => (∫ s in Iic t, f s ∂μ) / (δ + t) ^ 2) (Ici 0) := by
  apply (integrable_layer_product hδ hf hsupp hint).integral_prod_right.congr
  filter_upwards [] with t
  exact integral_layer_in_first_variable δ f t

theorem cauchy_cumulative_representation {μ : Measure ℝ} [SFinite μ]
    {δ : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ s ∂μ, 0 ≤ s)
    (hint : Integrable (fun s => f s / (δ + s)) μ) :
    (∫ s, f s / (δ + s) ∂μ) =
      ∫ t in Ici 0, (∫ s in Iic t, f s ∂μ) / (δ + t) ^ 2 := by
  calc
    (∫ s, f s / (δ + s) ∂μ) =
        ∫ s, (∫ t in Ici 0, layer δ f s t) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hsupp] with s hs
      exact (integral_layer hδ hs f).symm
    _ = ∫ t in Ici 0, ∫ s, layer δ f s t ∂μ :=
      integral_integral_swap (integrable_layer_product hδ hf hsupp hint)
    _ = ∫ t in Ici 0, (∫ s in Iic t, f s ∂μ) / (δ + t) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with t
      exact integral_layer_in_first_variable δ f t

/-- One weighted absolute-integrability hypothesis suffices for every positive argument. -/
theorem integrable_cauchy_of_weighted {μ : Measure ℝ}
    {δ : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ s ∂μ, 0 ≤ s)
    (hint : Integrable (fun s => f s / (1 + s)) μ) :
    Integrable (fun s => f s / (δ + s)) μ := by
  let C : ℝ := (1 + δ) / δ
  apply (hint.norm.const_mul C).mono'
    (hf.div (measurable_const.add measurable_id)).aestronglyMeasurable
  filter_upwards [hsupp] with s hs
  have hd : 0 < δ + s := by linarith
  have h1 : 0 < 1 + s := by linarith
  have hr : (1 + s) / (δ + s) ≤ C := by
    dsimp [C]
    apply (div_le_div_iff₀ hd hδ).mpr
    nlinarith [sq_nonneg δ]
  have heq : f s / (δ + s) = (f s / (1 + s)) * ((1 + s) / (δ + s)) := by
    field_simp
  change ‖f s / (δ + s)‖ ≤ C * ‖f s / (1 + s)‖
  rw [heq, norm_mul]
  have hn : ‖(1 + s) / (δ + s)‖ = (1 + s) / (δ + s) :=
    Real.norm_of_nonneg (div_nonneg h1.le hd.le)
  rw [hn, mul_comm C]
  exact mul_le_mul_of_nonneg_left hr (norm_nonneg _)

theorem cauchy_cumulative_of_weighted {μ : Measure ℝ} [SFinite μ]
    {δ : ℝ} {f : ℝ → ℝ} (hδ : 0 < δ) (hf : Measurable f)
    (hsupp : ∀ᵐ s ∂μ, 0 ≤ s)
    (hint : Integrable (fun s => f s / (1 + s)) μ) :
    (∫ s, f s / (δ + s) ∂μ) =
      ∫ t in Ici 0, (∫ s in Iic t, f s ∂μ) / (δ + t) ^ 2 :=
  cauchy_cumulative_representation hδ hf hsupp
    (integrable_cauchy_of_weighted hδ hf hsupp hint)

/-- A real density against a positive measure permits signed atoms as well as continuous input. -/
theorem cauchy_atom (δ t A : ℝ) :
    (∫ s, A / (δ + s) ∂Measure.dirac t) = A / (δ + t) := by
  simp

/-- The exact atom in the cumulative formula, including an atom at zero. -/
theorem cumulative_atom (t A x : ℝ) :
    (∫ _s in Iic x, A ∂Measure.dirac t) = if t ≤ x then A else 0 := by
  by_cases ht : t ≤ x <;> simp [measureReal_def, ht]

def weightedMoment (μ : Measure ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t, f t * t ^ (-r - (3 : ℝ) / 2) ∂μ

theorem moment_integrand_bound {H t r A : ℝ}
    (hH : 0 < H) (ht : H ≤ t) (hr : 0 ≤ r) :
    ‖A * t ^ (-r - (3 : ℝ) / 2)‖ ≤
      H ^ (-r) * ‖A * t ^ (-(3 : ℝ) / 2)‖ := by
  have hp : 0 < t := hH.trans_le ht
  have he : -r - (3 : ℝ) / 2 = -r + (-(3 : ℝ) / 2) := by ring
  rw [he, Real.rpow_add hp]
  have hn : ‖t ^ (-r)‖ = t ^ (-r) :=
    Real.norm_of_nonneg (Real.rpow_nonneg hp.le _)
  calc
    ‖A * (t ^ (-r) * t ^ (-(3 : ℝ) / 2))‖ =
        t ^ (-r) * ‖A * t ^ (-(3 : ℝ) / 2)‖ := by
      rw [mul_left_comm, norm_mul, hn]
    _ ≤ H ^ (-r) * ‖A * t ^ (-(3 : ℝ) / 2)‖ := by
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hH ht (by linarith)) (norm_nonneg _)

theorem integrable_weightedMoment {μ : Measure ℝ} {H r : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hr : 0 ≤ r) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    Integrable (fun t => f t * t ^ (-r - (3 : ℝ) / 2)) μ := by
  apply (hint.norm.const_mul (H ^ (-r))).mono'
    (hf.mul (measurable_id.pow_const _)).aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  exact moment_integrand_bound hH ht hr

theorem weightedMoment_bound {μ : Measure ℝ} {H r : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hr : 0 ≤ r) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    ‖weightedMoment μ f r‖ ≤
      H ^ (-r) * ∫ t, ‖f t * t ^ (-(3 : ℝ) / 2)‖ ∂μ := by
  unfold weightedMoment
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono_ae (integrable_weightedMoment hH hr hf hsupp hint).norm
    (hint.norm.const_mul _)
  filter_upwards [hsupp] with t ht
  exact moment_integrand_bound hH ht hr

def normalizedMoment (μ : Measure ℝ) (f : ℝ → ℝ) (r : ℝ) : ℝ :=
  weightedMoment μ f r / Real.pi

def normalizedMomentMass (μ : Measure ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ t, ‖f t * t ^ (-(3 : ℝ) / 2)‖ ∂μ) / Real.pi

/-- The manuscript's normalization and its exact geometric moment bound. -/
theorem normalizedMoment_bound {μ : Measure ℝ} {H r : ℝ} {f : ℝ → ℝ}
    (hH : 0 < H) (hr : 0 ≤ r) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    ‖normalizedMoment μ f r‖ ≤ normalizedMomentMass μ f * H ^ (-r) := by
  unfold normalizedMoment normalizedMomentMass
  rw [norm_div, Real.norm_of_nonneg Real.pi_pos.le]
  calc
    ‖weightedMoment μ f r‖ / Real.pi ≤
        (H ^ (-r) * ∫ t, ‖f t * t ^ (-(3 : ℝ) / 2)‖ ∂μ) / Real.pi :=
      div_le_div_of_nonneg_right (weightedMoment_bound hH hr hf hsupp hint) Real.pi_pos.le
    _ = ((∫ t, ‖f t * t ^ (-(3 : ℝ) / 2)‖ ∂μ) / Real.pi) * H ^ (-r) := by
      ring

theorem weightedMoment_atom (t A r : ℝ) :
    weightedMoment (Measure.dirac t) (fun _ => A) r =
      A * t ^ (-r - (3 : ℝ) / 2) := by
  simp [weightedMoment]

end
end LeanVerification.Stieltjes
