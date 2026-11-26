import LeanVerification.AngularCauchy
import LeanVerification.SlitCauchyHolomorphic

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.SpectralWidth

def cauchyReal (μ : Measure ℝ) (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  ∫ t, (f t / Real.sqrt t) / (t - v) ∂μ

def width (μ : Measure ℝ) (f : ℝ → ℝ) (K v : ℝ) : ℝ :=
  Real.sqrt v * (K + (1 / Real.pi) * cauchyReal μ f v)

def angularPeriod (W : ℝ → ℝ) (h : ℝ) : ℝ :=
  ∫ θ in Ioc (0 : ℝ) (Real.pi / 2),
    2 * Real.sqrt (2 * h) * Real.sin θ * deriv W (h * Real.sin θ ^ 2)

theorem gamma_mass_eq (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    ‖((f t / Real.sqrt t : ℝ) : ℂ)‖ / t = ‖f t * t ^ (-(3 : ℝ) / 2)‖ := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hs, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg ht.le _),
    show -(3 : ℝ) / 2 = -(3 / 2) by ring, Real.rpow_neg ht.le,
    AbelCauchy.rpow_three_halves ht]
  simp only [Real.norm_eq_abs]
  field_simp
  left
  ring

theorem gamma_measurable {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Measurable f) :
    AEStronglyMeasurable (fun t => ((f t / Real.sqrt t : ℝ) : ℂ)) μ :=
  (Complex.continuous_ofReal.measurable.comp (hf.div Real.continuous_sqrt.measurable)).aestronglyMeasurable

theorem gamma_mass_integrable {μ : Measure ℝ} {f : ℝ → ℝ} {H : ℝ}
    (hH : 0 < H) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    Integrable (fun t => ‖((f t / Real.sqrt t : ℝ) : ℂ)‖ / t) μ := by
  apply hint.norm.congr
  filter_upwards [hsupp] with t ht
  exact (gamma_mass_eq f (hH.trans_le ht)).symm

theorem cauchyIntegral_eq_ofReal (μ : Measure ℝ) (f : ℝ → ℝ) (v : ℝ) :
    SlitContour.cauchyIntegral μ (fun t => ((f t / Real.sqrt t : ℝ) : ℂ)) (v : ℂ) =
      (cauchyReal μ f v : ℂ) := by
  unfold SlitContour.cauchyIntegral cauchyReal
  simp only [← Complex.ofReal_sub, ← Complex.ofReal_div]
  exact integral_complex_ofReal

theorem hasDerivAt_cauchyReal {μ : Measure ℝ} {f : ℝ → ℝ} {H v : ℝ}
    (hH : 0 < H) (hv : v < H) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    HasDerivAt (cauchyReal μ f)
      (∫ t, (f t / Real.sqrt t) / (t - v) ^ 2 ∂μ) v := by
  have hd := SlitContour.hasDerivAt_cauchyIntegral hH
    (show (v : ℂ) ∈ SlitContour.domain H from Or.inl hv)
    (gamma_measurable hf) hsupp (gamma_mass_integrable hH hsupp hint)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt v hd.comp_ofReal
  convert hr using 1
  · funext x
    change cauchyReal μ f x = (SlitContour.cauchyIntegral μ
      (fun t => ((f t / Real.sqrt t : ℝ) : ℂ)) (x : ℂ)).re
    rw [cauchyIntegral_eq_ofReal]
    rfl
  · simp only [Complex.reCLM_apply, ← Complex.ofReal_sub, ← Complex.ofReal_pow,
      ← Complex.ofReal_div, integral_complex_ofReal, Complex.ofReal_re]

theorem integrable_cauchyReal {μ : Measure ℝ} {f : ℝ → ℝ} {H v : ℝ}
    (hH : 0 < H) (hv : v < H) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    Integrable (fun t => (f t / Real.sqrt t) / (t - v)) μ := by
  have hi := (SlitContour.integrable_cauchyIntegral hH
    (show (v : ℂ) ∈ SlitContour.domain H from Or.inl hv)
    (gamma_measurable hf) hsupp (gamma_mass_integrable hH hsupp hint)).re
  simpa only [← Complex.ofReal_sub, ← Complex.ofReal_div, Complex.ofReal_re] using hi

theorem integrable_cauchyReal_derivative {μ : Measure ℝ} {f : ℝ → ℝ} {H v : ℝ}
    (hH : 0 < H) (hv : v < H) (hf : Measurable f) (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    Integrable (fun t => (f t / Real.sqrt t) / (t - v) ^ 2) μ := by
  have hi := (integrable_cauchyReal hH hv hf hsupp hint).norm.div_const (H - v)
  have hm : Measurable (fun t => (f t / Real.sqrt t) / (t - v) ^ 2) := by fun_prop
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [hsupp] with t ht
  have hden : 0 < t - v := by linarith
  rw [show (f t / Real.sqrt t) / (t - v) ^ 2 =
    ((f t / Real.sqrt t) / (t - v)) / (t - v) by rw [pow_two, div_mul_eq_div_div],
    norm_div, Real.norm_of_nonneg hden.le]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (sub_pos.mpr hv) (by linarith)

theorem hasDerivAt_width {μ : Measure ℝ} {f : ℝ → ℝ} {H v K : ℝ}
    (hH : 0 < H) (hv : v ∈ Ioo 0 H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    HasDerivAt (width μ f K)
      ((K + (1 / Real.pi) * cauchyReal μ f v) / (2 * Real.sqrt v) +
        Real.sqrt v * ((1 / Real.pi) * ∫ t, (f t / Real.sqrt t) / (t - v) ^ 2 ∂μ)) v := by
  have hd := (Real.hasDerivAt_sqrt hv.1.ne').mul
    (((hasDerivAt_cauchyReal hH hv.2 hf hsupp hint).const_mul (1 / Real.pi)).const_add K)
  convert hd using 1
  ring

/-- The actual derivative of the reconstructed width has the required
regular angular input. Both integral terms are integrable from the initial mass. -/
theorem scaled_deriv_width {μ : Measure ℝ} {f : ℝ → ℝ} {H v K : ℝ}
    (hH : 0 < H) (hv : v ∈ Ioo 0 H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    2 * Real.sqrt v * deriv (width μ f K) v = K + (1 / Real.pi) *
      ∫ t, (f t / Real.sqrt t) * ((t + v) / (t - v) ^ 2) ∂μ := by
  have hi0 := integrable_cauchyReal hH hv.2 hf hsupp hint
  have hi1 := integrable_cauchyReal_derivative hH hv.2 hf hsupp hint
  have he : (∫ t, (f t / Real.sqrt t) * ((t + v) / (t - v) ^ 2) ∂μ) =
      cauchyReal μ f v + 2 * v * (∫ t, (f t / Real.sqrt t) / (t - v) ^ 2 ∂μ) := by
    rw [cauchyReal, ← integral_const_mul, ← integral_add hi0 (hi1.const_mul (2 * v))]
    apply integral_congr_ae
    filter_upwards [hsupp] with t ht
    have hn : t - v ≠ 0 := by linarith [hv.2]
    have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr (hH.trans_le ht)).ne'
    field_simp [hn, hs]
    ring
  rw [(hasDerivAt_width hH hv hf hsupp hint).deriv, he]
  have hs : Real.sqrt v ≠ 0 := (Real.sqrt_pos.mpr hv.1).ne'
  have halg (A B : ℝ) : 2 * Real.sqrt v *
      (A / (2 * Real.sqrt v) + Real.sqrt v * B) = A + 2 * v * B := by
    rw [mul_add, ← mul_div_assoc, mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) hs)]
    ring_nf
    rw [Real.sq_sqrt hv.1.le]
    ring
  rw [halg]
  ring

theorem angularPeriod_eq {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℝ} {H h K : ℝ}
    (hH : 0 < H) (hh : h ∈ Ioo 0 H) (hf : Measurable f)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    angularPeriod (width μ f K) h = Real.pi * K / Real.sqrt 2 +
      (1 / Real.sqrt 2) * ∫ t, f t * (t - h) ^ (-(3 : ℝ) / 2) ∂μ := by
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have hi := (AbelCauchy.integrable_angularLayer_product hH hh.1 hh.2 hf hsupp hint).integral_prod_right
  have he : ∀ θ ∈ Ioc (0 : ℝ) (Real.pi / 2),
      2 * Real.sqrt (2 * h) * Real.sin θ * deriv (width μ f K) (h * Real.sin θ ^ 2) =
        Real.sqrt 2 * (K + (1 / Real.pi) * ∫ t, AbelCauchy.angularLayer h f t θ ∂μ) := by
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hv : h * Real.sin θ ^ 2 ∈ Ioo 0 H :=
      ⟨mul_pos hh.1 (sq_pos_of_pos hs), (AbelCauchy.angular_energy_mem hh.1 θ).2.trans_lt hh.2⟩
    have hd := scaled_deriv_width hH hv hf hsupp hint (K := K)
    have hsv : Real.sqrt (h * Real.sin θ ^ 2) = Real.sqrt h * Real.sin θ := by
      rw [Real.sqrt_mul hh.1.le, Real.sqrt_sq hs.le]
    rw [hsv] at hd
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp only [AbelCauchy.angularLayer, AbelCauchy.angularKernel]
    linear_combination Real.sqrt 2 * hd
  unfold angularPeriod
  rw [setIntegral_congr_fun measurableSet_Ioc he, integral_const_mul,
    integral_add (integrable_const K) (hi.const_mul (1 / Real.pi)), integral_const_mul,
    AbelCauchy.integral_angularLayer_swap hH hh.1 hh.2 hf hsupp hint]
  have hc : (∫ _θ in Ioc (0 : ℝ) (Real.pi / 2), K) = (Real.pi / 2) * K := by
    rw [← intervalIntegral.integral_of_le hpi, intervalIntegral.integral_const]
    simp [smul_eq_mul]
  rw [hc]
  generalize (∫ t, f t * (t - h) ^ (-(3 : ℝ) / 2) ∂μ) = J
  have hs : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

theorem width_congr_ae {μ : Measure ℝ} {f g : ℝ → ℝ} (he : f =ᵐ[μ] g) (K : ℝ) :
    width μ f K = width μ g K := by
  funext v
  unfold width cauchyReal
  congr 3
  apply integral_congr_ae
  filter_upwards [he] with t ht
  rw [ht]

/-- The exact period representation also holds for the actual boundary
density, whose measurability is initially obtained almost everywhere. -/
theorem angularPeriod_eq_ae {μ : Measure ℝ} [SFinite μ] {f : ℝ → ℝ} {H h K : ℝ}
    (hH : 0 < H) (hh : h ∈ Ioo 0 H) (hf : AEStronglyMeasurable f μ)
    (hsupp : ∀ᵐ t ∂μ, H ≤ t)
    (hint : Integrable (fun t => f t * t ^ (-(3 : ℝ) / 2)) μ) :
    angularPeriod (width μ f K) h = Real.pi * K / Real.sqrt 2 +
      (1 / Real.sqrt 2) * ∫ t, f t * (t - h) ^ (-(3 : ℝ) / 2) ∂μ := by
  let g := hf.aemeasurable.mk f
  have hg : Measurable g := hf.aemeasurable.measurable_mk
  have he : f =ᵐ[μ] g := hf.aemeasurable.ae_eq_mk
  have hi : Integrable (fun t => g t * t ^ (-(3 : ℝ) / 2)) μ := by
    apply hint.congr
    filter_upwards [he] with t ht
    rw [ht]
  rw [width_congr_ae he K, angularPeriod_eq hH hh hg hsupp hi]
  congr 2
  apply integral_congr_ae
  filter_upwards [he] with t ht
  rw [ht]

theorem angularPeriod_congrOn {W V : ℝ → ℝ} {H h : ℝ} (hh : h ∈ Ioo 0 H)
    (he : EqOn W V (Ioo 0 H)) : angularPeriod W h = angularPeriod V h := by
  apply setIntegral_congr_fun measurableSet_Ioc
  intro θ hθ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hv : h * Real.sin θ ^ 2 ∈ Ioo 0 H :=
    ⟨mul_pos hh.1 (sq_pos_of_pos hs), (AbelCauchy.angular_energy_mem hh.1 θ).2.trans_lt hh.2⟩
  have hg : W =ᶠ[𝓝 (h * Real.sin θ ^ 2)] V := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with v hv
    exact he hv
  dsimp only
  rw [hg.deriv_eq]

end LeanVerification.SpectralWidth
