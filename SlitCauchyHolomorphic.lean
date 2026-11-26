import LeanVerification.SlitReflection
import LeanVerification.CauchyHolomorphic

/-! Holomorphy of the actual complex-density Cauchy integral on the entire
right-cut plane, from its original t^(-1) absolute mass. -/
noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology
namespace LeanVerification.SlitContour

set_option maxHeartbeats 1000000

def cauchyIntegral (μ : Measure ℝ) (Γ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t, Γ t / ((t : ℂ)-z) ∂μ

theorem exists_cauchy_lower_bound {H : ℝ} (hH : 0<H) {z : ℂ} (hz : z ∈ domain H) :
    ∃ ε > 0, ∃ c > 0, ∀ x ∈ ball z ε, ∀ t : ℝ, H ≤ t → c*t ≤ ‖(t:ℂ)-x‖ := by
  have hw : (H:ℂ)-z ∈ Complex.slitPlane := by
    rcases hz with hr | hi
    · exact Or.inl (by simpa using sub_pos.mpr hr)
    · exact Or.inr (by simpa using hi)
  obtain ⟨ε,hε,d,hd,hb⟩ := Cauchy.exists_slit_kernel_lower_bound hw
  refine ⟨ε,hε,d/(1+H),div_pos hd (by linarith),?_⟩
  intro x hx t ht
  have hx' : (H:ℂ)-x ∈ ball ((H:ℂ)-z) ε := by
    simp only [mem_ball_iff_norm] at hx ⊢
    have he : ((H:ℂ)-x)-((H:ℂ)-z)=-(x-z) := by ring
    simpa only [he,norm_neg] using hx
  have hb' := (hb _ hx' (t-H) (sub_nonneg.mpr ht)).2
  have he : ((H:ℂ)-x)+((t-H:ℝ):ℂ)=(t:ℂ)-x := by push_cast; ring
  rw [he] at hb'
  have hscale : t/(1+H) ≤ 1+(t-H) := by
    apply (div_le_iff₀ (by linarith : 0<1+H)).mpr
    nlinarith [mul_nonneg hH.le (sub_nonneg.mpr ht)]
  calc
    d/(1+H)*t = d*(t/(1+H)) := by ring
    _ ≤ d*(1+(t-H)) := mul_le_mul_of_nonneg_left hscale hd.le
    _ ≤ _ := hb'

theorem cauchy_kernel_bound {Γ : ℝ → ℂ} {c t : ℝ} {z : ℂ}
    (hc : 0<c) (ht : 0<t) (hb : c*t ≤ ‖(t:ℂ)-z‖) :
    ‖Γ t / ((t:ℂ)-z)‖ ≤ c⁻¹*(‖Γ t‖/t) := by
  rw [norm_div]
  calc
    _ ≤ ‖Γ t‖/(c*t) := div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hc ht) hb
    _ = _ := by field_simp

theorem cauchy_derivative_kernel_bound {Γ : ℝ → ℂ} {H c t : ℝ} {z : ℂ}
    (hH : 0<H) (hc : 0<c) (ht : H≤t) (hb : c*t ≤ ‖(t:ℂ)-z‖) :
    ‖Γ t / ((t:ℂ)-z)^2‖ ≤ (c^2*H)⁻¹*(‖Γ t‖/t) := by
  have htp : 0<t := hH.trans_le ht
  have hsq : c^2*H*t ≤ ‖(t:ℂ)-z‖^2 := by
    calc
      c^2*H*t ≤ c^2*t*t := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ht (sq_nonneg c)) htp.le
      _ = (c*t)^2 := by ring
      _ ≤ _ := pow_le_pow_left₀ (mul_pos hc htp).le hb 2
  rw [norm_div,norm_pow]
  calc
    _ ≤ ‖Γ t‖/(c^2*H*t) := div_le_div_of_nonneg_left (norm_nonneg _)
      (mul_pos (mul_pos (sq_pos_of_pos hc) hH) htp) hsq
    _ = _ := by field_simp

theorem integrable_cauchyIntegral {μ : Measure ℝ} {Γ : ℝ → ℂ} {H : ℝ} {z : ℂ}
    (hH : 0<H) (hz : z ∈ domain H) (hΓ : AEStronglyMeasurable Γ μ)
    (hsupp : ∀ᵐ t ∂μ, H≤t) (hint : Integrable (fun t => ‖Γ t‖/t) μ) :
    Integrable (fun t => Γ t / ((t:ℂ)-z)) μ := by
  obtain ⟨ε,hε,c,hc,hb⟩ := exists_cauchy_lower_bound hH hz
  have hm : AEStronglyMeasurable (fun t : ℝ => Γ t / ((t:ℂ)-z)) μ :=
    (hΓ.aemeasurable.div (Complex.continuous_ofReal.sub continuous_const).measurable.aemeasurable).aestronglyMeasurable
  apply (hint.const_mul c⁻¹).mono' hm
  filter_upwards [hsupp] with t ht
  exact cauchy_kernel_bound hc (hH.trans_le ht) (hb z (mem_ball_self hε) t ht)

theorem hasDerivAt_cauchyIntegral {μ : Measure ℝ} {Γ : ℝ → ℂ} {H : ℝ} {z : ℂ}
    (hH : 0<H) (hz : z ∈ domain H) (hΓ : AEStronglyMeasurable Γ μ)
    (hsupp : ∀ᵐ t ∂μ, H≤t) (hint : Integrable (fun t => ‖Γ t‖/t) μ) :
    HasDerivAt (cauchyIntegral μ Γ) (∫ t, Γ t / ((t:ℂ)-z)^2 ∂μ) z := by
  obtain ⟨ε,hε,c,hc,hb⟩ := exists_cauchy_lower_bound hH hz
  have hm : ∀ᶠ x : ℂ in 𝓝 z, AEStronglyMeasurable (fun t : ℝ => Γ t/((t:ℂ)-x)) μ :=
    Eventually.of_forall fun x => (hΓ.aemeasurable.div (Complex.continuous_ofReal.sub continuous_const).measurable.aemeasurable).aestronglyMeasurable
  have hdm : AEStronglyMeasurable (fun t : ℝ => Γ t/((t:ℂ)-z)^2) μ :=
    (hΓ.aemeasurable.div ((Complex.continuous_ofReal.sub continuous_const).pow 2).measurable.aemeasurable).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂μ, ∀ x∈ball z ε,
      ‖Γ t/((t:ℂ)-x)^2‖ ≤ (c^2*H)⁻¹*(‖Γ t‖/t) := by
    filter_upwards [hsupp] with t ht x hx
    exact cauchy_derivative_kernel_bound hH hc ht (hb x hx t ht)
  have hd : ∀ᵐ t ∂μ, ∀ x∈ball z ε,
      HasDerivAt (fun x : ℂ => Γ t/((t:ℂ)-x)) (Γ t/((t:ℂ)-x)^2) x := by
    filter_upwards [hsupp] with t ht x hx
    have hn : (t:ℂ)-x ≠ 0 := norm_pos_iff.mp ((mul_pos hc (hH.trans_le ht)).trans_le (hb x hx t ht))
    convert (hasDerivAt_const x (Γ t)).div ((hasDerivAt_id x).const_sub (t:ℂ)) hn using 1 <;> simp only [id_eq] <;> ring
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hm
    (integrable_cauchyIntegral hH hz hΓ hsupp hint) hdm hbound
    (hint.const_mul (c^2*H)⁻¹) hd).2

theorem analyticOnNhd_cauchyIntegral {μ : Measure ℝ} {Γ : ℝ → ℂ} {H : ℝ}
    (hH : 0<H) (hΓ : AEStronglyMeasurable Γ μ)
    (hsupp : ∀ᵐ t ∂μ, H≤t) (hint : Integrable (fun t => ‖Γ t‖/t) μ) :
    AnalyticOnNhd ℂ (cauchyIntegral μ Γ) (domain H) := by
  have hd : DifferentiableOn ℂ (cauchyIntegral μ Γ) (domain H) := by
    intro z hz
    exact (hasDerivAt_cauchyIntegral hH hz hΓ hsupp hint).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_domain H)

theorem eqOn_cauchy_of_real_axis {μ : Measure ℝ} {Γ : ℝ → ℂ} {F : ℂ → ℂ} {H : ℝ}
    (k : ℂ) (hH : 0<H) (hΓ : AEStronglyMeasurable Γ μ)
    (hsupp : ∀ᵐ t ∂μ, H≤t) (hint : Integrable (fun t => ‖Γ t‖/t) μ)
    (hF : DifferentiableOn ℂ F (domain H))
    (he : ∀ x : ℝ, x<H → F (x:ℂ)=k*cauchyIntegral μ Γ (x:ℂ)) :
    EqOn F (fun z => k*cauchyIntegral μ Γ z) (domain H) := by
  apply RealComplexification.eqOn_of_eqOn_real_slice
    (hF.analyticOnNhd (isOpen_domain H))
    (fun z hz => analyticAt_const.mul (analyticOnNhd_cauchyIntegral hH hΓ hsupp hint z hz))
    (isOpen_domain H) (isPreconnected_domain H) (r:=H-1) (Or.inl (by simp))
  intro x hx
  apply he x
  simpa [domain] using hx

end LeanVerification.SlitContour
