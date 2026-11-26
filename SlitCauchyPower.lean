import LeanVerification.SlitCauchyHolomorphic

/-!
# Complex-density power kernels on the entire right-cut plane

The original weighted absolute mass at exponent beta controls every raised
kernel on a support bounded away from zero. All complex derivatives have the
positive rising-factorial coefficient, because the kernel is (t-z)^(-beta).
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators

namespace LeanVerification.SlitContour
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def powerKernel (Γ : ℝ → ℂ) (β : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Γ t*((t : ℂ)-z)^((-β : ℝ) : ℂ)

def powerIntegral (μ : Measure ℝ) (Γ : ℝ → ℂ) (β : ℝ) (z : ℂ) : ℂ :=
  ∫ t, powerKernel Γ β z t ∂μ

theorem right_kernel_mem_slitPlane {H t : ℝ} {z : ℂ}
    (hz : z ∈ domain H) (ht : H≤t) : (t : ℂ)-z ∈ Complex.slitPlane := by
  rcases hz with hz | hz
  · left
    simp only [Complex.sub_re,Complex.ofReal_re]
    linarith
  · right
    simpa only [Complex.sub_im,Complex.ofReal_im,zero_sub,neg_ne_zero] using hz

theorem measurable_powerKernel_factor (β : ℝ) (z : ℂ) :
    Measurable (fun t : ℝ => ((t : ℂ)-z)^((-β : ℝ) : ℂ)) := by
  have hm : Measurable (fun t : ℝ => (t : ℂ)-z) :=
    Complex.continuous_ofReal.measurable.sub measurable_const
  simp only [Complex.cpow_def]
  apply Measurable.ite (measurableSet_eq_fun hm measurable_const) measurable_const
  exact ((Complex.measurable_log.comp hm).mul_const _).cexp

theorem aestronglyMeasurable_powerKernel {μ : Measure ℝ} {Γ : ℝ → ℂ}
    (hΓ : AEStronglyMeasurable Γ μ) (β : ℝ) (z : ℂ) :
    AEStronglyMeasurable (powerKernel Γ β z) μ :=
  (hΓ.aemeasurable.mul (measurable_powerKernel_factor β z).aemeasurable).aestronglyMeasurable

theorem norm_powerKernel (Γ : ℝ → ℂ) (β : ℝ) (z : ℂ) (t : ℝ) :
    ‖powerKernel Γ β z t‖=‖Γ t‖*‖(t : ℂ)-z‖^(-β) := by
  rw [powerKernel,norm_mul,Complex.norm_cpow_real]

theorem powerKernel_bound {Γ : ℝ → ℂ} {β c t : ℝ} {z : ℂ}
    (hβ : 0≤β) (hc : 0<c) (ht : 0<t) (hb : c*t≤‖(t : ℂ)-z‖) :
    ‖powerKernel Γ β z t‖≤c^(-β)*(‖Γ t‖*t^(-β)) := by
  rw [norm_powerKernel]
  have hk := Real.rpow_le_rpow_of_nonpos (mul_pos hc ht) hb (neg_nonpos.mpr hβ)
  rw [Real.mul_rpow hc.le ht.le] at hk
  calc
    _ ≤ ‖Γ t‖*(c^(-β)*t^(-β)) := mul_le_mul_of_nonneg_left hk (norm_nonneg _)
    _ = _ := by ring

/-- Higher inverse powers require no new moment: the lower support endpoint
converts their mass to the original mass at exponent beta. -/
theorem power_weight_bound {Γ : ℝ → ℂ} {H t β γ : ℝ}
    (hH : 0<H) (ht : H≤t) (hβγ : β≤γ) :
    ‖Γ t‖*t^(-γ)≤H^(β-γ)*(‖Γ t‖*t^(-β)) := by
  have htp : 0<t := hH.trans_le ht
  have hpow : t^(-γ)=t^(-β)*t^(β-γ) := by
    rw [← Real.rpow_add htp]
    congr 1
    ring
  rw [hpow]
  have hm := Real.rpow_le_rpow_of_nonpos hH ht (sub_nonpos.mpr hβγ)
  calc
    ‖Γ t‖*(t^(-β)*t^(β-γ)) ≤ ‖Γ t‖*(t^(-β)*H^(β-γ)) := by
      gcongr
    _ = _ := by ring

theorem integrable_power_weight_mono {μ : Measure ℝ} {Γ : ℝ → ℂ} {H β γ : ℝ}
    (hH : 0<H) (hΓ : AEStronglyMeasurable Γ μ) (hsupp : ∀ᵐ t ∂μ,H≤t)
    (hβγ : β≤γ) (hint : Integrable (fun t => ‖Γ t‖*t^(-β)) μ) :
    Integrable (fun t => ‖Γ t‖*t^(-γ)) μ := by
  apply (hint.const_mul (H^(β-γ))).mono'
    (hΓ.norm.mul (measurable_id.pow_const (-γ)).aestronglyMeasurable)
  filter_upwards [hsupp] with t ht
  dsimp only [Pi.mul_apply,id_eq]
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hH.trans_le ht).le _))]
  exact power_weight_bound hH ht hβγ

theorem integrable_powerKernel {μ : Measure ℝ} {Γ : ℝ → ℂ} {H β : ℝ} {z : ℂ}
    (hH : 0<H) (hβ : 0≤β) (hz : z ∈ domain H) (hΓ : AEStronglyMeasurable Γ μ)
    (hsupp : ∀ᵐ t ∂μ,H≤t) (hint : Integrable (fun t => ‖Γ t‖*t^(-β)) μ) :
    Integrable (powerKernel Γ β z) μ := by
  obtain ⟨ε,hε,c,hc,hb⟩ := exists_cauchy_lower_bound hH hz
  apply (hint.const_mul (c^(-β))).mono' (aestronglyMeasurable_powerKernel hΓ β z)
  filter_upwards [hsupp] with t ht
  exact powerKernel_bound hβ hc (hH.trans_le ht) (hb z (mem_ball_self hε) t ht)

theorem hasDerivAt_powerKernel (Γ : ℝ → ℂ) (β : ℝ) {z : ℂ} {t : ℝ}
    (hz : (t : ℂ)-z ∈ Complex.slitPlane) :
    HasDerivAt (fun x => powerKernel Γ β x t)
      ((β : ℂ)*powerKernel Γ (β+1) z t) z := by
  have hd := (((hasDerivAt_id z).const_sub (t : ℂ)).cpow_const
    (c := ((-β : ℝ) : ℂ)) hz).const_mul (Γ t)
  convert hd using 1
  simp only [powerKernel,id_eq,neg_mul,mul_neg,mul_one,neg_neg]
  have he : ((-(β+1) : ℝ) : ℂ)=((-β : ℝ) : ℂ)-1 := by push_cast; ring
  rw [he]
  push_cast
  ring

/-- Differentiation on the full right-cut plane uses only the original
weighted absolute mass, even for arbitrary complex densities. -/
theorem hasDerivAt_powerIntegral {μ : Measure ℝ} {Γ : ℝ → ℂ} {H β : ℝ} {z : ℂ}
    (hH : 0<H) (hβ : 0<β) (hz : z ∈ domain H) (hΓ : AEStronglyMeasurable Γ μ)
    (hsupp : ∀ᵐ t ∂μ,H≤t) (hint : Integrable (fun t => ‖Γ t‖*t^(-β)) μ) :
    HasDerivAt (powerIntegral μ Γ β) ((β : ℂ)*powerIntegral μ Γ (β+1) z) z := by
  obtain ⟨a,ha,c,hc,hb⟩ := exists_cauchy_lower_bound hH hz
  obtain ⟨b,hbpos,hdom⟩ := Metric.mem_nhds_iff.mp ((isOpen_domain H).mem_nhds hz)
  let ε := min a b
  have hε : 0<ε := lt_min ha hbpos
  have hmeas : ∀ᶠ x : ℂ in 𝓝 z, AEStronglyMeasurable (powerKernel Γ β x) μ :=
    Eventually.of_forall fun x => aestronglyMeasurable_powerKernel hΓ β x
  have hdm : AEStronglyMeasurable (fun t => (β : ℂ)*powerKernel Γ (β+1) z t) μ :=
    (aestronglyMeasurable_powerKernel hΓ (β+1) z).const_mul _
  have hbound : ∀ᵐ t ∂μ, ∀ x∈ball z ε,
      ‖(β : ℂ)*powerKernel Γ (β+1) x t‖≤
        (β*c^(-(β+1))*H^(-1 : ℝ))*(‖Γ t‖*t^(-β)) := by
    filter_upwards [hsupp] with t ht x hx
    have hxa : x ∈ ball z a := (ball_subset_ball (min_le_left _ _)) hx
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hβ.le]
    have hk := powerKernel_bound (Γ := Γ) (by linarith : 0≤β+1) hc (hH.trans_le ht) (hb x hxa t ht)
    have hw := power_weight_bound (Γ := Γ) (β := β) (γ := β+1) hH ht (by linarith)
    have he : β-(β+1)=(-1 : ℝ) := by ring
    rw [he] at hw
    calc
      _ ≤ β*(c^(-(β+1))*(‖Γ t‖*t^(-(β+1)))) :=
        mul_le_mul_of_nonneg_left hk hβ.le
      _ ≤ β*(c^(-(β+1))*(H^(-1 : ℝ)*(‖Γ t‖*t^(-β)))) := by gcongr
      _ = _ := by ring
  have hd : ∀ᵐ t ∂μ, ∀ x∈ball z ε,
      HasDerivAt (fun x => powerKernel Γ β x t) ((β : ℂ)*powerKernel Γ (β+1) x t) x := by
    filter_upwards [hsupp] with t ht x hx
    exact hasDerivAt_powerKernel Γ β (right_kernel_mem_slitPlane
      (hdom ((ball_subset_ball (min_le_right _ _)) hx)) ht)
  have he := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hmeas
    (integrable_powerKernel hH hβ.le hz hΓ hsupp hint) hdm hbound
    (hint.const_mul (β*c^(-(β+1))*H^(-1 : ℝ))) hd).2
  simpa only [powerIntegral,integral_const_mul] using he

theorem analyticOnNhd_powerIntegral {μ : Measure ℝ} {Γ : ℝ → ℂ} {H β : ℝ}
    (hH : 0<H) (hβ : 0<β) (hΓ : AEStronglyMeasurable Γ μ)
    (hsupp : ∀ᵐ t ∂μ,H≤t) (hint : Integrable (fun t => ‖Γ t‖*t^(-β)) μ) :
    AnalyticOnNhd ℂ (powerIntegral μ Γ β) (domain H) := by
  have hd : DifferentiableOn ℂ (powerIntegral μ Γ β) (domain H) := by
    intro z hz
    exact (hasDerivAt_powerIntegral hH hβ hz hΓ hsupp hint).differentiableAt.differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_domain H)

/-- Every derivative is the raised power kernel with a positive rising-factor
coefficient. There is no alternating sign for the kernel `(t-z)^(-beta)`. -/
theorem iteratedDeriv_powerIntegral {μ : Measure ℝ} {Γ : ℝ → ℂ} {H β : ℝ}
    (hH : 0<H) (hβ : 0<β) (hΓ : AEStronglyMeasurable Γ μ)
    (hsupp : ∀ᵐ t ∂μ,H≤t) (hint : Integrable (fun t => ‖Γ t‖*t^(-β)) μ) (k : ℕ) :
    ∀ z∈domain H, iteratedDeriv k (powerIntegral μ Γ β) z=
      (Cauchy.risingFactor β k : ℂ)*powerIntegral μ Γ (β+k) z := by
  induction k with
  | zero =>
      intro z hz
      simp [Cauchy.risingFactor]
  | succ k ih =>
      intro z hz
      rw [iteratedDeriv_succ]
      have he : iteratedDeriv k (powerIntegral μ Γ β) =ᶠ[𝓝 z]
          fun w => (Cauchy.risingFactor β k : ℂ)*powerIntegral μ Γ (β+k) w := by
        filter_upwards [(isOpen_domain H).mem_nhds hz] with w hw
        exact ih w hw
      rw [he.deriv_eq]
      have hki := integrable_power_weight_mono hH hΓ hsupp
        (show β≤β+(k : ℝ) by exact le_add_of_nonneg_right (Nat.cast_nonneg k)) hint
      have hd := (hasDerivAt_powerIntegral hH (by positivity : 0<β+(k : ℝ)) hz hΓ hsupp hki).const_mul
        (Cauchy.risingFactor β k : ℂ)
      rw [hd.deriv,Cauchy.risingFactor_succ]
      have hx : β+(k : ℝ)+1=β+((k+1 : ℕ) : ℝ) := by push_cast; ring
      rw [hx]
      push_cast
      ring

theorem powerIntegral_ofReal {μ : Measure ℝ} {Γ : ℝ → ℂ} {H β x : ℝ}
    (hx : x<H) (hsupp : ∀ᵐ t ∂μ,H≤t) :
    powerIntegral μ Γ β (x : ℂ)=∫ t, Γ t*((t-x)^(-β) : ℝ) ∂μ := by
  unfold powerIntegral
  apply integral_congr_ae
  filter_upwards [hsupp] with t ht
  dsimp only [powerKernel]
  rw [← Complex.ofReal_sub,← Complex.ofReal_cpow (by linarith : 0≤t-x)]

/-- A real-axis representation identifies the same power integral throughout
the entire connected cut domain. -/
theorem eqOn_powerIntegral_of_real_axis {μ : Measure ℝ} {Γ : ℝ → ℂ} {F : ℂ → ℂ} {H β : ℝ}
    (c : ℂ) (hH : 0<H) (hβ : 0<β) (hΓ : AEStronglyMeasurable Γ μ)
    (hsupp : ∀ᵐ t ∂μ,H≤t) (hint : Integrable (fun t => ‖Γ t‖*t^(-β)) μ)
    (hF : DifferentiableOn ℂ F (domain H))
    (he : ∀ x : ℝ, x<H → F (x : ℂ)=c*powerIntegral μ Γ β (x : ℂ)) :
    EqOn F (fun z => c*powerIntegral μ Γ β z) (domain H) := by
  apply RealComplexification.eqOn_of_eqOn_real_slice
    (hF.analyticOnNhd (isOpen_domain H))
    (fun z hz => analyticAt_const.mul (analyticOnNhd_powerIntegral hH hβ hΓ hsupp hint z hz))
    (isOpen_domain H) (isPreconnected_domain H) (r := H-1) (Or.inl (by simp))
  intro x hx
  apply he x
  simpa [domain] using hx

end LeanVerification.SlitContour
