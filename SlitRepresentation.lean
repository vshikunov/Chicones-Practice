import LeanVerification.SlitTail

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.SlitContour

theorem LocalBankControl.upper {f : ℂ → ℂ} {a : ℝ} (h : LocalBankControl f a) :
    ∀ R > a, ∃ η > 0, ∃ b : ℝ → ℝ, IntervalIntegrable b volume a R ∧
      ∀ᵐ t, t ∈ Ioc a R → ∀ ε ∈ Ioo (0 : ℝ) η,
        ‖f ((t : ℂ) + ((1 : ℝ) * ε : ℝ) * Complex.I)‖ ≤ b t := by
  intro R hR
  obtain ⟨η, hη, b, hb, hbound⟩ := h R hR
  refine ⟨η, hη, b, hb, ?_⟩
  filter_upwards [hbound] with t ht htmem ε he
  simpa only [one_mul] using (ht htmem ε he).1

theorem LocalBankControl.lower {f : ℂ → ℂ} {a : ℝ} (h : LocalBankControl f a) :
    ∀ R > a, ∃ η > 0, ∃ b : ℝ → ℝ, IntervalIntegrable b volume a R ∧
      ∀ᵐ t, t ∈ Ioc a R → ∀ ε ∈ Ioo (0 : ℝ) η,
        ‖f ((t : ℂ) + ((-1 : ℝ) * ε : ℝ) * Complex.I)‖ ≤ b t := by
  intro R hR
  obtain ⟨η, hη, b, hb, hbound⟩ := h R hR
  refine ⟨η, hη, b, hb, ?_⟩
  filter_upwards [hbound] with t ht htmem ε he
  simpa only [neg_one_mul, Complex.ofReal_neg, neg_mul, one_mul, sub_eq_add_neg] using
    (ht htmem ε he).2

theorem banks_tendsto {f : ℂ → ℂ} {u l : ℝ → ℂ} {H a R z : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hza : z < a) (haR : a < R)
    (hcontrol : LocalBankControl f a)
    (hu : ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ => f ((t : ℂ) + ε * Complex.I))
      (𝓝[>] 0) (𝓝 (u t)))
    (hl : ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ => f ((t : ℂ) - ε * Complex.I))
      (𝓝[>] 0) (𝓝 (l t))) :
    Tendsto (banks (quotient f z) a R) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ t in a..R, (u t - l t) / ((t : ℂ) - z))) := by
  obtain ⟨ηu, hηu, bu, hbu, hboundu⟩ := hcontrol.upper R haR
  obtain ⟨ηl, hηl, bl, hbl, hboundl⟩ := hcontrol.lower R haR
  have hu' : ∀ᵐ t : ℝ, t ∈ Ioc a R → Tendsto
      (fun ε : ℝ => f ((t : ℂ) + ((1 : ℝ) * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 (u t)) := by
    filter_upwards [hu] with t ht htmem
    simpa only [one_mul] using ht
  have hl' : ∀ᵐ t : ℝ, t ∈ Ioc a R → Tendsto
      (fun ε : ℝ => f ((t : ℂ) + ((-1 : ℝ) * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 (l t)) := by
    filter_upwards [hl] with t ht htmem
    simpa only [neg_one_mul, Complex.ofReal_neg, neg_mul, one_mul, sub_eq_add_neg] using ht
  have htu := integral_bank_tendsto hf one_ne_zero hza haR.le hηu hbu hboundu hu'
  have htl := integral_bank_tendsto hf (neg_ne_zero.mpr one_ne_zero) hza haR.le hηl hbl hboundl hl'
  have hiu := integrable_bank_quotient hf one_ne_zero hza haR.le hηu hbu hboundu hu'
  have hil := integrable_bank_quotient hf (neg_ne_zero.mpr one_ne_zero) hza haR.le hηl hbl hboundl hl'
  have he : (∫ t in a..R, u t / ((t : ℂ) - z)) -
      (∫ t in a..R, l t / ((t : ℂ) - z)) =
        ∫ t in a..R, (u t - l t) / ((t : ℂ) - z) := by
    rw [← intervalIntegral.integral_sub hiu hil]
    apply intervalIntegral.integral_congr
    intro t ht
    exact (sub_div _ _ _).symm
  have hs := htu.sub htl
  rw [he] at hs
  change Tendsto (fun ε => banks (quotient f z) a R ε) (𝓝[>] (0 : ℝ)) _
  simpa only [banks, one_mul, neg_one_mul, Complex.ofReal_neg, neg_mul,
    sub_eq_add_neg] using hs

/-- The finite contour estimate survives the bank limit, with every
improper endpoint controlled by the local bank majorant. -/
theorem cauchy_truncation_error {f : ℂ → ℂ} {u l : ℝ → ℂ}
    {H a R z C α R₀ : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hza : z < a) (haH : a < H)
    (haR : a < R) (hC : 0 ≤ C) (hα : 0 < α) (hR : 0 < R)
    (hRH : -R < H) (hR₀ : R₀ ≤ R) (hz : 2 * |z| ≤ R)
    (hdecay : ∀ w ∈ domain H, R₀ ≤ ‖w‖ → ‖f w‖ ≤ C * ‖w‖ ^ (-α))
    (hcontrol : LocalBankControl f a)
    (hu : ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ => f ((t : ℂ) + ε * Complex.I))
      (𝓝[>] 0) (𝓝 (u t)))
    (hl : ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ => f ((t : ℂ) - ε * Complex.I))
      (𝓝[>] 0) (𝓝 (l t))) :
    ‖2 * (Real.pi : ℂ) * Complex.I * f z -
      ∫ t in a..R, (u t - l t) / ((t : ℂ) - z)‖ ≤ 16 * C * R ^ (-α) := by
  have hLz : -R < z := by nlinarith [neg_abs_le z, abs_nonneg z]
  have hbank := banks_tendsto hf hza haR hcontrol hu hl
  have hgap : Tendsto (gap (quotient f z) a) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (physical_gap_tendsto_zero hf haH hza.ne').mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun ε : ℝ => ‖2 * (Real.pi : ℂ) * Complex.I * f z -
      (banks (quotient f z) a R ε + gap (quotient f z) a ε)‖) (𝓝[>] 0)
      (𝓝 ‖2 * (Real.pi : ℂ) * Complex.I * f z -
        ∫ t in a..R, (u t - l t) / ((t : ℂ) - z)‖) := by
    simpa only [add_zero] using (tendsto_const_nhds.sub (hbank.add hgap)).norm
  apply le_of_tendsto ht
  filter_upwards [Ioo_mem_nhdsGT hR] with ε he
  have heq := finite_contour hLz hza haH haR he.1 he.2.le hf
  have heq' : 2 * (Real.pi : ℂ) * Complex.I * f z -
      (banks (quotient f z) a R ε + gap (quotient f z) a ε) =
        outer (quotient f z) (-R) R R ε := by linear_combination -heq
  rw [heq']
  exact norm_outer_quotient_le hC hα hR hRH hR₀ hz he.1 he.2.le hdecay

/-- The slit representation is obtained from the actual finite contours,
bank limits, and power-decay estimate. The full improper integrability is
proved from those data, not assumed as a representation hypothesis. -/
theorem real_cauchy_representation {f : ℂ → ℂ} {u l : ℝ → ℂ}
    {H a z C α R₀ : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (hza : z < a) (haH : a < H)
    (hC : 0 ≤ C) (hα : 0 < α)
    (hdecay : ∀ w ∈ domain H, R₀ ≤ ‖w‖ → ‖f w‖ ≤ C * ‖w‖ ^ (-α))
    (hcontrol : LocalBankControl f a)
    (hu : ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ => f ((t : ℂ) + ε * Complex.I))
      (𝓝[>] 0) (𝓝 (u t)))
    (hl : ∀ᵐ t : ℝ, Tendsto (fun ε : ℝ => f ((t : ℂ) - ε * Complex.I))
      (𝓝[>] 0) (𝓝 (l t))) :
    IntegrableOn (fun t => (u t - l t) / ((t : ℂ) - z)) (Ioi a) ∧
      (∫ t in Ioi a, (u t - l t) / ((t : ℂ) - z)) =
        2 * (Real.pi : ℂ) * Complex.I * f z := by
  have hu' : ∀ᵐ t : ℝ, Tendsto
      (fun ε : ℝ => f ((t : ℂ) + ((1 : ℝ) * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 (u t)) := by simpa only [one_mul] using hu
  have hl' : ∀ᵐ t : ℝ, Tendsto
      (fun ε : ℝ => f ((t : ℂ) + ((-1 : ℝ) * ε : ℝ) * Complex.I))
      (𝓝[>] 0) (𝓝 (l t)) := by
    simpa only [neg_one_mul, Complex.ofReal_neg, neg_mul, one_mul, sub_eq_add_neg] using hl
  have hiu := integrableOn_bank_quotient hf one_ne_zero hC hα hza hdecay hu' hcontrol.upper
  have hil := integrableOn_bank_quotient hf (neg_ne_zero.mpr one_ne_zero) hC hα hza
    hdecay hl' hcontrol.lower
  have hi : IntegrableOn (fun t => (u t - l t) / ((t : ℂ) - z)) (Ioi a) := by
    simpa only [sub_div] using hiu.sub hil
  refine ⟨hi, ?_⟩
  have ht := intervalIntegral_tendsto_integral_Ioi a hi tendsto_id
  have hnorm : Tendsto (fun R : ℝ => ‖2 * (Real.pi : ℂ) * Complex.I * f z -
      ∫ t in a..R, (u t - l t) / ((t : ℂ) - z)‖) atTop
      (𝓝 ‖2 * (Real.pi : ℂ) * Complex.I * f z -
        ∫ t in Ioi a, (u t - l t) / ((t : ℂ) - z)‖) :=
    (tendsto_const_nhds.sub ht).norm
  have hbound : ∀ᶠ R : ℝ in atTop,
      ‖2 * (Real.pi : ℂ) * Complex.I * f z -
        ∫ t in a..R, (u t - l t) / ((t : ℂ) - z)‖ ≤ 16 * C * R ^ (-α) := by
    filter_upwards [eventually_gt_atTop a, eventually_gt_atTop (0 : ℝ),
      eventually_gt_atTop (-H), eventually_ge_atTop R₀,
      eventually_ge_atTop (2 * |z|)] with R haR hR hRH hR₀ hzR
    exact cauchy_truncation_error hf hza haH haR hC hα hR (by linarith)
      hR₀ hzR hdecay hcontrol hu hl
  have hz0 : ‖2 * (Real.pi : ℂ) * Complex.I * f z -
      ∫ t in Ioi a, (u t - l t) / ((t : ℂ) - z)‖ ≤ 0 :=
    le_of_tendsto_of_tendsto hnorm (outer_bound_tendsto_zero C hα) hbound
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz0 (norm_nonneg _)))).symm

end LeanVerification.SlitContour
