import LeanVerification.Loud.CompactAnalyticIntegral
import LeanVerification.AnalyticMultiplicity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Tactic.LinearCombination

/-!
Regular angular forms of the half-raised and twice-raised Abel transforms.
Differentiation is performed on a fixed compact angular interval. The
singular inverse-square-root kernel is never differentiated.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology

namespace LeanVerification.RaisedAbel

def moment (g : ℝ → ℝ) (k : ℕ) (h : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2,
    g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ (2 * k)

def half (g : ℝ → ℝ) (h : ℝ) : ℝ := 2 * h ^ 2 * moment g 1 h

def raised (g : ℝ → ℝ) (h : ℝ) : ℝ := 2 * h ^ 3 * moment g 2 h

theorem sin_sq_energy_mem {H h : ℝ} (hh : h ∈ Icc 0 H) (θ : ℝ) :
    h * Real.sin θ ^ 2 ∈ Icc 0 H := by
  have hs : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  exact ⟨mul_nonneg hh.1 (sq_nonneg _),
    (mul_le_of_le_one_right hh.1 hs).trans hh.2⟩

theorem continuous_angle {g : ℝ → ℝ} {H h : ℝ}
    (hg : ContinuousOn g (Icc 0 H)) (hh : h ∈ Icc 0 H) :
    Continuous (fun θ => g (h * Real.sin θ ^ 2)) := by
  exact hg.comp_continuous (continuous_const.mul (Real.continuous_sin.pow 2))
    (fun θ => sin_sq_energy_mem hh θ)

theorem analyticAt_moment {g : ℝ → ℝ} {H h : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Icc 0 H) (k : ℕ) :
    AnalyticAt ℝ (moment g k) h := by
  let f : (Loud.PeriodParameterSpace × ℝ) → ℝ := fun z =>
    g (z.1.2 * Real.sin z.2 ^ 2) * Real.sin z.2 ^ 2 * Real.cos z.2 ^ (2 * k)
  have ha : ∀ θ ∈ Icc (0 : ℝ) (Real.pi / 2),
      AnalyticAt ℝ f (((0, 0), h), θ) := by
    intro θ _
    have hi : AnalyticAt ℝ
        (fun z : Loud.PeriodParameterSpace × ℝ => z.1.2 * Real.sin z.2 ^ 2)
        (((0, 0), h), θ) :=
      (analyticAt_snd.comp analyticAt_fst).mul
        (((Loud.analyticAt_real_sin θ).comp_of_eq analyticAt_snd rfl).pow 2)
    have hs : AnalyticAt ℝ
        (fun z : Loud.PeriodParameterSpace × ℝ => Real.sin z.2 ^ 2)
        (((0, 0), h), θ) :=
      ((Loud.analyticAt_real_sin θ).comp_of_eq analyticAt_snd rfl).pow 2
    have hc : AnalyticAt ℝ
        (fun z : Loud.PeriodParameterSpace × ℝ => Real.cos z.2 ^ (2 * k))
        (((0, 0), h), θ) := by
      have hcos : AnalyticAt ℝ Real.cos θ := by
        have he : AnalyticAt ℂ Complex.cos (θ : ℂ) := Complex.differentiable_cos.analyticAt _
        simpa only [← Complex.ofReal_cos, Complex.ofReal_re] using he.re_ofReal
      exact (hcos.comp_of_eq analyticAt_snd rfl).pow _
    exact (((hg _ (sin_sq_energy_mem hh θ)).comp_of_eq hi rfl).mul hs).mul hc
  have hi := (Loud.analyticAt_setIntegral_of_joint_on_compact
    (f := f) (x₀ := ((0, 0), h)) (K := Icc (0 : ℝ) (Real.pi / 2))
    (S := Ioc (0 : ℝ) (Real.pi / 2)) isCompact_Icc ha
    measurableSet_Ioc Ioc_subset_Icc_self).1.curry_right
  change AnalyticAt ℝ (fun h => ∫ θ in (0 : ℝ)..Real.pi / 2,
    g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ (2 * k)) h
  simpa only [f, intervalIntegral.integral_of_le (by positivity :
    (0 : ℝ) ≤ Real.pi / 2)] using hi

theorem analyticAt_half {g : ℝ → ℝ} {H h : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Icc 0 H) :
    AnalyticAt ℝ (half g) h :=
  (analyticAt_const.mul (analyticAt_id.pow 2)).mul (analyticAt_moment hg hh 1)

theorem analyticAt_raised {g : ℝ → ℝ} {H h : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Icc 0 H) :
    AnalyticAt ℝ (raised g) h :=
  (analyticAt_const.mul (analyticAt_id.pow 3)).mul (analyticAt_moment hg hh 2)

theorem hasDerivAt_moment {g : ℝ → ℝ} {H h : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H) (k : ℕ) :
    HasDerivAt (moment g k)
      (∫ θ in (0 : ℝ)..Real.pi / 2,
        deriv g (h * Real.sin θ ^ 2) * Real.sin θ ^ 4 * Real.cos θ ^ (2 * k)) h := by
  have hgc : ContinuousOn g (Icc 0 H) := fun u hu => (hg u hu).continuousAt.continuousWithinAt
  have hdc : ContinuousOn (deriv g) (Icc 0 H) := fun u hu =>
    (hg u hu).deriv.continuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := isCompact_Icc.bddAbove_image hdc.norm
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (isOpen_Ioo.mem_nhds hh)
  let f := fun r θ => g (r * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ (2 * k)
  let f' := fun r θ => deriv g (r * Real.sin θ ^ 2) * Real.sin θ ^ 4 * Real.cos θ ^ (2 * k)
  have hcf : ∀ r ∈ Icc 0 H, Continuous (f r) := by
    intro r hr
    exact ((continuous_angle hgc hr).mul (Real.continuous_sin.pow 2)).mul
      (Real.continuous_cos.pow _)
  have hcf' : ∀ r ∈ Icc 0 H, Continuous (f' r) := by
    intro r hr
    exact ((continuous_angle hdc hr).mul (Real.continuous_sin.pow 4)).mul
      (Real.continuous_cos.pow _)
  have hm : ∀ᶠ r in 𝓝 h, AEStronglyMeasurable (f r)
      (volume.restrict (uIoc (0 : ℝ) (Real.pi / 2))) := by
    filter_upwards [Metric.ball_mem_nhds h hε] with r hr
    exact (hcf r (Ioo_subset_Icc_self (hsub hr))).aestronglyMeasurable
  have hb : ∀ᵐ θ : ℝ, θ ∈ uIoc (0 : ℝ) (Real.pi / 2) →
      ∀ r ∈ Metric.ball h ε, ‖f' r θ‖ ≤ M := by
    apply Filter.Eventually.of_forall
    intro θ _ r hr
    have hm' := hM (mem_image_of_mem _ (sin_sq_energy_mem
      (Ioo_subset_Icc_self (hsub hr)) θ))
    have hs : ‖Real.sin θ‖ ^ 4 ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (Real.abs_sin_le_one θ)
    have hc : ‖Real.cos θ‖ ^ (2 * k) ≤ 1 :=
      pow_le_one₀ (norm_nonneg _) (Real.abs_cos_le_one θ)
    change ‖deriv g (r * Real.sin θ ^ 2) * Real.sin θ ^ 4 * Real.cos θ ^ (2 * k)‖ ≤ M
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    exact (mul_le_of_le_one_right (by positivity) hc).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hs).trans hm')
  have hd : ∀ᵐ θ : ℝ, θ ∈ uIoc (0 : ℝ) (Real.pi / 2) →
      ∀ r ∈ Metric.ball h ε, HasDerivAt (fun r => f r θ) (f' r θ) r := by
    apply Filter.Eventually.of_forall
    intro θ _ r hr
    have hi := (hg _ (sin_sq_energy_mem (Ioo_subset_Icc_self (hsub hr)) θ)).differentiableAt.hasDerivAt
    have he := ((hi.comp r ((hasDerivAt_id r).mul_const (Real.sin θ ^ 2))).mul_const
      (Real.sin θ ^ 2)).mul_const (Real.cos θ ^ (2 * k))
    convert he using 1 <;> dsimp [f, f'] <;> ring
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hε hm
    ((hcf h (Ioo_subset_Icc_self hh)).intervalIntegrable _ _)
    (hcf' h (Ioo_subset_Icc_self hh)).aestronglyMeasurable hb
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 (Real.pi / 2)) hd).2

theorem half_angular_integration_by_parts {g : ℝ → ℝ} {H h : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Icc 0 H) :
    2 * h * (∫ θ in (0 : ℝ)..Real.pi / 2,
      deriv g (h * Real.sin θ ^ 2) * Real.sin θ ^ 4 * Real.cos θ ^ 2) +
      4 * moment g 1 h - moment g 0 h = 0 := by
  let p := fun θ => g (h * Real.sin θ ^ 2) * Real.sin θ ^ 3 * Real.cos θ
  let d := fun θ => 2 * h *
      (deriv g (h * Real.sin θ ^ 2) * Real.sin θ ^ 4 * Real.cos θ ^ 2) +
    4 * (g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ 2) -
      g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2
  have hd : ∀ θ, HasDerivAt p (d θ) θ := by
    intro θ
    have hgd := (hg _ (sin_sq_energy_mem hh θ)).differentiableAt.hasDerivAt
    have hi := ((Real.hasDerivAt_sin θ).pow 2).const_mul h
    have hp := (((hgd.comp θ hi).mul ((Real.hasDerivAt_sin θ).pow 3)).mul
      (Real.hasDerivAt_cos θ))
    apply hp.congr_deriv
    simp only [d, Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub]
    linear_combination
      -(g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2) * Real.sin_sq_add_cos_sq θ
  have hc : Continuous (fun θ => g (h * Real.sin θ ^ 2)) :=
    continuous_angle (fun v hv => (hg v hv).continuousAt.continuousWithinAt) hh
  have hdc : Continuous (fun θ => deriv g (h * Real.sin θ ^ 2)) :=
    continuous_angle (fun v hv => (hg v hv).deriv.continuousAt.continuousWithinAt) hh
  have hci : Continuous (fun θ =>
      deriv g (h * Real.sin θ ^ 2) * Real.sin θ ^ 4 * Real.cos θ ^ 2) :=
    (hdc.mul (Real.continuous_sin.pow 4)).mul (Real.continuous_cos.pow 2)
  have hc1 : Continuous (fun θ =>
      g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ 2) :=
    (hc.mul (Real.continuous_sin.pow 2)).mul (Real.continuous_cos.pow 2)
  have hc0 : Continuous (fun θ => g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2) :=
    hc.mul (Real.continuous_sin.pow 2)
  have hdd : Continuous d := ((continuous_const.mul hci).add
    (continuous_const.mul hc1)).sub hc0
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi / 2) (fun θ _ => hd θ)
      (hdd.intervalIntegrable _ _)
  simp only [p, Real.sin_zero, zero_pow (by norm_num : 3 ≠ 0), mul_zero,
    Real.cos_pi_div_two, zero_sub, zero_mul, neg_zero] at he
  dsimp only [d] at he
  rw [intervalIntegral.integral_sub
    (((continuous_const.mul hci).add (continuous_const.mul hc1)).intervalIntegrable _ _)
    (hc0.intervalIntegrable _ _),
    intervalIntegral.integral_add ((continuous_const.mul hci).intervalIntegrable _ _)
      ((continuous_const.mul hc1).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at he
  simpa only [moment, Nat.mul_one, Nat.mul_zero, pow_zero, mul_one] using he

theorem raised_angular_integration_by_parts {g : ℝ → ℝ} {H h : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Icc 0 H) :
    2 * h * (∫ θ in (0 : ℝ)..Real.pi / 2,
      deriv g (h * Real.sin θ ^ 2) * Real.sin θ ^ 4 * Real.cos θ ^ 4) +
      6 * moment g 2 h - 3 * moment g 1 h = 0 := by
  let p := fun θ => g (h * Real.sin θ ^ 2) * Real.sin θ ^ 3 * Real.cos θ ^ 3
  let d := fun θ => 2 * h *
      (deriv g (h * Real.sin θ ^ 2) * Real.sin θ ^ 4 * Real.cos θ ^ 4) +
    6 * (g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ 4) -
      3 * (g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ 2)
  have hd : ∀ θ, HasDerivAt p (d θ) θ := by
    intro θ
    have hgd := (hg _ (sin_sq_energy_mem hh θ)).differentiableAt.hasDerivAt
    have hi := ((Real.hasDerivAt_sin θ).pow 2).const_mul h
    have hp := (((hgd.comp θ hi).mul ((Real.hasDerivAt_sin θ).pow 3)).mul
      ((Real.hasDerivAt_cos θ).pow 3))
    apply hp.congr_deriv
    simp only [d, Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub]
    linear_combination
      -(3 * g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ 2) *
        Real.sin_sq_add_cos_sq θ
  have hc : Continuous (fun θ => g (h * Real.sin θ ^ 2)) :=
    continuous_angle (fun v hv => (hg v hv).continuousAt.continuousWithinAt) hh
  have hdc : Continuous (fun θ => deriv g (h * Real.sin θ ^ 2)) :=
    continuous_angle (fun v hv => (hg v hv).deriv.continuousAt.continuousWithinAt) hh
  have hci : Continuous (fun θ =>
      deriv g (h * Real.sin θ ^ 2) * Real.sin θ ^ 4 * Real.cos θ ^ 4) :=
    (hdc.mul (Real.continuous_sin.pow 4)).mul (Real.continuous_cos.pow 4)
  have hc2 : Continuous (fun θ =>
      g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ 4) :=
    (hc.mul (Real.continuous_sin.pow 2)).mul (Real.continuous_cos.pow 4)
  have hc1 : Continuous (fun θ =>
      g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ 2) :=
    (hc.mul (Real.continuous_sin.pow 2)).mul (Real.continuous_cos.pow 2)
  have hdd : Continuous d := ((continuous_const.mul hci).add
    (continuous_const.mul hc2)).sub (continuous_const.mul hc1)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi / 2) (fun θ _ => hd θ)
      (hdd.intervalIntegrable _ _)
  simp only [p, Real.sin_zero, zero_pow (by norm_num : 3 ≠ 0), mul_zero,
    Real.cos_pi_div_two, zero_sub, zero_mul, neg_zero] at he
  dsimp only [d] at he
  rw [intervalIntegral.integral_sub
    (((continuous_const.mul hci).add (continuous_const.mul hc2)).intervalIntegrable _ _)
    ((continuous_const.mul hc1).intervalIntegrable _ _),
    intervalIntegral.integral_add ((continuous_const.mul hci).intervalIntegrable _ _)
      ((continuous_const.mul hc2).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at he
  simpa only [moment, Nat.mul_one, show 2 * 2 = 4 by norm_num] using he

theorem hasDerivAt_half {g : ℝ → ℝ} {H h : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H) :
    HasDerivAt (half g) (h * moment g 0 h) h := by
  have hd := (((hasDerivAt_id h).pow 2).const_mul 2).mul (hasDerivAt_moment hg hh 1)
  apply hd.congr_deriv
  have he := half_angular_integration_by_parts hg (Ioo_subset_Icc_self hh)
  norm_num
  linear_combination h * he

theorem hasDerivAt_raised {g : ℝ → ℝ} {H h : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H) :
    HasDerivAt (raised g) ((3 / 2 : ℝ) * half g h) h := by
  have hd := (((hasDerivAt_id h).pow 3).const_mul 2).mul (hasDerivAt_moment hg hh 2)
  apply hd.congr_deriv
  have he := raised_angular_integration_by_parts hg (Ioo_subset_Icc_self hh)
  simp only [half, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat, mul_one, id_eq]
  linear_combination h ^ 2 * he

theorem raised_eq_energy_integral {g : ℝ → ℝ} {H h : ℝ}
    (hg : ContinuousOn g (Icc 0 H)) (hh : h ∈ Ioo 0 H) :
    raised g h = ∫ v in (0 : ℝ)..h,
      (Real.sqrt v * g v) * (h - v) * Real.sqrt (h - v) := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have himage : (fun θ : ℝ => h * Real.sin θ ^ 2) '' uIcc 0 (Real.pi / 2) ⊆ Icc 0 h := by
    rintro _ ⟨θ, _, rfl⟩
    exact sin_sq_energy_mem ⟨hh.1.le, le_rfl⟩ θ
  have hgc : ContinuousOn (fun v : ℝ => (Real.sqrt v * g v) * (h - v) * Real.sqrt (h - v))
      (Icc 0 h) := by
    exact (((Real.continuous_sqrt.continuousOn.mul
      (hg.mono (Icc_subset_Icc le_rfl hh.2.le))).mul
      (continuousOn_const.sub continuousOn_id)).mul
      (Real.continuous_sqrt.comp (continuous_const.sub continuous_id)).continuousOn)
  have hd : ∀ θ : ℝ, HasDerivAt (fun x : ℝ => h * Real.sin x ^ 2)
      (2 * h * Real.sin θ * Real.cos θ) θ := by
    intro θ
    convert ((Real.hasDerivAt_sin θ).pow 2).const_mul h using 1 <;> norm_num <;> ring
  have he := intervalIntegral.integral_comp_mul_deriv'
    (a := (0 : ℝ)) (b := Real.pi / 2) (fun θ _ => hd θ)
    ((continuous_const.mul Real.continuous_sin |>.mul Real.continuous_cos).continuousOn)
    (hgc.mono himage)
  simp only [Real.sin_zero, Real.sin_pi_div_two, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, one_pow, mul_one] at he
  rw [← he]
  unfold raised moment
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [uIcc_of_le hpi] at hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1
    (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩
  have hsub : h - h * Real.sin θ ^ 2 = h * Real.cos θ ^ 2 := by
    linear_combination -h * Real.sin_sq_add_cos_sq θ
  have hsqrt : Real.sqrt (h - h * Real.sin θ ^ 2) = Real.sqrt h * Real.cos θ := by
    rw [hsub, Real.sqrt_mul hh.1.le, Real.sqrt_sq hc]
  simp only [Function.comp_apply]
  rw [Real.sqrt_mul hh.1.le, Real.sqrt_sq hs, hsqrt, hsub]
  have hroot := Real.sq_sqrt hh.1.le
  norm_num
  linear_combination -(2 * h ^ 2 * g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ 4) * hroot

end LeanVerification.RaisedAbel
