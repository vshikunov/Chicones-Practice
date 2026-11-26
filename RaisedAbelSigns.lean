import LeanVerification.RaisedAbelCalculus
import LeanVerification.CountedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
Sign reduction for the regular angular Abel transforms. The shifted input
is formed from the given function, and every strict integral inequality
is obtained from a nonzero value on the physical energy interval.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace LeanVerification.RaisedAbel

def shift (c : ℝ) (g : ℝ → ℝ) (v : ℝ) : ℝ := (v - c) * g v

theorem analyticOnNhd_shift {g : ℝ → ℝ} {H c : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) :
    AnalyticOnNhd ℝ (shift c g) (Icc 0 H) :=
  fun v hv => (analyticAt_id.sub analyticAt_const).mul (hg v hv)

theorem moment_shift {g : ℝ → ℝ} {H h c : ℝ}
    (hg : ContinuousOn g (Icc 0 H)) (hh : h ∈ Icc 0 H) (k : ℕ) :
    moment (shift c g) k h = (h - c) * moment g k h - h * moment g (k + 1) h := by
  have hc := continuous_angle hg hh
  have h1 : Continuous (fun θ =>
      g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ (2 * k)) :=
    (hc.mul (Real.continuous_sin.pow 2)).mul (Real.continuous_cos.pow _)
  have h2 : Continuous (fun θ =>
      g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ (2 * (k + 1))) :=
    (hc.mul (Real.continuous_sin.pow 2)).mul (Real.continuous_cos.pow _)
  unfold moment
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub
      ((continuous_const.mul h1).intervalIntegrable _ _)
      ((continuous_const.mul h2).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [shift, show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
  linear_combination
    h * g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ (2 * k) *
      Real.sin_sq_add_cos_sq θ

theorem exists_angle_for_energy {h v : ℝ} (hh : 0 < h) (hv : v ∈ Ioo 0 h) :
    ∃ θ ∈ Ioo (0 : ℝ) (Real.pi / 2), h * Real.sin θ ^ 2 = v := by
  have hvh : 0 < v / h := div_pos hv.1 hh
  have hlt : v / h < 1 := (div_lt_one hh).mpr hv.2
  have hr0 : 0 < Real.sqrt (v / h) := Real.sqrt_pos.mpr hvh
  have hr1 : Real.sqrt (v / h) < 1 := by
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr (by simpa using hlt)
  refine ⟨Real.arcsin (Real.sqrt (v / h)),
    ⟨Real.arcsin_pos.mpr hr0, Real.arcsin_lt_pi_div_two.mpr hr1⟩, ?_⟩
  rw [Real.sin_arcsin (by linarith) hr1.le, Real.sq_sqrt hvh.le]
  field_simp

theorem moment_pos {g : ℝ → ℝ} {H h : ℝ} (k : ℕ)
    (hg : ContinuousOn g (Icc 0 H)) (hh : h ∈ Ioo 0 H)
    (hn : ∀ v ∈ Icc 0 h, 0 ≤ g v)
    (hp : ∃ v ∈ Ioo 0 h, 0 < g v) : 0 < moment g k h := by
  have hc := continuous_angle hg (Ioo_subset_Icc_self hh)
  have hcont := (hc.mul (Real.continuous_sin.pow 2)).mul (Real.continuous_cos.pow (2 * k))
  apply intervalIntegral.integral_pos (by positivity : (0 : ℝ) < Real.pi / 2)
    hcont.continuousOn
  · intro θ _
    have hcos : 0 ≤ Real.cos θ ^ (2 * k) := by
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    exact mul_nonneg (mul_nonneg (hn _ (sin_sq_energy_mem ⟨hh.1.le, le_rfl⟩ θ))
      (sq_nonneg _)) hcos
  · obtain ⟨v, hv, hgv⟩ := hp
    obtain ⟨θ, hθ, he⟩ := exists_angle_for_energy hh.1 hv
    refine ⟨θ, Ioo_subset_Icc_self hθ, ?_⟩
    have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
    rw [he]
    exact mul_pos (mul_pos hgv (pow_pos hsin _)) (pow_pos hcos _)

theorem analytic_nonzero_on_initial_interval {g : ℝ → ℝ} {H d : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hd : d ∈ Ioo 0 H)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) : ∃ v ∈ Ioo 0 d, g v ≠ 0 := by
  by_contra hn
  push_neg at hn
  have hc : d / 2 ∈ Ioo 0 d := ⟨by linarith [hd.1], by linarith [hd.1]⟩
  have he : g =ᶠ[𝓝 (d / 2)] 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hc] with v hv
    exact hn v hv
  have hwhole := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_Icc (0 : ℝ) H).isPreconnected
    (show d / 2 ∈ Icc 0 H by constructor <;> linarith [hd.1, hd.2]) he
  obtain ⟨v, hv, hne⟩ := hnz
  exact hne (hwhole hv)

theorem raised_pos_before_first_change {g : ℝ → ℝ} {H h c : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H) (hc : h ≤ c)
    (hn : ∀ v ∈ Icc 0 c, 0 ≤ g v)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) : 0 < raised g h := by
  obtain ⟨v, hv, hne⟩ := analytic_nonzero_on_initial_interval hg hh hnz
  have hi : 0 < moment g 2 h := moment_pos 2 hg.continuousOn hh
    (fun v hv => hn v ⟨hv.1, hv.2.trans hc⟩)
    ⟨v, hv, lt_of_le_of_ne (hn v ⟨hv.1.le, hv.2.le.trans hc⟩) (Ne.symm hne)⟩
  exact mul_pos (mul_pos (by norm_num) (pow_pos hh.1 _)) hi

theorem raised_normalized_derivative {g : ℝ → ℝ} {H h c : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H) (hc : c < h) :
    HasDerivAt (fun t => raised g t * (t - c) ^ (-(3 / 2 : ℝ)))
      ((3 / 2 : ℝ) * (h - c) ^ (-(5 / 2 : ℝ)) * half (shift c g) h) h := by
  have hb := sub_pos.mpr hc
  have hd := (hasDerivAt_raised hg hh).mul
    (((hasDerivAt_id h).sub_const c).rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hb.ne'))
  apply hd.congr_deriv
  have hm := moment_shift hg.continuousOn (Ioo_subset_Icc_self hh) (c := c) 1
  have hp : (h - c) ^ (-(3 / 2 : ℝ)) =
      (h - c) * (h - c) ^ (-(5 / 2 : ℝ)) := by
    calc
      _ = (h - c) ^ ((1 : ℝ) + -(5 / 2 : ℝ)) := by congr 1; norm_num
      _ = (h - c) * (h - c) ^ (-(5 / 2 : ℝ)) := by
        rw [Real.rpow_add hb, Real.rpow_one]
  simp only [half, raised, id_eq, sub_zero, mul_one,
    show -(3 / 2 : ℝ) - 1 = -(5 / 2 : ℝ) by norm_num, hp]
  linear_combination -(3 * h ^ 2 * (h - c) ^ (-(5 / 2 : ℝ))) * hm

theorem half_normalized_derivative {g : ℝ → ℝ} {H h c : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H) (hc : c < h) :
    HasDerivAt (fun t => half g t * (t - c) ^ (-(1 / 2 : ℝ)))
      (h * (h - c) ^ (-(3 / 2 : ℝ)) * moment (shift c g) 0 h) h := by
  have hb := sub_pos.mpr hc
  have hd := (hasDerivAt_half hg hh).mul
    (((hasDerivAt_id h).sub_const c).rpow_const (p := -(1 / 2 : ℝ)) (Or.inl hb.ne'))
  apply hd.congr_deriv
  have hm := moment_shift hg.continuousOn (Ioo_subset_Icc_self hh) (c := c) 0
  have hp : (h - c) ^ (-(1 / 2 : ℝ)) =
      (h - c) * (h - c) ^ (-(3 / 2 : ℝ)) := by
    calc
      _ = (h - c) ^ ((1 : ℝ) + -(3 / 2 : ℝ)) := by congr 1; norm_num
      _ = (h - c) * (h - c) ^ (-(3 / 2 : ℝ)) := by
        rw [Real.rpow_add hb, Real.rpow_one]
  simp only [half, id_eq, sub_zero, mul_one,
    show -(1 / 2 : ℝ) - 1 = -(3 / 2 : ℝ) by norm_num, hp]
  linear_combination -(h * (h - c) ^ (-(3 / 2 : ℝ))) * hm

theorem moment_neg (g : ℝ → ℝ) (k : ℕ) (h : ℝ) :
    moment (fun v => -g v) k h = -moment g k h := by
  unfold moment
  rw [← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro θ _
  ring

theorem exists_positive_before_first_change {g : ℝ → ℝ} {H h c : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H) (hc : 0 < c)
    (hn : ∀ v ∈ Icc 0 c, 0 ≤ g v)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) :
    ∃ v, v ∈ Ioo 0 h ∧ v < c ∧ 0 < g v := by
  let d := min h c / 2
  have hmin : 0 < min h c := lt_min hh.1 hc
  have hd : d ∈ Ioo 0 H := by
    dsimp [d]
    constructor
    · positivity
    · have hm : min h c ≤ h := min_le_left _ _
      linarith [hh.2]
  obtain ⟨v, hv, hne⟩ := analytic_nonzero_on_initial_interval hg hd hnz
  have hvh : v < h := by
    have hm : min h c ≤ h := min_le_left _ _
    dsimp [d] at hv
    linarith [hv.2]
  have hvc : v < c := by
    have hm : min h c ≤ c := min_le_right _ _
    dsimp [d] at hv
    linarith [hv.2]
  exact ⟨v, ⟨hv.1, hvh⟩, hvc, lt_of_le_of_ne (hn v ⟨hv.1.le, hvc.le⟩) (Ne.symm hne)⟩

theorem half_shift_neg_before_second_change {g : ℝ → ℝ} {H h c₁ c₂ : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H)
    (hc₁ : 0 < c₁) (hh₂ : h ≤ c₂)
    (hpos : ∀ v ∈ Icc 0 c₁, 0 ≤ g v)
    (hneg : ∀ v ∈ Icc c₁ c₂, g v ≤ 0)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) : half (shift c₁ g) h < 0 := by
  have hc : ContinuousOn (fun v => -shift c₁ g v) (Icc 0 H) :=
    (analyticOnNhd_shift hg).continuousOn.neg
  have hn : ∀ v ∈ Icc 0 h, 0 ≤ -shift c₁ g v := by
    intro v hv
    apply neg_nonneg.mpr
    change (v - c₁) * g v ≤ 0
    by_cases hv₁ : v ≤ c₁
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv₁) (hpos v ⟨hv.1, hv₁⟩)
    · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (le_of_not_ge hv₁))
        (hneg v ⟨(le_of_not_ge hv₁), hv.2.trans hh₂⟩)
  obtain ⟨v, hv, hv₁, hgv⟩ := exists_positive_before_first_change hg hh hc₁ hpos hnz
  have hposi := moment_pos 1 hc hh hn
    ⟨v, hv, neg_pos.mpr (mul_neg_of_neg_of_pos (sub_neg.mpr hv₁) hgv)⟩
  rw [moment_neg] at hposi
  change 2 * h ^ 2 * moment (shift c₁ g) 1 h < 0
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) (pow_pos hh.1 _)) (neg_pos.mp hposi)

theorem twice_shift_moment_pos {g : ℝ → ℝ} {H h c₁ c₂ : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H)
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂)
    (hpos : ∀ v ∈ Icc 0 c₁, 0 ≤ g v)
    (hneg : ∀ v ∈ Icc c₁ c₂, g v ≤ 0)
    (hlast : ∀ v ∈ Icc c₂ H, 0 ≤ g v)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) :
    0 < moment (shift c₂ (shift c₁ g)) 0 h := by
  have hc := (analyticOnNhd_shift (c := c₂) (analyticOnNhd_shift (c := c₁) hg)).continuousOn
  have hn : ∀ v ∈ Icc 0 h, 0 ≤ shift c₂ (shift c₁ g) v := by
    intro v hv
    change 0 ≤ (v - c₂) * ((v - c₁) * g v)
    by_cases hv₁ : v ≤ c₁
    · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hv₁.trans hc₁₂.le))
        (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hv₁) (hpos v ⟨hv.1, hv₁⟩))
    · have hc₁v : c₁ ≤ v := (lt_of_not_ge hv₁).le
      by_cases hv₂ : v ≤ c₂
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hv₂)
          (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hc₁v) (hneg v ⟨hc₁v, hv₂⟩))
      · exact mul_nonneg (sub_nonneg.mpr (lt_of_not_ge hv₂).le)
          (mul_nonneg (sub_nonneg.mpr hc₁v) (hlast v ⟨(lt_of_not_ge hv₂).le, hv.2.trans hh.2.le⟩))
  obtain ⟨v, hv, hv₁, hgv⟩ := exists_positive_before_first_change hg hh hc₁ hpos hnz
  have hp : 0 < shift c₂ (shift c₁ g) v :=
    mul_pos_of_neg_of_neg (sub_neg.mpr (hv₁.trans hc₁₂))
      (mul_neg_of_neg_of_pos (sub_neg.mpr hv₁) hgv)
  exact moment_pos 0 hc hh hn ⟨v, hv, hp⟩

theorem half_shift_deriv_pos_at_zero {g : ℝ → ℝ} {H h c₁ c₂ : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hh : h ∈ Ioo 0 H)
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂h : c₂ < h)
    (hpos : ∀ v ∈ Icc 0 c₁, 0 ≤ g v)
    (hneg : ∀ v ∈ Icc c₁ c₂, g v ≤ 0)
    (hlast : ∀ v ∈ Icc c₂ H, 0 ≤ g v)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0)
    (hz : half (shift c₁ g) h = 0) : 0 < deriv (half (shift c₁ g)) h := by
  have hi := twice_shift_moment_pos hg hh hc₁ hc₁₂ hpos hneg hlast hnz
  have hd := half_normalized_derivative (analyticOnNhd_shift (c := c₁) hg) hh hc₂h
  have hf := (hasDerivAt_half (analyticOnNhd_shift (c := c₁) hg) hh)
  have hp := (((hasDerivAt_id h).sub_const c₂).rpow_const
    (p := -(1 / 2 : ℝ)) (Or.inl (sub_pos.mpr hc₂h).ne'))
  have he := hd.unique (hf.mul hp)
  simp only [hz, zero_mul, add_zero, id_eq, sub_zero, mul_one] at he
  have hl : 0 < h * (h - c₂) ^ (-(3 / 2 : ℝ)) *
      moment (shift c₂ (shift c₁ g)) 0 h :=
    mul_pos (mul_pos hh.1 (Real.rpow_pos_of_pos (sub_pos.mpr hc₂h) _)) hi
  rw [he] at hl
  have hpow : 0 < (h - c₂) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (sub_pos.mpr hc₂h) _
  rw [hf.deriv]
  exact (mul_pos_iff_of_pos_right hpow).mp hl

theorem normalized_raised_positive_curvature {g : ℝ → ℝ} {H c₁ c₂ : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂)
    (hpos : ∀ v ∈ Icc 0 c₁, 0 ≤ g v)
    (hneg : ∀ v ∈ Icc c₁ c₂, g v ≤ 0)
    (hlast : ∀ v ∈ Icc c₂ H, 0 ≤ g v)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) :
    ∀ h ∈ Ioo c₁ H,
      deriv (fun t => raised g t * (t - c₁) ^ (-(3 / 2 : ℝ))) h = 0 →
      0 < deriv (deriv (fun t => raised g t * (t - c₁) ^ (-(3 / 2 : ℝ)))) h := by
  intro h hh hz
  have hh0 : h ∈ Ioo 0 H := ⟨hc₁.trans hh.1, hh.2⟩
  let A := fun t => raised g t * (t - c₁) ^ (-(3 / 2 : ℝ))
  let p := fun t => (3 / 2 : ℝ) * (t - c₁) ^ (-(5 / 2 : ℝ))
  have hp : 0 < p h := by
    dsimp [p]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (sub_pos.mpr hh.1) _)
  have hAeq : deriv A =ᶠ[𝓝 h] fun t => p t * half (shift c₁ g) t := by
    filter_upwards [isOpen_Ioo.mem_nhds hh] with t ht
    exact (raised_normalized_derivative hg ⟨hc₁.trans ht.1, ht.2⟩ ht.1).deriv
  have hzB : half (shift c₁ g) h = 0 := by
    have he := hAeq.eq_of_nhds
    rw [hz] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hp.ne'
  have hc₂h : c₂ < h := by
    by_contra hn
    have hlt := half_shift_neg_before_second_change hg hh0 hc₁ (le_of_not_gt hn) hpos hneg hnz
    exact (ne_of_lt hlt) hzB
  have hdB := half_shift_deriv_pos_at_zero hg hh0 hc₁ hc₁₂ hc₂h hpos hneg hlast hnz hzB
  have hdp : DifferentiableAt ℝ p h := by
    have ha : AnalyticAt ℝ (fun t : ℝ => (t - c₁) ^ (-(5 / 2 : ℝ))) h :=
      (Loud.analyticAt_rpow_const (-(5 / 2 : ℝ)) (h - c₁) (sub_pos.mpr hh.1)).comp_of_eq
        (analyticAt_id.sub analyticAt_const) rfl
    exact (analyticAt_const.mul ha).differentiableAt
  have hdhalf := (analyticAt_half (analyticOnNhd_shift (c := c₁) hg) (Ioo_subset_Icc_self hh0)).differentiableAt.hasDerivAt
  have he := (hdp.hasDerivAt.mul hdhalf).deriv
  rw [hzB, mul_zero, zero_add] at he
  rw [hAeq.deriv_eq, he]
  exact mul_pos hp hdB

/-- The twice-raised transform has at most two zeros counted with their
actual analytic multiplicities, for an ordered positive/negative/positive
input. Zeros of even order inside a sign block are allowed. -/
theorem multiplicityBound_two_of_three_sign_blocks {g : ℝ → ℝ} {H c₁ c₂ : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂)
    (hpos : ∀ v ∈ Icc 0 c₁, 0 ≤ g v)
    (hneg : ∀ v ∈ Icc c₁ c₂, g v ≤ 0)
    (hlast : ∀ v ∈ Icc c₂ H, 0 ≤ g v)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) :
    AnalyticMultiplicity.MultiplicityBound 2 (raised g) (Ioo 0 H) := by
  classical
  let A := fun t => raised g t * (t - c₁) ^ (-(3 / 2 : ℝ))
  have hA : AnalyticOnNhd ℝ A (Ioo c₁ H) := by
    intro h hh
    have hf := analyticAt_raised hg ⟨(hc₁.trans hh.1).le, hh.2.le⟩
    have hp : AnalyticAt ℝ (fun t : ℝ => (t - c₁) ^ (-(3 / 2 : ℝ))) h :=
      (Loud.analyticAt_rpow_const (-(3 / 2 : ℝ)) (h - c₁) (sub_pos.mpr hh.1)).comp_of_eq
        (analyticAt_id.sub analyticAt_const) rfl
    exact hf.mul hp
  have hbound := AnalyticMultiplicity.multiplicityBound_two_of_stationary_curvature hA
    (normalized_raised_positive_curvature hg hc₁ hc₁₂ hpos hneg hlast hnz)
  apply AnalyticMultiplicity.multiplicityBound_of_zero_order_transport hbound
  intro h hh hz
  have hc₁h : c₁ < h := by
    by_contra hn
    have hp := raised_pos_before_first_change hg hh (le_of_not_gt hn) hpos hnz
    exact (ne_of_gt hp) hz
  have hf := analyticAt_raised hg (Ioo_subset_Icc_self hh)
  have hp : AnalyticAt ℝ (fun t : ℝ => (t - c₁) ^ (-(3 / 2 : ℝ))) h :=
    (Loud.analyticAt_rpow_const (-(3 / 2 : ℝ)) (h - c₁) (sub_pos.mpr hc₁h)).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl
  refine ⟨⟨hc₁h, hh.2⟩, by dsimp [A]; rw [hz, zero_mul], ?_⟩
  rw [AnalyticMultiplicity.vanishingOrder_eq hf,
    AnalyticMultiplicity.vanishingOrder_eq (hA h ⟨hc₁h, hh.2⟩)]
  exact (AnalyticReparametrization.order_mul_nonvanishing hf hp
    (Real.rpow_pos_of_pos (sub_pos.mpr hc₁h) _).ne').symm

theorem raised_const_mul (q : ℝ) (g : ℝ → ℝ) (h : ℝ) :
    raised (fun v => q * g v) h = q * raised g h := by
  unfold raised moment
  have he : (∫ θ in (0 : ℝ)..Real.pi / 2,
      q * g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ (2 * 2)) =
      q * ∫ θ in (0 : ℝ)..Real.pi / 2,
        g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ (2 * 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [he]
  ring

theorem exists_initial_strict_sign {g : ℝ → ℝ} {H : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hH : 0 < H)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) :
    ∃ q d : ℝ, (q = 1 ∨ q = -1) ∧ d ∈ Ioo 0 H ∧
      (∀ v ∈ Icc 0 d, 0 ≤ q * g v) ∧ (∀ v ∈ Ioo 0 d, 0 < q * g v) := by
  classical
  have hg0 := hg 0 ⟨le_rfl, hH.le⟩
  have hlocal : ¬∀ᶠ v in 𝓝 (0 : ℝ), g v = 0 := by
    intro he
    have he' : g =ᶠ[𝓝 (0 : ℝ)] 0 := he
    have hz := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_Icc (0 : ℝ) H).isPreconnected ⟨le_rfl, hH.le⟩ he'
    obtain ⟨v, hv, hvn⟩ := hnz
    exact hvn (hz hv)
  obtain ⟨n, b, hb, hbn, he⟩ := hg0.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hlocal
  let q : ℝ := if 0 < b 0 then 1 else -1
  have hq : q = 1 ∨ q = -1 := by
    by_cases hp : 0 < b 0 <;> simp [q, hp]
  have hqb : 0 < q * b 0 := by
    by_cases hp : 0 < b 0
    · simpa [q, hp] using hp
    · have hn : b 0 < 0 := lt_of_le_of_ne (le_of_not_gt hp) hbn
      simpa [q, hp] using neg_pos.mpr hn
  have hbp : ∀ᶠ v in 𝓝 (0 : ℝ), 0 < q * b v :=
    (continuousAt_const.mul hb.continuousAt).eventually (Ioi_mem_nhds hqb)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (he.and hbp)
  let d := min H ε / 2
  have hm : 0 < min H ε := lt_min hH hε
  have hd : d ∈ Ioo 0 H := by
    dsimp [d]
    constructor
    · positivity
    · have hle := min_le_left H ε
      linarith
  have hdε : d < ε := by
    dsimp [d]
    have hle := min_le_right H ε
    linarith
  have hformula : ∀ v ∈ Icc 0 d, q * g v = v ^ n * (q * b v) ∧ 0 < q * b v := by
    intro v hv
    have hvb : v ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hv.1]
      exact hv.2.trans_lt hdε
    obtain ⟨hvf, hvc⟩ := hball hvb
    simp only [sub_zero, smul_eq_mul] at hvf
    exact ⟨by rw [hvf]; ring, hvc⟩
  refine ⟨q, d, hq, hd, ?_, ?_⟩
  · intro v hv
    obtain ⟨heq, hpos⟩ := hformula v hv
    rw [heq]
    exact mul_nonneg (pow_nonneg hv.1 _) hpos.le
  · intro v hv
    obtain ⟨heq, hpos⟩ := hformula v (Ioo_subset_Icc_self hv)
    rw [heq]
    exact mul_pos (pow_pos hv.1 _) hpos

theorem exists_raised_nonzero {g : ℝ → ℝ} {H : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hH : 0 < H)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) :
    ∃ h ∈ Ioo 0 H, raised g h ≠ 0 := by
  obtain ⟨q, d, _, hd, hnonneg, hpos⟩ := exists_initial_strict_sign hg hH hnz
  let h := d / 2
  have hh : h ∈ Ioo 0 H := by dsimp [h]; constructor <;> linarith [hd.1, hd.2]
  have hhd : h < d := by dsimp [h]; linarith [hd.1]
  have hm : 0 < moment (fun v => q * g v) 2 h := by
    apply moment_pos 2 (continuousOn_const.mul hg.continuousOn) hh
      (fun v hv => hnonneg v ⟨hv.1, hv.2.trans hhd.le⟩)
    refine ⟨h / 2, ⟨by linarith [hh.1], by linarith [hh.1]⟩, ?_⟩
    exact hpos _ ⟨by linarith [hh.1], by linarith [hh.1]⟩
  have hr : 0 < raised (fun v => q * g v) h :=
    mul_pos (mul_pos (by norm_num) (pow_pos hh.1 _)) hm
  rw [raised_const_mul] at hr
  refine ⟨h, hh, ?_⟩
  intro hz
  rw [hz, mul_zero] at hr
  exact lt_irrefl 0 hr

/-- The raised transform cannot vanish identically unless its analytic
input does. This converse uses the actual local factorization of the
input at zero, not an assumed injectivity statement. -/
theorem raised_identically_zero_iff {g : ℝ → ℝ} {H : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hH : 0 < H) :
    (∀ h ∈ Ioo 0 H, raised g h = 0) ↔ ∀ v ∈ Icc 0 H, g v = 0 := by
  constructor
  · intro hz v hv
    by_contra hn
    obtain ⟨h, hh, hne⟩ := exists_raised_nonzero hg hH ⟨v, hv, hn⟩
    exact hne (hz h hh)
  · intro hz h hh
    have hi : moment g 2 h = 0 := by
      unfold moment
      have he : (fun θ => g (h * Real.sin θ ^ 2) * Real.sin θ ^ 2 * Real.cos θ ^ (2 * 2)) =
          (fun _ : ℝ => (0 : ℝ)) := by
        funext θ
        rw [hz _ (sin_sq_energy_mem (Ioo_subset_Icc_self hh) θ), zero_mul, zero_mul]
      rw [he]
      simp
    simp only [raised, hi, mul_zero]

theorem multiplicityBound_one_of_two_sign_blocks {g : ℝ → ℝ} {H c : ℝ}
    (hg : AnalyticOnNhd ℝ g (Icc 0 H)) (hc : 0 < c)
    (hpos : ∀ v ∈ Icc 0 c, 0 ≤ g v)
    (hneg : ∀ v ∈ Icc c H, g v ≤ 0)
    (hnz : ∃ v ∈ Icc 0 H, g v ≠ 0) :
    AnalyticMultiplicity.MultiplicityBound 1 (raised g) (Ioo 0 H) := by
  classical
  let A := fun t => raised g t * (t - c) ^ (-(3 / 2 : ℝ))
  have hA : AnalyticOnNhd ℝ A (Ioo c H) := by
    intro h hh
    have hf := analyticAt_raised hg ⟨(hc.trans hh.1).le, hh.2.le⟩
    have hp : AnalyticAt ℝ (fun t : ℝ => (t - c) ^ (-(3 / 2 : ℝ))) h :=
      (Loud.analyticAt_rpow_const (-(3 / 2 : ℝ)) (h - c) (sub_pos.mpr hh.1)).comp_of_eq
        (analyticAt_id.sub analyticAt_const) rfl
    exact hf.mul hp
  have hd : ∀ h ∈ Ioo c H, deriv A h < 0 := by
    intro h hh
    have hh0 : h ∈ Ioo 0 H := ⟨hc.trans hh.1, hh.2⟩
    rw [(raised_normalized_derivative hg hh0 hh.1).deriv]
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) (Real.rpow_pos_of_pos (sub_pos.mpr hh.1) _))
      (half_shift_neg_before_second_change hg hh0 hc hh.2.le hpos hneg hnz)
  have hdz : AnalyticMultiplicity.MultiplicityBound 0 (deriv A) (Ioo c H) := by
    intro z hz
    have he : z = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro x hx
      exact (ne_of_lt (hd x (hz x hx).1)) (hz x hx).2
    simp [he]
  have hb := AnalyticMultiplicity.multiplicityBound_of_derivative (convex_Ioo c H) hA hdz
  apply AnalyticMultiplicity.multiplicityBound_of_zero_order_transport hb
  intro h hh hz
  have hch : c < h := by
    by_contra hn
    exact (ne_of_gt (raised_pos_before_first_change hg hh (le_of_not_gt hn) hpos hnz)) hz
  have hf := analyticAt_raised hg (Ioo_subset_Icc_self hh)
  have hp : AnalyticAt ℝ (fun t : ℝ => (t - c) ^ (-(3 / 2 : ℝ))) h :=
    (Loud.analyticAt_rpow_const (-(3 / 2 : ℝ)) (h - c) (sub_pos.mpr hch)).comp_of_eq
      (analyticAt_id.sub analyticAt_const) rfl
  refine ⟨⟨hch, hh.2⟩, by dsimp [A]; rw [hz, zero_mul], ?_⟩
  rw [AnalyticMultiplicity.vanishingOrder_eq hf,
    AnalyticMultiplicity.vanishingOrder_eq (hA h ⟨hch, hh.2⟩)]
  exact (AnalyticReparametrization.order_mul_nonvanishing hf hp
    (Real.rpow_pos_of_pos (sub_pos.mpr hch) _).ne').symm

end LeanVerification.RaisedAbel
