import LeanVerification.SlitReflection

/-! Local boundedness of regular cut points from genuine one-sided continuous extensions. -/
noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.SlitContour

set_option maxHeartbeats 500000

theorem local_bound_of_bank_limits {f : ℂ → ℂ} {H t : ℝ} {u l : ℂ}
    (ht : H < t)
    (hu : Tendsto f (𝓝[{w : ℂ | 0 < w.im}] (t : ℂ)) (𝓝 u))
    (hl : Tendsto f (𝓝[{w : ℂ | w.im < 0}] (t : ℂ)) (𝓝 l)) :
    ∃ r > 0, ∃ M ≥ 0, ∀ w ∈ domain H, dist w (t : ℂ) < r → ‖f w‖ ≤ M := by
  obtain ⟨ru, hru, hbu⟩ := Metric.tendsto_nhdsWithin_nhds.mp hu 1 (by norm_num)
  obtain ⟨rl, hrl, hbl⟩ := Metric.tendsto_nhdsWithin_nhds.mp hl 1 (by norm_num)
  let r := min ru (min rl (t - H))
  have hr : 0 < r := lt_min hru (lt_min hrl (sub_pos.mpr ht))
  refine ⟨r, hr, 1 + ‖u‖ + ‖l‖, by positivity, ?_⟩
  intro w hw hdist
  have hdt : dist w (t : ℂ) < t - H := hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hre : H < w.re := by
    have hnorm := Complex.abs_re_le_norm (w - (t : ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at hnorm
    rw [← dist_eq_norm] at hnorm
    have habs := neg_le_abs (w.re - t)
    linarith
  have him : w.im ≠ 0 := hw.resolve_left (not_lt.mpr hre.le)
  rcases lt_or_gt_of_ne him with hneg | hpos
  · have hb := hbl hneg (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    rw [dist_eq_norm] at hb
    have hn := norm_add_le (f w - l) l
    rw [sub_add_cancel] at hn
    linarith [norm_nonneg u]
  · have hb := hbu hpos (hdist.trans_le (min_le_left _ _))
    rw [dist_eq_norm] at hb
    have hn := norm_add_le (f w - u) u
    rw [sub_add_cancel] at hn
    linarith [norm_nonneg l]

theorem local_bound_left_of_cut {f : ℂ → ℂ} {H t : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (ht : t < H) :
    ∃ r > 0, ∃ M ≥ 0, ∀ w ∈ domain H, dist w (t : ℂ) < r → ‖f w‖ ≤ M := by
  have hc := (hf.differentiableAt ((isOpen_domain H).mem_nhds (show (t : ℂ) ∈ domain H from Or.inl ht))).continuousAt
  obtain ⟨r, hr, hb⟩ := Metric.continuousAt_iff.mp hc 1 (by norm_num)
  refine ⟨r, hr, 1 + ‖f (t : ℂ)‖, by positivity, ?_⟩
  intro w _ hw
  have hd := hb hw
  rw [dist_eq_norm] at hd
  have hn := norm_add_le (f w - f (t : ℂ)) (f (t : ℂ))
  rw [sub_add_cancel] at hn
  linarith

end LeanVerification.SlitContour
