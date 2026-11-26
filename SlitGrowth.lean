import LeanVerification.SlitBoundary
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace LeanVerification.SlitContour

theorem intervalIntegrable_abs_rpow {a b r : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun x : ℝ => |x| ^ r) volume a b := by
  have h1 := (intervalIntegral.intervalIntegrable_rpow' hr (a := a) (b := b)).norm
  have h2 : IntervalIntegrable (fun x : ℝ => ‖(-x) ^ r‖) volume a b := by
    simpa using (IntervalIntegrable.iff_comp_neg.mp
      (intervalIntegral.intervalIntegrable_rpow' hr (a := -a) (b := -b))).norm
  apply (h1.add h2).mono_fun' (continuous_abs.measurable.pow_const r).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg x) r)]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, Real.norm_of_nonneg (Real.rpow_nonneg hx r)]
    exact le_add_of_nonneg_right (norm_nonneg _)
  · rw [abs_of_nonpos hx, Real.norm_of_nonneg (Real.rpow_nonneg (neg_nonneg.mpr hx) r)]
    exact le_add_of_nonneg_left (norm_nonneg _)

theorem intervalIntegrable_abs_sub_rpow {a b r c : ℝ} (hr : -1 < r) :
    IntervalIntegrable (fun x : ℝ => |x - c| ^ r) volume a b := by
  simpa only [sub_add_cancel] using
    (intervalIntegrable_abs_rpow hr (a := a - c) (b := b - c)).comp_sub_right c

def powerMajorant {N : ℕ} (c β : Fin N → ℝ) (x : ℝ) : ℝ :=
  1 + ∑ j, |x - c j| ^ (-β j)

theorem one_le_powerMajorant {N : ℕ} (c β : Fin N → ℝ) (x : ℝ) :
    1 ≤ powerMajorant c β x := by
  unfold powerMajorant
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => Real.rpow_nonneg (abs_nonneg _) _)

theorem term_le_powerMajorant {N : ℕ} (c β : Fin N → ℝ) (x : ℝ) (j : Fin N) :
    |x - c j| ^ (-β j) ≤ powerMajorant c β x := by
  apply (Finset.single_le_sum (fun i _ => Real.rpow_nonneg (abs_nonneg (x - c i)) (-β i))
    (Finset.mem_univ j)).trans
  unfold powerMajorant
  linarith

theorem intervalIntegrable_powerMajorant {N : ℕ} (c β : Fin N → ℝ)
    (hβ : ∀ j, β j < 1) (a b : ℝ) :
    IntervalIntegrable (powerMajorant c β) volume a b := by
  have hi : IntervalIntegrable (fun x => ∑ j, |x - c j| ^ (-β j)) volume a b := by
    convert IntervalIntegrable.sum Finset.univ
      (fun j _ => intervalIntegrable_abs_sub_rpow (a := a) (b := b) (c := c j)
        (by linarith [hβ j] : -1 < -β j)) using 1
    ext x
    simp only [Finset.sum_apply]
  exact intervalIntegrable_const.add hi

/-- A finite cover turns locally uniform strip bounds into a single
integrable majorant. Its dependence on the horizontal coordinate is retained. -/
theorem compact_strip_bound {f : ℂ → ℂ} {P : ℝ → ℝ} {a R : ℝ} {S : Set ℝ}
    (hP : ∀ x ∉ S, 0 ≤ P x)
    (hloc : ∀ t ∈ Icc a R, ∃ r > 0, ∃ M ≥ 0,
      ∀ x y : ℝ, |x - t| < r → |y| < r → y ≠ 0 → x ∉ S →
        ‖f ((x : ℂ) + y * Complex.I)‖ ≤ M * P x) :
    ∃ η > 0, ∃ M ≥ 0, ∀ x ∈ Icc a R, ∀ y : ℝ,
      |y| < η → y ≠ 0 → x ∉ S → ‖f ((x : ℂ) + y * Complex.I)‖ ≤ M * P x := by
  classical
  choose r hr M hM hb using fun t : Icc a R => hloc t t.property
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover
    (fun t : Icc a R => Metric.ball (t : ℝ) (r t)) (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using hr ⟨x, hx⟩⟩)
  have hev : ∀ᶠ y in 𝓝 (0 : ℝ), ∀ i ∈ s, |y| < r i := by
    rw [s.eventually_all]
    intro i hi
    simpa [Metric.ball, Real.dist_eq] using Metric.ball_mem_nhds (0 : ℝ) (hr i)
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨η, hη, ∑ i ∈ s, M i, Finset.sum_nonneg (fun i hi => hM i), ?_⟩
  intro x hx y hy hyn hxS
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hs hx)
  obtain ⟨his, hxball⟩ := mem_iUnion.mp hxi
  have hxr : |x - (i : ℝ)| < r i := by simpa only [Metric.mem_ball, Real.dist_eq] using hxball
  have hyr : |y| < r i := hball (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hy) i his
  have hMi : M i ≤ ∑ j ∈ s, M j := Finset.single_le_sum (fun j hj => hM j) his
  exact (hb i x y hxr hyr hyn hxS).trans (mul_le_mul_of_nonneg_right hMi (hP x hxS))

theorem horizontal_distance_le (x y t : ℝ) :
    dist ((x : ℂ) + y * Complex.I) (t : ℂ) ≤ |x - t| + |y| := by
  rw [dist_eq_norm]
  have he : (x : ℂ) + y * Complex.I - t = ((x - t : ℝ) : ℂ) + (y : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he]
  simpa only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one]
    using norm_add_le (((x - t : ℝ) : ℂ)) ((y : ℂ) * Complex.I)

/-- The paper's finite subintegrable power singularities give an actual
common horizontal-bank majorant. Regular bank points need only local boundedness. -/
theorem exists_power_bank_majorant {N : ℕ} {f : ℂ → ℂ} {H a R : ℝ}
    (c β : Fin N → ℝ) (hβ₀ : ∀ j, 0 ≤ β j) (hβ₁ : ∀ j, β j < 1)
    (hsing : ∀ j, ∃ r > 0, ∃ M ≥ 0, ∀ w ∈ domain H,
      dist w (c j : ℂ) < r → ‖f w‖ ≤ M * dist w (c j : ℂ) ^ (-β j))
    (hreg : ∀ t ∈ Icc a R, t ∉ range c → ∃ r > 0, ∃ M ≥ 0,
      ∀ w ∈ domain H, dist w (t : ℂ) < r → ‖f w‖ ≤ M) :
    ∃ η > 0, ∃ b : ℝ → ℝ, IntervalIntegrable b volume a R ∧
      (∀ x, 0 ≤ b x) ∧
      ∀ᵐ x, x ∈ Icc a R → ∀ y : ℝ, |y| < η → y ≠ 0 →
        ‖f ((x : ℂ) + y * Complex.I)‖ ≤ b x := by
  have hlocal : ∀ t ∈ Icc a R, ∃ r > 0, ∃ M ≥ 0,
      ∀ x y : ℝ, |x - t| < r → |y| < r → y ≠ 0 → x ∉ range c →
        ‖f ((x : ℂ) + y * Complex.I)‖ ≤ M * powerMajorant c β x := by
    intro t ht
    by_cases htc : t ∈ range c
    · obtain ⟨j, rfl⟩ := htc
      obtain ⟨r, hr, M, hM, hm⟩ := hsing j
      refine ⟨r / 2, half_pos hr, M, hM, ?_⟩
      intro x y hx hy hyn hxc
      have hw : (x : ℂ) + y * Complex.I ∈ domain H := Or.inr (by simpa using hyn)
      have hd : dist ((x : ℂ) + y * Complex.I) (c j : ℂ) < r :=
        (horizontal_distance_le x y (c j)).trans_lt (by linarith)
      have hxcj : x ≠ c j := fun he => hxc ⟨j, he.symm⟩
      have hlow : |x - c j| ≤ dist ((x : ℂ) + y * Complex.I) (c j : ℂ) := by
        simpa [dist_eq_norm] using Complex.abs_re_le_norm
          ((x : ℂ) + y * Complex.I - (c j : ℂ))
      have hp := Real.rpow_le_rpow_of_nonpos (abs_pos.mpr (sub_ne_zero.mpr hxcj)) hlow
        (neg_nonpos.mpr (hβ₀ j))
      exact (hm _ hw hd).trans (mul_le_mul_of_nonneg_left
        (hp.trans (term_le_powerMajorant c β x j)) hM)
    · obtain ⟨r, hr, M, hM, hm⟩ := hreg t ht htc
      refine ⟨r / 2, half_pos hr, M, hM, ?_⟩
      intro x y hx hy hyn hxc
      have hw : (x : ℂ) + y * Complex.I ∈ domain H := Or.inr (by simpa using hyn)
      have hd : dist ((x : ℂ) + y * Complex.I) (t : ℂ) < r :=
        (horizontal_distance_le x y t).trans_lt (by linarith)
      exact (hm _ hw hd).trans (le_mul_of_one_le_right hM (one_le_powerMajorant c β x))
  obtain ⟨η, hη, M, hM, hb⟩ := compact_strip_bound
    (fun x _ => (zero_le_one.trans (one_le_powerMajorant c β x))) hlocal
  refine ⟨η, hη, fun x => M * powerMajorant c β x,
    (intervalIntegrable_powerMajorant c β hβ₁ a R).const_mul M,
    fun x => mul_nonneg hM (zero_le_one.trans (one_le_powerMajorant c β x)), ?_⟩
  have hn : ∀ᵐ x : ℝ, x ∉ range c := by
    rw [ae_iff]
    simpa only [not_not] using (Set.finite_range c).measure_zero volume
  filter_upwards [hn] with x hx hxmem y hy hyn
  exact hb x hxmem y hy hyn hx

end LeanVerification.SlitContour
