import LeanVerification.RectangularCauchy
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.SlitContour

open RectangularCauchy

/-- The plane cut along the real ray beginning at `H`. -/
def domain (H : ℝ) : Set ℂ := {w | w.re < H ∨ w.im ≠ 0}

theorem isOpen_domain (H : ℝ) : IsOpen (domain H) :=
  (isOpen_lt Complex.continuous_re continuous_const).union
    (isOpen_ne_fun Complex.continuous_im continuous_const)

def quotient (f : ℂ → ℂ) (z : ℝ) (w : ℂ) : ℂ := f w / (w - z)

def outer (g : ℂ → ℂ) (L R r ε : ℝ) : ℂ :=
  (∫ x in L..R, g ((x : ℂ) - r * Complex.I)) -
  (∫ x in L..R, g ((x : ℂ) + r * Complex.I)) +
  Complex.I * (∫ y in ε..r, g ((R : ℂ) + y * Complex.I)) +
  Complex.I * (∫ y in (-r)..(-ε), g ((R : ℂ) + y * Complex.I)) -
  Complex.I * (∫ y in (-r)..r, g ((L : ℂ) + y * Complex.I))

def banks (g : ℂ → ℂ) (a R ε : ℝ) : ℂ :=
  (∫ x in a..R, g ((x : ℂ) + ε * Complex.I)) -
  (∫ x in a..R, g ((x : ℂ) - ε * Complex.I))

def gap (g : ℂ → ℂ) (a ε : ℝ) : ℂ :=
  Complex.I * (∫ y in (-ε)..ε, g ((a : ℂ) + y * Complex.I))

theorem differentiableOn_quotient {f : ℂ → ℂ} {s : Set ℂ} {z : ℝ}
    (hf : DifferentiableOn ℂ f s) (hz : (z : ℂ) ∉ s) :
    DifferentiableOn ℂ (quotient f z) s := by
  apply hf.div (differentiableOn_id.sub_const (z : ℂ))
  intro w hw
  exact sub_ne_zero.mpr (fun he => hz (he ▸ hw))

theorem rectangle_left_subset {H L a c d : ℝ} (hLa : L ≤ a) (haH : a < H) :
    uIcc L a ×ℂ uIcc c d ⊆ domain H := by
  intro w hw
  exact Or.inl (((uIcc_of_le hLa ▸ hw.1).2).trans_lt haH)

theorem rectangle_upper_subset {H a R ε r : ℝ} (he : 0 < ε) (her : ε ≤ r) :
    uIcc a R ×ℂ uIcc ε r ⊆ domain H := by
  intro w hw
  exact Or.inr (ne_of_gt (he.trans_le (uIcc_of_le her ▸ hw.2).1))

theorem rectangle_lower_subset {H a R ε r : ℝ} (he : 0 < ε) (her : ε ≤ r) :
    uIcc a R ×ℂ uIcc (-r) (-ε) ⊆ domain H := by
  intro w hw
  exact Or.inr (ne_of_lt (((uIcc_of_le (neg_le_neg her) ▸ hw.2).2).trans_lt
    (neg_neg_of_pos he)))

/-- The finite slit contour is assembled from three genuine rectangles.
The small vertical segment lies strictly to the left of the cut. -/
theorem finite_contour {f : ℂ → ℂ} {H L z a R r ε : ℝ}
    (hLz : L < z) (hza : z < a) (haH : a < H) (haR : a < R)
    (he : 0 < ε) (her : ε ≤ r)
    (hf : DifferentiableOn ℂ f (domain H)) :
    outer (quotient f z) L R r ε + banks (quotient f z) a R ε +
      gap (quotient f z) a ε = 2 * (Real.pi : ℂ) * Complex.I * f z := by
  let g := quotient f z
  have hr : 0 < r := he.trans_le her
  have hLa : L ≤ a := (hLz.trans hza).le
  have hleft := hf.mono (rectangle_left_subset (c := -r) (d := r) hLa haH)
  have hupper := differentiableOn_quotient
    (hf.mono (rectangle_upper_subset (a := a) (R := R) he her)) (z := z) (by
      intro hz
      have hz' : (0 : ℝ) ∈ uIcc ε r := by simpa using hz.2
      have hz'' := (uIcc_of_le her ▸ hz').1
      linarith)
  have hlower := differentiableOn_quotient
    (hf.mono (rectangle_lower_subset (a := a) (R := R) he her)) (z := z) (by
      intro hz
      have hz' : (0 : ℝ) ∈ uIcc (-r) (-ε) := by simpa using hz.2
      have hz'' := (uIcc_of_le (neg_le_neg her) ▸ hz').2
      linarith)
  have hc := boundary_cauchy hLz hza (neg_neg_of_pos hr) hr hleft
  have hu := boundary_eq_zero hupper
  have hl := boundary_eq_zero hlower
  have hgc (w : ℂ) (hw : w ∈ domain H) (hwz : w ≠ (z : ℂ)) : ContinuousAt g w := by
    exact (hf.differentiableAt ((isOpen_domain H).mem_nhds hw)).continuousAt.div
      (continuousAt_id.sub_const (z : ℂ)) (sub_ne_zero.mpr hwz)
  have hhor (y : ℝ) (hy : y ≠ 0) :
      Continuous (fun x : ℝ => g ((x : ℂ) + y * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hw : (x : ℂ) + y * Complex.I ∈ domain H := Or.inr (by simpa using hy)
    have hn : (x : ℂ) + y * Complex.I ≠ z := by
      intro heq
      have him := congrArg Complex.im heq
      simp at him
      exact hy him
    have hp : ContinuousAt (fun u : ℝ => (u : ℂ) + y * Complex.I) x := by fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => (u : ℂ) + y * Complex.I) (hgc _ hw hn) hp
  have hvert (x : ℝ) (hx : x < H) (hxz : x ≠ z) :
      Continuous (fun y : ℝ => g ((x : ℂ) + y * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hw : (x : ℂ) + y * Complex.I ∈ domain H := Or.inl (by simpa using hx)
    have hn : (x : ℂ) + y * Complex.I ≠ z := by
      intro heq
      have hre := congrArg Complex.re heq
      simp at hre
      exact hxz hre
    have hp : ContinuousAt (fun u : ℝ => (x : ℂ) + u * Complex.I) y := by fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => (x : ℂ) + u * Complex.I) (hgc _ hw hn) hp
  have hcint : EdgeIntegrable g L a (-r) r :=
    ⟨(hhor (-r) (neg_ne_zero.mpr hr.ne')).intervalIntegrable L a,
      (hhor r hr.ne').intervalIntegrable L a,
      (hvert a haH hza.ne').intervalIntegrable (-r) r,
      (hvert L (hLa.trans_lt haH) hLz.ne).intervalIntegrable (-r) r⟩
  have huint := edgeIntegrable_of_continuousOn hupper.continuousOn
  have hlint := edgeIntegrable_of_continuousOn hlower.continuousOn
  have hbottom := intervalIntegral.integral_add_adjacent_intervals hcint.1 hlint.1
  have htop := intervalIntegral.integral_add_adjacent_intervals hcint.2.1 huint.2.1
  have hmid : IntervalIntegrable (fun y => g ((a : ℂ) + y * Complex.I)) volume (-ε) ε :=
    hcint.2.2.1.mono_set (by
      rw [uIcc_of_le (by linarith : -ε ≤ ε), uIcc_of_le (by linarith : -r ≤ r)]
      exact Icc_subset_Icc (neg_le_neg her) her)
  have hfirst := intervalIntegral.integral_add_adjacent_intervals hlint.2.2.2 hmid
  have hlast := intervalIntegral.integral_add_adjacent_intervals
    (hlint.2.2.2.trans hmid) huint.2.2.2
  simp only [boundary, outer, banks, gap, quotient, g, sub_eq_add_neg,
    Complex.ofReal_neg, neg_mul] at hc hu hl hbottom htop hfirst hlast ⊢
  linear_combination hc + hu + hl + Complex.I * hfirst + Complex.I * hlast - hbottom + htop

theorem continuous_quotient_vertical {f : ℂ → ℂ} {H a z : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (ha : a < H) (haz : a ≠ z) :
    Continuous (fun y : ℝ => quotient f z ((a : ℂ) + y * Complex.I)) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have hw : (a : ℂ) + y * Complex.I ∈ domain H := Or.inl (by simpa using ha)
  have hn : (a : ℂ) + y * Complex.I - z ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp at hre
    exact haz (sub_eq_zero.mp hre)
  have hc : ContinuousAt (quotient f z) ((a : ℂ) + y * Complex.I) :=
    (hf.differentiableAt ((isOpen_domain H).mem_nhds hw)).continuousAt.div
      (continuousAt_id.sub_const (z : ℂ)) hn
  exact ContinuousAt.comp (f := fun u : ℝ => (a : ℂ) + u * Complex.I) hc (by fun_prop)

theorem gap_tendsto_zero {g : ℂ → ℂ} {a : ℝ}
    (hg : Continuous (fun y : ℝ => g ((a : ℂ) + y * Complex.I))) :
    Tendsto (gap g a) (𝓝 (0 : ℝ)) (𝓝 0) := by
  let P (b : ℝ) := ∫ y in (0 : ℝ)..b, g ((a : ℂ) + y * Complex.I)
  have hp : Continuous P := intervalIntegral.continuous_primitive
    (μ := volume) (fun x y => hg.intervalIntegrable x y) 0
  have he (ε : ℝ) : gap g a ε = Complex.I * (P ε - P (-ε)) := by
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hg.intervalIntegrable 0 (-ε)) (hg.intervalIntegrable (-ε) ε)
    unfold gap P
    congr 1
    linear_combination hi
  rw [show gap g a = fun ε => Complex.I * (P ε - P (-ε)) from funext he]
  convert (continuous_const.mul (hp.sub (hp.comp continuous_neg))).continuousAt.tendsto using 1
  simp

theorem physical_gap_tendsto_zero {f : ℂ → ℂ} {H a z : ℝ}
    (hf : DifferentiableOn ℂ f (domain H)) (ha : a < H) (haz : a ≠ z) :
    Tendsto (gap (quotient f z) a) (𝓝 (0 : ℝ)) (𝓝 0) :=
  gap_tendsto_zero (continuous_quotient_vertical hf ha haz)

/-- A uniform bound outside a circle controls every surviving outer edge.
The bound is independent of the thickness of the removed slit. -/
theorem norm_outer_le {g : ℂ → ℂ} {H R ε B : ℝ}
    (hR : 0 < R) (hRH : -R < H) (he : 0 < ε) (her : ε ≤ R) (hB : 0 ≤ B)
    (hg : ∀ w ∈ domain H, R ≤ ‖w‖ → ‖g w‖ ≤ B) :
    ‖outer g (-R) R R ε‖ ≤ 8 * R * B := by
  have hhor (x : ℝ) : R ≤ ‖(x : ℂ) + R * Complex.I‖ := by
    simpa [abs_of_pos hR] using Complex.abs_im_le_norm ((x : ℂ) + R * Complex.I)
  have hhor' (x : ℝ) : R ≤ ‖(x : ℂ) - R * Complex.I‖ := by
    simpa [abs_of_pos hR] using Complex.abs_im_le_norm ((x : ℂ) - R * Complex.I)
  have hvert (y : ℝ) : R ≤ ‖(R : ℂ) + y * Complex.I‖ := by
    simpa [abs_of_pos hR] using Complex.abs_re_le_norm ((R : ℂ) + y * Complex.I)
  have hvert' (y : ℝ) : R ≤ ‖(-R : ℂ) + y * Complex.I‖ := by
    simpa [abs_of_pos hR] using Complex.abs_re_le_norm ((-R : ℂ) + y * Complex.I)
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -R) (b := R) (fun x _ => hg _ (Or.inr (by simpa using neg_ne_zero.mpr hR.ne')) (hhor' x))
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -R) (b := R) (fun x _ => hg _ (Or.inr (by simpa using hR.ne')) (hhor x))
  have h3 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := ε) (b := R) (fun y hy => hg _ (Or.inr (by
      have hy' := (uIoc_of_le her ▸ hy).1
      simpa using (he.trans hy').ne')) (hvert y))
  have h4 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -R) (b := -ε) (fun y hy => hg _ (Or.inr (by
      have hy' := (uIoc_of_le (neg_le_neg her) ▸ hy).2
      simpa using (hy'.trans_lt (neg_neg_of_pos he)).ne)) (hvert y))
  have h5 := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -R) (b := R) (fun y _ => hg _ (Or.inl (by simpa using hRH)) (hvert' y))
  have habs1 : |R - -R| = 2 * R := by rw [abs_of_nonneg (by linarith)]; ring
  have habs2 : |R - ε| = R - ε := abs_of_nonneg (sub_nonneg.mpr her)
  have habs3 : |-ε - -R| = R - ε := by
    rw [abs_of_nonneg (by linarith)]; ring
  rw [habs1] at h1 h2 h5
  rw [habs2] at h3
  rw [habs3] at h4
  have hn1 := norm_sub_le
    (∫ x in (-R)..R, g ((x : ℂ) - R * Complex.I))
    (∫ x in (-R)..R, g ((x : ℂ) + R * Complex.I))
  unfold outer
  simp only [Complex.ofReal_neg]
  calc
    _ ≤ ‖(∫ x in (-R)..R, g ((x : ℂ) - R * Complex.I)) -
          (∫ x in (-R)..R, g ((x : ℂ) + R * Complex.I))‖ +
        ‖Complex.I * (∫ y in ε..R, g ((R : ℂ) + y * Complex.I))‖ +
        ‖Complex.I * (∫ y in (-R)..(-ε), g ((R : ℂ) + y * Complex.I))‖ +
        ‖Complex.I * (∫ y in (-R)..R, g ((-R : ℂ) + y * Complex.I))‖ := by
          exact (norm_sub_le _ _).trans (add_le_add_right
            ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)) _)
    _ ≤ 8 * R * B := by
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.ofReal_neg]
      nlinarith [mul_nonneg he.le hB]

theorem norm_quotient_le_of_decay {f : ℂ → ℂ} {H C α R₀ R z : ℝ}
    (hC : 0 ≤ C) (hα : 0 < α) (hR : 0 < R) (hR₀ : R₀ ≤ R)
    (hz : 2 * |z| ≤ R)
    (hdecay : ∀ w ∈ domain H, R₀ ≤ ‖w‖ → ‖f w‖ ≤ C * ‖w‖ ^ (-α)) :
    ∀ w ∈ domain H, R ≤ ‖w‖ →
      ‖quotient f z w‖ ≤ 2 * C * R ^ (-α) / R := by
  intro w hw hRw
  have hnorm : R / 2 ≤ ‖w - (z : ℂ)‖ := by
    have htri := norm_add_le (w - (z : ℂ)) (z : ℂ)
    rw [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs] at htri
    linarith
  have hfbound : ‖f w‖ ≤ C * R ^ (-α) :=
    (hdecay w hw (hR₀.trans hRw)).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hR hRw (neg_nonpos.mpr hα.le)) hC)
  unfold quotient
  rw [norm_div]
  calc
    _ ≤ (C * R ^ (-α)) / (R / 2) := div_le_div₀
      (mul_nonneg hC (Real.rpow_nonneg hR.le _)) hfbound (half_pos hR) hnorm
    _ = _ := by ring

/-- The actual outer contour vanishes at the paper's stated power-decay
rate, uniformly in the slit thickness. -/
theorem norm_outer_quotient_le {f : ℂ → ℂ} {H C α R₀ R z ε : ℝ}
    (hC : 0 ≤ C) (hα : 0 < α) (hR : 0 < R) (hRH : -R < H)
    (hR₀ : R₀ ≤ R) (hz : 2 * |z| ≤ R) (he : 0 < ε) (her : ε ≤ R)
    (hdecay : ∀ w ∈ domain H, R₀ ≤ ‖w‖ → ‖f w‖ ≤ C * ‖w‖ ^ (-α)) :
    ‖outer (quotient f z) (-R) R R ε‖ ≤ 16 * C * R ^ (-α) := by
  have hb : 0 ≤ 2 * C * R ^ (-α) / R := by positivity
  have he := norm_outer_le hR hRH he her hb
    (norm_quotient_le_of_decay hC hα hR hR₀ hz hdecay)
  convert he using 1
  field_simp
  ring

theorem outer_bound_tendsto_zero (C : ℝ) {α : ℝ} (hα : 0 < α) :
    Tendsto (fun R : ℝ => 16 * C * R ^ (-α)) atTop (𝓝 0) := by
  simpa using (tendsto_rpow_neg_atTop hα).const_mul (16 * C)

end LeanVerification.SlitContour
