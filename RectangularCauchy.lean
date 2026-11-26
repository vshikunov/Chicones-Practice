import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.RectangularCauchy

/-- The positively oriented integral around a rectangle. -/
def boundary (f : ℂ → ℂ) (a b c d : ℝ) : ℂ :=
  (∫ x in a..b, f ((x : ℂ) + c * Complex.I)) -
  (∫ x in a..b, f ((x : ℂ) + d * Complex.I)) +
  Complex.I * (∫ y in c..d, f ((b : ℂ) + y * Complex.I)) -
  Complex.I * (∫ y in c..d, f ((a : ℂ) + y * Complex.I))

theorem log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im,
    Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]

theorem log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Complex.log_re, Complex.log_im,
    Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]

theorem integral_horizontal_inv (a b y z : ℝ) (hy : y ≠ 0) :
    (∫ x in a..b, (((x : ℂ) + y * Complex.I - z)⁻¹)) =
      Complex.log ((b : ℂ) + y * Complex.I - z) -
        Complex.log ((a : ℂ) + y * Complex.I - z) := by
  have hs (x : ℝ) : (x : ℂ) + y * Complex.I - z ∈ Complex.slitPlane := by
    right
    simpa using hy
  have hd (x : ℝ) : HasDerivAt
      (fun u : ℝ => Complex.log ((u : ℂ) + y * Complex.I - z))
      (((x : ℂ) + y * Complex.I - z)⁻¹) x := by
    simpa using ((Complex.ofRealCLM.hasDerivAt.add_const
      ((y : ℂ) * Complex.I)).sub_const (z : ℂ)).clog_real (hs x)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hd x)
  have hc : Continuous (fun x : ℝ => ((x : ℂ) + y * Complex.I - z)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    exact fun x => Complex.slitPlane_ne_zero (hs x)
  exact hc.intervalIntegrable a b

theorem integral_vertical_inv_right (c d b z : ℝ) (hb : z < b) :
    Complex.I * (∫ y in c..d, (((b : ℂ) + y * Complex.I - z)⁻¹)) =
      Complex.log ((b : ℂ) + d * Complex.I - z) -
        Complex.log ((b : ℂ) + c * Complex.I - z) := by
  have hs (y : ℝ) : (b : ℂ) + y * Complex.I - z ∈ Complex.slitPlane := by
    left
    simpa using sub_pos.mpr hb
  have hd (y : ℝ) : HasDerivAt
      (fun u : ℝ => Complex.log ((b : ℂ) + u * Complex.I - z))
      (Complex.I * ((b : ℂ) + y * Complex.I - z)⁻¹) y := by
    convert ((Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).const_add
      (b : ℂ) |>.sub_const (z : ℂ)).clog_real (hs y) using 1 <;> simp [div_eq_mul_inv]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hd y)
  have hc : Continuous (fun y : ℝ => Complex.I * ((b : ℂ) + y * Complex.I - z)⁻¹) := by
    apply continuous_const.mul
    apply Continuous.inv₀ (by fun_prop)
    exact fun y => Complex.slitPlane_ne_zero (hs y)
  exact hc.intervalIntegrable c d

theorem integral_vertical_inv_left (c d a z : ℝ) (ha : a < z) :
    Complex.I * (∫ y in c..d, (((a : ℂ) + y * Complex.I - z)⁻¹)) =
      Complex.log (-((a : ℂ) + d * Complex.I - z)) -
        Complex.log (-((a : ℂ) + c * Complex.I - z)) := by
  have hs (y : ℝ) : -((a : ℂ) + y * Complex.I - z) ∈ Complex.slitPlane := by
    left
    simpa using sub_pos.mpr ha
  have hn (y : ℝ) : (a : ℂ) + y * Complex.I - z ≠ 0 := by
    exact neg_ne_zero.mp (Complex.slitPlane_ne_zero (hs y))
  have hd (y : ℝ) : HasDerivAt
      (fun u : ℝ => Complex.log (-((a : ℂ) + u * Complex.I - z)))
      (Complex.I * ((a : ℂ) + y * Complex.I - z)⁻¹) y := by
    convert ((Complex.ofRealCLM.hasDerivAt.mul_const Complex.I).const_add
      (a : ℂ) |>.sub_const (z : ℂ) |>.neg).clog_real (hs y) using 1
    simp only [div_eq_mul_inv, neg_sub, Complex.ofRealCLM_apply, Complex.ofReal_one,
      one_mul]
    rw [show (z : ℂ) - ((a : ℂ) + y * Complex.I) =
      -((a : ℂ) + y * Complex.I - z) by ring, inv_neg]
    ring
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hd y)
  have hc : Continuous (fun y : ℝ => Complex.I * ((a : ℂ) + y * Complex.I - z)⁻¹) := by
    apply continuous_const.mul
    exact Continuous.inv₀ (by fun_prop) hn
  exact hc.intervalIntegrable c d

/-- The rectangle's pole coefficient is computed from explicit logarithmic
primitives, including the two different branch jumps on its left edge. -/
theorem boundary_inv {a b c d z : ℝ}
    (ha : a < z) (hb : z < b) (hc : c < 0) (hd : 0 < d) :
    boundary (fun w => (w - z)⁻¹) a b c d =
      2 * (Real.pi : ℂ) * Complex.I := by
  unfold boundary
  rw [integral_horizontal_inv a b c z hc.ne,
    integral_horizontal_inv a b d z hd.ne',
    integral_vertical_inv_right c d b z hb,
    integral_vertical_inv_left c d a z ha,
    log_neg_of_im_pos (by simpa using hd : 0 < ((a : ℂ) + d * Complex.I - z).im),
    log_neg_of_im_neg (by simpa using hc : ((a : ℂ) + c * Complex.I - z).im < 0)]
  ring

def EdgeIntegrable (f : ℂ → ℂ) (a b c d : ℝ) : Prop :=
  IntervalIntegrable (fun x => f ((x : ℂ) + c * Complex.I)) volume a b ∧
  IntervalIntegrable (fun x => f ((x : ℂ) + d * Complex.I)) volume a b ∧
  IntervalIntegrable (fun y => f ((b : ℂ) + y * Complex.I)) volume c d ∧
  IntervalIntegrable (fun y => f ((a : ℂ) + y * Complex.I)) volume c d

theorem edgeIntegrable_of_continuousOn {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : ContinuousOn f (uIcc a b ×ℂ uIcc c d)) : EdgeIntegrable f a b c d := by
  have hh (y : ℝ) (hy : y ∈ uIcc c d) :
      ContinuousOn (fun x : ℝ => f ((x : ℂ) + y * Complex.I)) (uIcc a b) := by
    apply hf.comp (by fun_prop) ?_
    intro x hx
    simpa [Complex.mem_reProdIm] using And.intro hx hy
  have hv (x : ℝ) (hx : x ∈ uIcc a b) :
      ContinuousOn (fun y : ℝ => f ((x : ℂ) + y * Complex.I)) (uIcc c d) := by
    apply hf.comp (by fun_prop) ?_
    intro y hy
    simpa [Complex.mem_reProdIm] using And.intro hx hy
  exact ⟨(hh c left_mem_uIcc).intervalIntegrable,
    (hh d right_mem_uIcc).intervalIntegrable,
    (hv b right_mem_uIcc).intervalIntegrable,
    (hv a left_mem_uIcc).intervalIntegrable⟩

theorem edgeIntegrable_inv {a b c d z : ℝ}
    (ha : a < z) (hb : z < b) (hc : c < 0) (hd : 0 < d) :
    EdgeIntegrable (fun w => (w - z)⁻¹) a b c d := by
  have hh (y : ℝ) (hy : y ≠ 0) :
      Continuous (fun x : ℝ => ((x : ℂ) + y * Complex.I - z)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x
    exact Complex.slitPlane_ne_zero (Or.inr (by simpa using hy))
  have hv (x : ℝ) (hx : x ≠ z) :
      Continuous (fun y : ℝ => ((x : ℂ) + y * Complex.I - z)⁻¹) := by
    apply Continuous.inv₀ (by fun_prop)
    intro y he
    have hre := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero, Complex.zero_re] at hre
    exact hx (sub_eq_zero.mp hre)
  exact ⟨(hh c hc.ne).intervalIntegrable a b,
    (hh d hd.ne').intervalIntegrable a b,
    (hv b hb.ne').intervalIntegrable c d,
    (hv a ha.ne).intervalIntegrable c d⟩

theorem EdgeIntegrable.const_mul {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : EdgeIntegrable f a b c d) (q : ℂ) :
    EdgeIntegrable (fun w => q * f w) a b c d :=
  ⟨hf.1.const_mul q, hf.2.1.const_mul q, hf.2.2.1.const_mul q,
    hf.2.2.2.const_mul q⟩

theorem boundary_add {f g : ℂ → ℂ} {a b c d : ℝ}
    (hf : EdgeIntegrable f a b c d) (hg : EdgeIntegrable g a b c d) :
    boundary (fun w => f w + g w) a b c d =
      boundary f a b c d + boundary g a b c d := by
  simp only [boundary, intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

theorem boundary_const_mul (q : ℂ) (f : ℂ → ℂ) (a b c d : ℝ) :
    boundary (fun w => q * f w) a b c d = q * boundary f a b c d := by
  simp only [boundary, intervalIntegral.integral_const_mul]
  ring

theorem boundary_congr {f g : ℂ → ℂ} {a b c d : ℝ}
    (hc : ∀ x ∈ uIcc a b, f ((x : ℂ) + c * Complex.I) = g ((x : ℂ) + c * Complex.I))
    (hd : ∀ x ∈ uIcc a b, f ((x : ℂ) + d * Complex.I) = g ((x : ℂ) + d * Complex.I))
    (hb : ∀ y ∈ uIcc c d, f ((b : ℂ) + y * Complex.I) = g ((b : ℂ) + y * Complex.I))
    (ha : ∀ y ∈ uIcc c d, f ((a : ℂ) + y * Complex.I) = g ((a : ℂ) + y * Complex.I)) :
    boundary f a b c d = boundary g a b c d := by
  unfold boundary
  rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_congr hd,
    intervalIntegral.integral_congr hb, intervalIntegral.integral_congr ha]

theorem boundary_eq_zero {f : ℂ → ℂ} {a b c d : ℝ}
    (hf : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc c d)) :
    boundary f a b c d = 0 := by
  simpa [boundary] using Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f ((a : ℂ) + c * Complex.I) ((b : ℂ) + d * Complex.I) (by simpa using hf)

/-- Cauchy's integral formula for a rectangle and an interior real point.
The coefficient is evaluated from logarithms; no contour identity is assumed. -/
theorem boundary_cauchy {f : ℂ → ℂ} {a b c d z : ℝ}
    (ha : a < z) (hb : z < b) (hc : c < 0) (hd : 0 < d)
    (hf : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc c d)) :
    boundary (fun w => f w / (w - z)) a b c d =
      2 * (Real.pi : ℂ) * Complex.I * f z := by
  have hnhds : uIcc a b ×ℂ uIcc c d ∈ 𝓝 (z : ℂ) := by
    have hopen : IsOpen (Ioo a b ×ℂ Ioo c d) :=
      (isOpen_Ioo.preimage Complex.continuous_re).inter
        (isOpen_Ioo.preimage Complex.continuous_im)
    apply mem_of_superset (hopen.mem_nhds ?_) ?_
    · simpa [Complex.mem_reProdIm] using And.intro (And.intro ha hb) (And.intro hc hd)
    · intro w hw
      exact ⟨Icc_subset_uIcc (Ioo_subset_Icc_self hw.1),
        Icc_subset_uIcc (Ioo_subset_Icc_self hw.2)⟩
  have hq : DifferentiableOn ℂ (dslope f (z : ℂ)) (uIcc a b ×ℂ uIcc c d) :=
    (Complex.differentiableOn_dslope hnhds).mpr hf
  have he (w : ℂ) (hw : w ≠ (z : ℂ)) :
      f w / (w - z) = dslope f (z : ℂ) w + f z * (w - z)⁻¹ := by
    rw [dslope_of_ne f hw, slope_def_field]
    field_simp [sub_ne_zero.mpr hw]
  have hv (x y : ℝ) (hx : x ≠ z) : (x : ℂ) + y * Complex.I ≠ z := by
    intro h
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_self, add_zero] at hh
    exact hx hh
  have hh (x y : ℝ) (hy : y ≠ 0) : (x : ℂ) + y * Complex.I ≠ z := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add] at hi
    exact hy hi
  rw [boundary_congr (g := fun w => dslope f (z : ℂ) w + f z * (w - z)⁻¹)
    (fun x _ => he _ (hh x c hc.ne))
    (fun x _ => he _ (hh x d hd.ne'))
    (fun y _ => he _ (hv b y hb.ne')) (fun y _ => he _ (hv a y ha.ne)),
    boundary_add (edgeIntegrable_of_continuousOn hq.continuousOn)
      ((edgeIntegrable_inv ha hb hc hd).const_mul (f z)),
    boundary_eq_zero hq, boundary_const_mul, boundary_inv ha hb hc hd]
  ring

end LeanVerification.RectangularCauchy
