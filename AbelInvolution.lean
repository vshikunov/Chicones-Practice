import LeanVerification.AbelCauchyKernel
import Mathlib.MeasureTheory.Integral.Prod

/-! The convergent Abel involution, including the exact inner beta integral. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace LeanVerification.AbelInvolution
set_option maxHeartbeats 1500000
set_option maxRecDepth 4000

def betaKernel (a b t : ℝ) : ℝ :=
  1/(Real.sqrt (t-a)*Real.sqrt (b-t))

def betaPrimitive (a b t : ℝ) : ℝ :=
  2*Real.arcsin (Real.sqrt ((t-a)/(b-a)))

theorem hasDerivAt_betaPrimitive {a b t : ℝ} (ht : t∈Ioo a b) :
    HasDerivAt (betaPrimitive a b) (betaKernel a b t) t := by
  have hab : 0<b-a := by linarith [ht.1,ht.2]
  have hta : 0<t-a := sub_pos.mpr ht.1
  have hbt : 0<b-t := sub_pos.mpr ht.2
  let q := (t-a)/(b-a)
  have hq : 0<q := div_pos hta hab
  have hq1 : q<1 := (div_lt_one hab).mpr (by linarith)
  have h1q : 1-q=(b-t)/(b-a) := by dsimp only [q]; field_simp
  have hprod : Real.sqrt q*Real.sqrt (1-q)=
      Real.sqrt (t-a)*Real.sqrt (b-t)/(b-a) := by
    rw [h1q]
    dsimp only [q]
    rw [Real.sqrt_div hta.le,Real.sqrt_div hbt.le]
    have hs := Real.sq_sqrt hab.le
    have hsp : Real.sqrt (b-a)≠0 := (Real.sqrt_pos.mpr hab).ne'
    field_simp only [hsp,hab.ne']
    rw [←pow_two,hs]
  have hs0 : Real.sqrt q≠-1 := by linarith [Real.sqrt_nonneg q]
  have hs1 : Real.sqrt q≠1 := by
    intro hs
    have hsq := Real.sq_sqrt hq.le
    rw [hs] at hsq
    linarith
  have hdq := ((hasDerivAt_id t).sub_const a).div_const (b-a)
  have hd := ((Real.hasDerivAt_arcsin hs0 hs1).comp t (hdq.sqrt hq.ne')).const_mul 2
  convert hd using 1
  change 1/(Real.sqrt (t-a)*Real.sqrt (b-t))=
    2*((1/Real.sqrt (1-(Real.sqrt q)^2))*((1/(b-a))/(2*Real.sqrt q)))
  rw [Real.sq_sqrt hq.le]
  have hs : Real.sqrt q≠0 := (Real.sqrt_pos.mpr hq).ne'
  have hs' : Real.sqrt (1-q)≠0 := (Real.sqrt_pos.mpr (sub_pos.mpr hq1)).ne'
  have he : 2*((1/Real.sqrt (1-q))*((1/(b-a))/(2*Real.sqrt q)))=
      1/((b-a)*(Real.sqrt q*Real.sqrt (1-q))) := by
    field_simp only [hs,hs',hab.ne']
    ring
  rw [he,hprod]
  field_simp only [hab.ne']
  ring

theorem continuous_betaPrimitive (a b : ℝ) : Continuous (betaPrimitive a b) := by
  exact continuous_const.mul (Real.continuous_arcsin.comp (Real.continuous_sqrt.comp
    ((continuous_id.sub continuous_const).div_const _)))

theorem intervalIntegrable_betaKernel {a b : ℝ} (hab : a<b) :
    IntervalIntegrable (betaKernel a b) volume a b := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    ((continuous_betaPrimitive a b).continuousOn)
  · intro t ht
    simp only [min_eq_left hab.le,max_eq_right hab.le] at ht
    exact hasDerivAt_betaPrimitive ht
  · intro t ht
    exact div_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem integral_betaKernel {a b : ℝ} (hab : a<b) :
    (∫ t in Ioo a b,betaKernel a b t)=Real.pi := by
  rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
      (continuous_betaPrimitive a b).continuousOn (fun t ht => hasDerivAt_betaPrimitive ht)
      (intervalIntegrable_betaKernel hab)]
  simp [betaPrimitive,(sub_pos.mpr hab).ne',Real.arcsin_one]
  ring

def transform (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in Ioo (0 : ℝ) t,f s/Real.sqrt (t-s)

def triangleKernel (f : ℝ → ℝ) (h : ℝ) (p : ℝ × ℝ) : ℝ :=
  if p.1<p.2 then f p.1*betaKernel p.1 h p.2 else 0

theorem measurable_triangleKernel {f : ℝ → ℝ} (hf : Measurable f) (h : ℝ) :
    Measurable (triangleKernel f h) := by
  unfold triangleKernel betaKernel
  apply Measurable.ite (isOpen_lt continuous_fst continuous_snd).measurableSet
  · exact (hf.comp measurable_fst).mul (measurable_const.div
      (((measurable_snd.sub measurable_fst).sqrt).mul
        ((measurable_const.sub measurable_snd).sqrt)))
  · exact measurable_const

theorem triangle_row_eq {f : ℝ → ℝ} {h s : ℝ} (hs : s∈Ioo 0 h) :
    (∫ t in Ioo (0 : ℝ) h,triangleKernel f h (s,t))=Real.pi*f s := by
  have he : (fun t => triangleKernel f h (s,t))=
      (Ioi s).indicator (fun t => f s*betaKernel s h t) := by
    funext t
    simp only [triangleKernel,indicator,mem_Ioi]
  rw [he,integral_indicator measurableSet_Ioi,Measure.restrict_restrict measurableSet_Ioi]
  have hi : Ioi s ∩ Ioo (0 : ℝ) h=Ioo s h := by
    ext t
    simp only [mem_inter_iff,mem_Ioi,mem_Ioo]
    constructor <;> intro ht
    · exact ⟨ht.1,ht.2.2⟩
    · exact ⟨ht.1,hs.1.trans ht.1,ht.2⟩
  rw [hi,integral_const_mul,integral_betaKernel hs.2]
  ring

theorem integrable_triangle_row {f : ℝ → ℝ} {h s : ℝ} (hs : s∈Ioo 0 h) :
    Integrable (fun t => triangleKernel f h (s,t)) (volume.restrict (Ioo 0 h)) := by
  have he : (fun t => triangleKernel f h (s,t))=
      (Ioi s).indicator (fun t => f s*betaKernel s h t) := by
    funext t
    simp only [triangleKernel,indicator,mem_Ioi]
  rw [he,integrable_indicator_iff measurableSet_Ioi,IntegrableOn,Measure.restrict_restrict measurableSet_Ioi]
  have hi : Ioi s ∩ Ioo (0 : ℝ) h=Ioo s h := by
    ext t
    simp only [mem_inter_iff,mem_Ioi,mem_Ioo]
    constructor <;> intro ht
    · exact ⟨ht.1,ht.2.2⟩
    · exact ⟨ht.1,hs.1.trans ht.1,ht.2⟩
  rw [hi]
  exact ((intervalIntegrable_betaKernel hs.2).1.mono_set Ioo_subset_Ioc_self).const_mul _

theorem triangle_row_norm {f : ℝ → ℝ} {h s : ℝ} (hs : s∈Ioo 0 h) :
    (∫ t in Ioo (0 : ℝ) h,‖triangleKernel f h (s,t)‖)=Real.pi*‖f s‖ := by
  have he : (fun t => ‖triangleKernel f h (s,t)‖)=
      (fun t => triangleKernel (fun x => ‖f x‖) h (s,t)) := by
    funext t
    simp only [triangleKernel]
    split_ifs
    · have hb : 0≤betaKernel s h t := div_nonneg zero_le_one
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      rw [norm_mul,Real.norm_of_nonneg hb]
    · simp
  rw [he,triangle_row_eq hs]

theorem integrable_triangleKernel {f : ℝ → ℝ} {h : ℝ} (hf : Measurable f)
    (hi : IntegrableOn f (Ioo 0 h)) :
    Integrable (triangleKernel f h)
      ((volume.restrict (Ioo 0 h)).prod (volume.restrict (Ioo 0 h))) := by
  apply (integrable_prod_iff (measurable_triangleKernel hf h).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact integrable_triangle_row hs
  · apply (hi.norm.const_mul Real.pi).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (triangle_row_norm hs).symm

theorem triangle_column_eq {f : ℝ → ℝ} {h t : ℝ} (ht : t∈Ioo 0 h) :
    (∫ s in Ioo (0 : ℝ) h,triangleKernel f h (s,t))=transform f t/Real.sqrt (h-t) := by
  have he : (fun s => triangleKernel f h (s,t))=
      (Iio t).indicator (fun s => f s*betaKernel s h t) := by
    funext s
    simp only [triangleKernel,indicator,mem_Iio]
  rw [he,integral_indicator measurableSet_Iio,Measure.restrict_restrict measurableSet_Iio]
  have hi : Iio t ∩ Ioo (0 : ℝ) h=Ioo 0 t := by
    ext s
    simp only [mem_inter_iff,mem_Iio,mem_Ioo]
    constructor <;> intro hs
    · exact ⟨hs.2.1,hs.1⟩
    · exact ⟨hs.2,hs.1,hs.2.trans ht.2⟩
  rw [hi,transform,←integral_div]
  apply integral_congr_ae
  filter_upwards with s
  simp only [betaKernel]
  simp only [div_eq_mul_inv,mul_inv]
  ring

/-- The double Abel transform is absolutely integrable and equals pi times
the original integral. The triangle Fubini hypotheses follow from the
original L1 input and the proved beta identity. -/
theorem transform_twice {f : ℝ → ℝ} {h : ℝ} (hf : Measurable f)
    (hi : IntegrableOn f (Ioo 0 h)) :
    IntegrableOn (fun t => transform f t/Real.sqrt (h-t)) (Ioo 0 h) ∧
    transform (transform f) h=Real.pi*∫ s in Ioo (0 : ℝ) h,f s := by
  have hip := integrable_triangleKernel hf hi
  have he : (fun t => ∫ s in Ioo (0 : ℝ) h,triangleKernel f h (s,t))=ᵐ[volume.restrict (Ioo 0 h)]
      (fun t => transform f t/Real.sqrt (h-t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact triangle_column_eq ht
  refine ⟨hip.integral_prod_right.congr he,?_⟩
  rw [transform,←integral_congr_ae he,←integral_integral_swap (f := fun s t => triangleKernel f h (s,t)) hip,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  exact triangle_row_eq hs

end LeanVerification.AbelInvolution
