import LeanVerification.RaisedAbelCalculus
import LeanVerification.WeightedCompactDerivatives
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Positivity at a zero of the inverse-width Abel transform

The positive-part square proves terminal positivity without component topology.
All differentiation and integration by parts take place on compact angular or
unit intervals with regular analytic integrands.
-/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology

namespace LeanVerification.InverseWidthAbel
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

def positiveSquare (x : ℝ) : ℝ := (max x 0)^2

theorem hasDerivAt_positiveSquare (x : ℝ) :
    HasDerivAt positiveSquare (2*max x 0) x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have he : positiveSquare =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [eventually_lt_nhds hx] with y hy
      simp only [positiveSquare, max_eq_right hy.le, zero_pow two_ne_zero]
    rw [max_eq_right hx.le, mul_zero]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he
  · subst x
    rw [max_self, mul_zero, hasDerivAt_iff_tendsto]
    have he : (fun y : ℝ => ‖y-0‖⁻¹ * ‖positiveSquare y-positiveSquare 0-(y-0) • (0 : ℝ)‖) =
        fun y : ℝ => max y 0 := by
      funext y
      simp only [sub_zero, smul_zero, positiveSquare, max_self, zero_pow two_ne_zero,
        Real.norm_eq_abs, abs_sq]
      by_cases hy : 0 ≤ y
      · rw [max_eq_left hy, abs_of_nonneg hy]
        by_cases he : y=0
        · simp [he]
        · field_simp; ring
      · rw [max_eq_right (le_of_not_ge hy)]
        simp
    rw [he]
    simpa only [id_eq, max_self] using
      (continuous_id.max (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))).tendsto (0 : ℝ)
  · have he : positiveSquare =ᶠ[𝓝 x] (fun y : ℝ => y^2) := by
      filter_upwards [eventually_gt_nhds hx] with y hy
      simp only [positiveSquare, max_eq_left hy.le]
    rw [max_eq_left hx.le]
    exact (by convert (hasDerivAt_id x).pow 2 using 1; norm_num :
      HasDerivAt (fun y : ℝ => y^2) (2*x) x).congr_of_eventuallyEq he

/-- A nonnegative derivative on the positive set makes the squared positive
part globally nondecreasing on the interval. -/
theorem monotone_positiveSquare {z : ℝ → ℝ} {H : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H))
    (hd : ∀ s ∈ Icc 0 H, 0 < z s → 0 ≤ deriv z s) :
    MonotoneOn (fun s => positiveSquare (z s)) (Icc 0 H) := by
  have hder (s : ℝ) (hs : s ∈ Icc 0 H) :
      HasDerivAt (fun t => positiveSquare (z t))
        ((2*max (z s) 0)*deriv z s) s :=
    (hasDerivAt_positiveSquare (z s)).comp s (hz s hs).differentiableAt.hasDerivAt
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 H)
  · exact fun s hs => (hder s hs).continuousAt.continuousWithinAt
  · intro s hs
    exact (hder s (interior_subset hs)).hasDerivWithinAt
  · intro s hs
    by_cases hpos : 0 < z s
    · exact mul_nonneg (by positivity) (hd s (interior_subset hs) hpos)
    · simp only [max_eq_right (le_of_not_gt hpos), mul_zero, zero_mul, le_refl]

theorem positive_value_persists {z : ℝ → ℝ} {H s h : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H))
    (hd : ∀ s ∈ Icc 0 H, 0 < z s → 0 ≤ deriv z s)
    (hs : s ∈ Icc 0 H) (hh : h ∈ Icc 0 H) (hsh : s ≤ h) (hpos : 0 < z s) :
    0 < z h ∧ z s ≤ z h := by
  have hm := monotone_positiveSquare hz hd hs hh hsh
  dsimp only [positiveSquare] at hm
  rw [max_eq_left hpos.le] at hm
  have hp : 0 < z h := by
    by_contra hn
    rw [max_eq_right (le_of_not_gt hn)] at hm
    nlinarith
  rw [max_eq_left hp.le] at hm
  exact ⟨hp, by nlinarith⟩

theorem value_le_positive_endpoint {z : ℝ → ℝ} {H s h : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H))
    (hd : ∀ s ∈ Icc 0 H, 0 < z s → 0 ≤ deriv z s)
    (hs : s ∈ Icc 0 H) (hh : h ∈ Icc 0 H) (hsh : s ≤ h) (hpos : 0 < z h) :
    z s ≤ z h := by
  by_cases hp : 0 < z s
  · exact (positive_value_persists hz hd hs hh hsh hp).2
  · exact (le_of_not_gt hp).trans hpos.le

/-- Joint analytic kernels on a fixed compact interval discharge all hypotheses
for ordinary scalar differentiation under that interval integral. -/
theorem joint_integral_hasDerivAt {f : ℝ × ℝ → ℝ} {x a b : ℝ} {d : ℝ → ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, AnalyticAt ℝ f (x,t))
    (hd : ∀ t ∈ Icc a b, HasDerivAt (fun y => f (y,t)) (d t) x) :
    AnalyticAt ℝ (fun y => ∫ t in a..b, f (y,t)) x ∧
    HasDerivAt (fun y => ∫ t in a..b, f (y,t)) (∫ t in a..b, d t) x := by
  have hi := WeightedCompactIntegral.weightedIntegral_all_derivatives_on_compact
    (K := Icc a b) (S := Ioc a b) (ω := fun _ => (1 : ℝ)) isCompact_Icc hf
    measurableSet_Ioc Ioc_subset_Icc_self (integrable_const 1)
  simp only [one_mul] at hi
  have he := (hi.2.2 1 (fun _ => (1 : ℝ))).2
  simp only [iteratedFDeriv_one_apply, fderiv_deriv] at he
  have hed : (∫ t in Ioc a b, deriv (fun y => f (y,t)) x) = ∫ t in Ioc a b, d t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (hd t (Ioc_subset_Icc_self ht)).deriv
  rw [hed] at he
  have hda := hi.1.differentiableAt.hasDerivAt
  rw [he] at hda
  simpa only [intervalIntegral.integral_of_le hab] using And.intro hi.1 hda

def slopeAverage (z : ℝ → ℝ) (h s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv z (h+t*(s-h))

def angularAbel (z : ℝ → ℝ) (h : ℝ) : ℝ :=
  2 * ∫ θ in (0 : ℝ)..Real.pi/2, z (h*Real.sin θ^2)

theorem segment_mem {H h s t : ℝ} (hh : h ∈ Icc 0 H) (hs : s ∈ Icc 0 H)
    (ht : t ∈ Icc 0 1) : h+t*(s-h) ∈ Icc 0 H := by
  constructor
  · nlinarith [mul_nonneg ht.1 hs.1, mul_nonneg (sub_nonneg.mpr ht.2) hh.1]
  · nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hs.2),
      mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hh.2)]

theorem slopeAverage_analytic_derivative {z : ℝ → ℝ} {H h s : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H)) (hh : h ∈ Icc 0 H) (hs : s ∈ Icc 0 H) :
    AnalyticAt ℝ (slopeAverage z h) s ∧
    HasDerivAt (slopeAverage z h)
      (∫ t in (0 : ℝ)..1, deriv (deriv z) (h+t*(s-h))*t) s := by
  apply joint_integral_hasDerivAt (f := fun p : ℝ × ℝ => deriv z (h+p.2*(p.1-h)))
    (d := fun t => deriv (deriv z) (h+t*(s-h))*t) (x := s) (by norm_num : (0 : ℝ) ≤ 1)
  · intro t ht
    have ha : AnalyticAt ℝ (fun p : ℝ × ℝ => h+p.2*(p.1-h)) (s,t) :=
      analyticAt_const.add (analyticAt_snd.mul (analyticAt_fst.sub analyticAt_const))
    exact (hz _ (segment_mem hh hs ht)).deriv.comp_of_eq ha rfl
  · intro t ht
    have hi := (hz _ (segment_mem hh hs ht)).deriv.differentiableAt.hasDerivAt
    have hm := (((hasDerivAt_id s).sub_const h).const_mul t).const_add h
    simpa only [one_mul, mul_one] using hi.comp s hm

theorem slopeAverage_difference {z : ℝ → ℝ} {H h s : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H)) (hh : h ∈ Icc 0 H) (hs : s ∈ Icc 0 H) :
    z s-z h = (s-h)*slopeAverage z h s := by
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t => z (h+t*(s-h))) (deriv z (h+t*(s-h))*(s-h)) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    simpa only [one_mul] using
      ((hz _ (segment_mem hh hs ht)).differentiableAt.hasDerivAt).comp t
        (((hasDerivAt_id t).mul_const (s-h)).const_add h)
  have hc : ContinuousOn (fun t => deriv z (h+t*(s-h))) (Icc 0 1) :=
    ((hz.deriv).continuousOn).comp (by fun_prop) (fun t ht => segment_mem hh hs ht)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((hc.mul continuousOn_const).intervalIntegrable_of_Icc (by norm_num))
  rw [intervalIntegral.integral_mul_const] at hi
  simp only [zero_mul, one_mul, add_zero, add_sub_cancel_left] at hi
  have hhs : h+(s-h)=s := by ring
  rw [hhs] at hi
  change slopeAverage z h s*(s-h)=z s-z h at hi
  simpa only [mul_comm] using hi.symm

theorem slopeAverage_derivative_relation {z : ℝ → ℝ} {H h s : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H)) (hh : h ∈ Icc 0 H) (hs : s ∈ Icc 0 H) :
    slopeAverage z h s+(s-h)*deriv (slopeAverage z h) s = deriv z s := by
  let P := fun t : ℝ => t*deriv z (h+t*(s-h))
  let d := fun t : ℝ => deriv z (h+t*(s-h))+(s-h)*(deriv (deriv z) (h+t*(s-h))*t)
  have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt P (d t) t := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hi := (hz _ (segment_mem hh hs ht)).deriv.differentiableAt.hasDerivAt
    have hm := ((hasDerivAt_id t).mul_const (s-h)).const_add h
    convert (hasDerivAt_id t).mul (hi.comp t hm) using 1
    dsimp [P,d]
    ring
  have hc : ContinuousOn (fun t => deriv z (h+t*(s-h))) (Icc 0 1) :=
    hz.deriv.continuousOn.comp (by fun_prop) (fun t ht => segment_mem hh hs ht)
  have hcc : ContinuousOn (fun t => deriv (deriv z) (h+t*(s-h))*t) (Icc 0 1) :=
    (hz.deriv.deriv.continuousOn.comp (by fun_prop) (fun t ht => segment_mem hh hs ht)).mul continuousOn_id
  have hdc : ContinuousOn d (Icc 0 1) := hc.add (continuousOn_const.mul hcc)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hdc.intervalIntegrable_of_Icc (by norm_num))
  dsimp only [P,d] at he
  rw [intervalIntegral.integral_add (hc.intervalIntegrable_of_Icc (by norm_num))
    ((continuousOn_const.mul hcc).intervalIntegrable_of_Icc (by norm_num)),
    intervalIntegral.integral_const_mul] at he
  simp only [zero_mul, one_mul, add_zero, add_sub_cancel_left, sub_zero] at he
  rw [(slopeAverage_analytic_derivative hz hh hs).2.deriv]
  simpa only [slopeAverage, show h+(s-h)=s by ring] using he

theorem angularAbel_analytic_derivative {z : ℝ → ℝ} {H h : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H)) (hh : h ∈ Icc 0 H) :
    AnalyticAt ℝ (angularAbel z) h ∧ HasDerivAt (angularAbel z)
      (2*∫ θ in (0 : ℝ)..Real.pi/2, deriv z (h*Real.sin θ^2)*Real.sin θ^2) h := by
  have hi : AnalyticAt ℝ (fun u => ∫ θ in (0 : ℝ)..Real.pi/2, z (u*Real.sin θ^2)) h ∧
      HasDerivAt (fun u => ∫ θ in (0 : ℝ)..Real.pi/2, z (u*Real.sin θ^2))
        (∫ θ in (0 : ℝ)..Real.pi/2, deriv z (h*Real.sin θ^2)*Real.sin θ^2) h := by
    apply joint_integral_hasDerivAt (f := fun p : ℝ × ℝ => z (p.1*Real.sin p.2^2))
      (d := fun θ => deriv z (h*Real.sin θ^2)*Real.sin θ^2) (x := h)
      (by positivity : (0 : ℝ) ≤ Real.pi/2)
    · intro θ _
      have hm : AnalyticAt ℝ (fun p : ℝ × ℝ => p.1*Real.sin p.2^2) (h,θ) :=
        analyticAt_fst.mul (((Loud.analyticAt_real_sin θ).comp_of_eq analyticAt_snd rfl).pow 2)
      exact (hz _ (RaisedAbel.sin_sq_energy_mem hh θ)).comp_of_eq hm rfl
    · intro θ _
      simpa only [one_mul] using
        ((hz _ (RaisedAbel.sin_sq_energy_mem hh θ)).differentiableAt.hasDerivAt).comp h
          ((hasDerivAt_id h).mul_const (Real.sin θ^2))
  exact ⟨analyticAt_const.mul hi.1, hi.2.const_mul 2⟩


/-- The apparent singular divided difference has a regular angular primitive.
Its endpoint values vanish, so integration by parts has no boundary term. -/
theorem angularAbel_derivative_slopeAverage {z : ℝ → ℝ} {H h : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H)) (hh : h ∈ Icc 0 H) (hh0 : 0 < h) :
    deriv (angularAbel z) h =
      ∫ θ in (0 : ℝ)..Real.pi/2, slopeAverage z h (h*Real.sin θ^2) := by
  let A := slopeAverage z h
  let p := fun θ : ℝ => -h*Real.sin θ*Real.cos θ*A (h*Real.sin θ^2)
  let d := fun θ : ℝ => h*(2*(deriv z (h*Real.sin θ^2)*Real.sin θ^2)-A (h*Real.sin θ^2))
  have hAd (s : ℝ) (hs : s ∈ Icc 0 H) : HasDerivAt A (deriv A s) s :=
    (slopeAverage_analytic_derivative hz hh hs).1.differentiableAt.hasDerivAt
  have hd : ∀ θ : ℝ, HasDerivAt p (d θ) θ := by
    intro θ
    have hs := RaisedAbel.sin_sq_energy_mem hh θ
    have harg := ((Real.hasDerivAt_sin θ).pow 2).const_mul h
    have hp := ((((Real.hasDerivAt_sin θ).const_mul (-h)).mul
      (Real.hasDerivAt_cos θ)).mul ((hAd _ hs).comp θ harg))
    apply hp.congr_deriv
    have he := slopeAverage_derivative_relation hz hh hs
    have htrig := Real.sin_sq_add_cos_sq θ
    simp only [d, Function.comp_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    change A (h*Real.sin θ^2)+(h*Real.sin θ^2-h)*deriv A (h*Real.sin θ^2)=
      deriv z (h*Real.sin θ^2) at he
    linear_combination
      (2*h*Real.sin θ^2)*he -
      (h*A (h*Real.sin θ^2)+2*h^2*Real.sin θ^2*deriv A (h*Real.sin θ^2))*htrig
  have hAc : Continuous (fun θ => A (h*Real.sin θ^2)) :=
    RaisedAbel.continuous_angle (fun s hs =>
      (slopeAverage_analytic_derivative hz hh hs).1.continuousAt.continuousWithinAt) hh
  have hzc : Continuous (fun θ => deriv z (h*Real.sin θ^2)*Real.sin θ^2) :=
    (RaisedAbel.continuous_angle hz.deriv.continuousOn hh).mul (Real.continuous_sin.pow 2)
  have hdc : Continuous d := continuous_const.mul ((continuous_const.mul hzc).sub hAc)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := Real.pi/2) (fun θ _ => hd θ)
    (hdc.intervalIntegrable _ _)
  simp only [p, Real.sin_zero, Real.cos_pi_div_two, mul_zero, zero_mul, sub_self] at hi
  dsimp only [d] at hi
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub ((continuous_const.mul hzc).intervalIntegrable _ _)
      (hAc.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at hi
  rw [(angularAbel_analytic_derivative hz hh).2.deriv]
  change h*(2*(∫ θ in (0 : ℝ)..Real.pi/2, deriv z (h*Real.sin θ^2)*Real.sin θ^2)-
    (∫ θ in (0 : ℝ)..Real.pi/2, A (h*Real.sin θ^2)))=0 at hi
  exact sub_eq_zero.mp ((mul_eq_zero.mp hi).resolve_left hh0.ne')

theorem exists_angle_energy {h s : ℝ} (hs : s ∈ Icc 0 h) :
    ∃ θ ∈ Icc (0 : ℝ) (Real.pi/2), h*Real.sin θ^2=s := by
  have hc : Continuous (fun θ : ℝ => h*Real.sin θ^2) :=
    continuous_const.mul (Real.continuous_sin.pow 2)
  apply intermediate_value_Icc (by positivity : (0 : ℝ) ≤ Real.pi/2) hc.continuousOn
  simpa only [Real.sin_zero, Real.sin_pi_div_two, zero_pow two_ne_zero, mul_zero,
    one_pow, mul_one] using hs

/-- A zero of the Abel transform of a nonzero analytic input has a positive
terminal value under the positive-set derivative hypothesis. -/
theorem positive_endpoint_of_angularAbel_zero {z : ℝ → ℝ} {H h : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H)) (hh : h ∈ Ioo 0 H)
    (hd : ∀ s ∈ Icc 0 H, 0 < z s → 0 ≤ deriv z s)
    (hn : ∃ s ∈ Icc 0 H, z s ≠ 0) (hzero : angularAbel z h=0) : 0 < z h := by
  by_contra hp
  have hnonpos : ∀ s ∈ Icc 0 h, z s ≤ 0 := by
    intro s hs
    by_contra hsp
    exact hp (positive_value_persists hz hd
      (Icc_subset_Icc le_rfl hh.2.le hs) (Ioo_subset_Icc_self hh) hs.2 (lt_of_not_ge hsp)).1
  have hcz : Continuous (fun θ => z (h*Real.sin θ^2)) :=
    RaisedAbel.continuous_angle hz.continuousOn (Ioo_subset_Icc_self hh)
  have heq : EqOn z 0 (Icc 0 h) := by
    intro s hs
    change z s=0
    apply le_antisymm (hnonpos s hs)
    by_contra hsneg
    obtain ⟨θ, hθ, hθs⟩ := exists_angle_energy hs
    have hi : (∫ θ in (0 : ℝ)..Real.pi/2, z (h*Real.sin θ^2)) < 0 := by
      have hi := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (by positivity : (0 : ℝ)<Real.pi/2) hcz.continuousOn continuousOn_const
        (fun θ _ => hnonpos _ (RaisedAbel.sin_sq_energy_mem ⟨hh.1.le,le_rfl⟩ θ))
        ⟨θ, hθ, by rw [hθs]; exact lt_of_not_ge hsneg⟩
      simpa only [intervalIntegral.integral_zero] using hi
    dsimp only [angularAbel] at hzero
    linarith
  have hmid : h/2 ∈ Icc 0 H := ⟨by linarith [hh.1], by linarith [hh.1,hh.2]⟩
  have hlocal : z =ᶠ[𝓝 (h/2)] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show h/2 ∈ Ioo 0 h by constructor <;> linarith [hh.1])]
      with s hs
    exact heq (Ioo_subset_Icc_self hs)
  have hall := hz.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    (convex_Icc (0 : ℝ) H).isPreconnected hmid hlocal
  obtain ⟨s, hs, hsn⟩ := hn
  exact hsn (hall hs)

/-- Strict upward crossing at every zero of the complete regular Abel transform.
The center condition makes the divided difference strictly positive at the
angular endpoint, which forces a strictly positive integral derivative. -/
theorem angularAbel_derivative_pos_at_zero {z : ℝ → ℝ} {H h : ℝ}
    (hz : AnalyticOnNhd ℝ z (Icc 0 H)) (hz0 : z 0=0) (hh : h ∈ Ioo 0 H)
    (hd : ∀ s ∈ Icc 0 H, 0 < z s → 0 ≤ deriv z s)
    (hn : ∃ s ∈ Icc 0 H, z s ≠ 0) (hzero : angularAbel z h=0) :
    0 < deriv (angularAbel z) h := by
  have hpos := positive_endpoint_of_angularAbel_zero hz hh hd hn hzero
  have hhc := Ioo_subset_Icc_self hh
  have hAnn : ∀ s ∈ Icc 0 h, 0 ≤ slopeAverage z h s := by
    intro s hs
    have hsH := Icc_subset_Icc le_rfl hh.2.le hs
    rcases eq_or_lt_of_le hs.2 with hsame | hsh
    · subst s
      have he := slopeAverage_derivative_relation hz hhc hhc
      simp only [sub_self, zero_mul, add_zero] at he
      rw [he]
      exact hd h hhc hpos
    · have hc := value_le_positive_endpoint hz hd hsH hhc hs.2 hpos
      have he := slopeAverage_difference hz hhc hsH
      by_contra ha
      have hm : 0 < (s-h)*slopeAverage z h s :=
        mul_pos_of_neg_of_neg (sub_neg.mpr hsh) (lt_of_not_ge ha)
      linarith
  have hA0 : 0 < slopeAverage z h 0 := by
    have he := slopeAverage_difference hz hhc (show (0 : ℝ) ∈ Icc 0 H by constructor; rfl; linarith [hh.1,hh.2])
    rw [hz0, zero_sub, zero_sub] at he
    nlinarith [hh.1]
  rw [angularAbel_derivative_slopeAverage hz hhc hh.1]
  apply intervalIntegral.integral_pos (by positivity : (0 : ℝ)<Real.pi/2)
  · exact (RaisedAbel.continuous_angle (fun s hs =>
      (slopeAverage_analytic_derivative hz hhc hs).1.continuousAt.continuousWithinAt) hhc).continuousOn
  · intro θ _
    exact hAnn _ (RaisedAbel.sin_sq_energy_mem ⟨hh.1.le,le_rfl⟩ θ)
  · refine ⟨0, ⟨le_rfl, by positivity⟩, ?_⟩
    simpa only [Real.sin_zero, zero_pow two_ne_zero, mul_zero] using hA0


end LeanVerification.InverseWidthAbel
