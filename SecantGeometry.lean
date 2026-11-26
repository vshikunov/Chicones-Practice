import LeanVerification.PositiveDCompletion.LowerCone

/-! Basic secant geometry and its exact flow on both sides of a=1. -/
noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000

theorem secantF_fraction {a q : ℝ} (ha : 0<a) (hq : 0<q) :
    secantF a q=Real.sinh (a*q)*Real.cosh q/(Real.sinh q*Real.cosh (a*q)) := by
  unfold secantF secantR
  field_simp [ha.ne',(Real.sinh_pos_iff.mpr hq).ne',(Real.cosh_pos (a*q)).ne']
  <;> ring

theorem secantF_pos {a q : ℝ} (ha : 0<a) (hq : 0<q) : 0<secantF a q := by
  rw [secantF_fraction ha hq]
  exact div_pos (mul_pos (Real.sinh_pos_iff.mpr (mul_pos ha hq)) (Real.cosh_pos q))
    (mul_pos (Real.sinh_pos_iff.mpr hq) (Real.cosh_pos (a*q)))

theorem secantRho_pos {a q : ℝ} (ha : 0<a) (hq : 0<q) : 0<secantRho a q := by
  exact sq_pos_of_pos (div_pos (Real.sinh_pos_iff.mpr (mul_pos ha hq))
    (mul_pos ha (Real.sinh_pos_iff.mpr hq)))

theorem secant_reciprocal {a q : ℝ} (ha : 0<a) (hq : 0<q) :
    secantF (1/a) (a*q)=1/secantF a q ∧
      secantRho (1/a) (a*q)=1/secantRho a q := by
  have hi : (1/a)*(a*q)=q := by field_simp
  have hs := (Real.sinh_pos_iff.mpr hq).ne'
  have hsa := (Real.sinh_pos_iff.mpr (mul_pos ha hq)).ne'
  have hc := (Real.cosh_pos q).ne'
  have hca := (Real.cosh_pos (a*q)).ne'
  constructor
  · unfold secantF secantR
    rw [hi]
    field_simp [ha.ne',hs,hsa,hc,hca]
    <;> ring
  · unfold secantRho
    rw [hi]
    field_simp [ha.ne',hs,hsa]
    <;> ring

theorem secant_lower_bounds {a q : ℝ} (ha : 1<a) (hq : 0<q) :
    1<secantF a q ∧ secantF a q<a ∧ 1<secantRho a q := by
  have ha0 : 0<a := by linarith
  have hb : 0<1/a := one_div_pos.mpr ha0
  have hbu : 1/a<1 := (div_lt_one ha0).mpr ha
  have hbq : 0<a*q := mul_pos ha0 hq
  have he := secant_reciprocal ha0 hq
  have hF := secantF_bounds hb hbu hbq
  have hR := secantRho_bounds hb hbu hbq
  rw [he.1] at hF
  rw [he.2] at hR
  have hf := secantF_pos ha0 hq
  have hr := secantRho_pos ha0 hq
  refine ⟨(div_lt_one hf).mp hF.2,?_,(div_lt_one hr).mp hR.2⟩
  have hc := (div_lt_div_iff₀ ha0 hf).mp hF.1
  simpa only [one_mul] using hc

theorem secant_g_ne_zero {a q : ℝ} (ha : 0<a) (ha1 : a≠1) (hq : 0<q) :
    1-a^2*secantRho a q≠0 := by
  rcases lt_or_gt_of_ne ha1 with hlt|hgt
  · exact (secant_g_pos ha hlt hq).ne'
  · have hr := (secant_lower_bounds hgt hq).2.2
    have ha2 : 1<a^2 := by nlinarith
    have hp := mul_lt_mul_of_pos_left hr (sq_pos_of_pos ha)
    linarith

theorem secantR_flow_general {a q : ℝ} (ha : 0<a) (ha1 : a≠1) (hq : 0<q) :
    HasDerivAt (secantR a)
      (a*Real.cosh (a*q)/Real.sinh (a*q) *
        (1+secantF a q)*(secantR a q-secantRho a q)*(1-secantF a q)/
          (1-a^2*secantRho a q)) q := by
  have hsq : 0<Real.sinh q := Real.sinh_pos_iff.mpr hq
  have hsa : 0<Real.sinh (a*q) := Real.sinh_pos_iff.mpr (mul_pos ha hq)
  have hca := Real.cosh_pos (a*q)
  have hcp := Real.cosh_pos q
  have hg := secant_g_ne_zero ha ha1 hq
  have hsaq : Real.sinh (a*q)≠Real.sinh q := by
    intro he
    have heq := Real.sinh_injective he
    have heq' : a*q=1*q := by simpa only [one_mul] using heq
    exact ha1 ((mul_right_cancel₀ hq.ne') heq')
  have hm : -Real.sinh q+Real.sinh (a*q)≠0 := by intro he;apply hsaq;linarith
  have hp : Real.sinh q+Real.sinh (a*q)≠0 := (add_pos hsq hsa).ne'
  have hgeq : 1-a^2*secantRho a q = (Real.sinh q^2-Real.sinh (a*q)^2)/Real.sinh q^2 := by
    unfold secantRho
    field_simp [ha.ne',hsq.ne']
    <;> ring
  have hgn : Real.sinh q^2-Real.sinh (a*q)^2≠0 := by
    intro he
    apply hg
    rw [hgeq,he,zero_div]
  have hd := (((Real.hasDerivAt_sinh (a*q)).comp q ((hasDerivAt_id q).const_mul a)).mul
      (Real.hasDerivAt_cosh q)).div
    (((Real.hasDerivAt_sinh q).const_mul a).mul
      ((Real.hasDerivAt_cosh (a*q)).comp q ((hasDerivAt_id q).const_mul a)))
      (mul_pos (mul_pos ha hsq) hca).ne'
  have halg :
      ((a*Real.cosh (a*q)*Real.cosh q+Real.sinh (a*q)*Real.sinh q)*
          (a*Real.sinh q*Real.cosh (a*q))-
        (Real.sinh (a*q)*Real.cosh q)*
          (a*Real.cosh q*Real.cosh (a*q)+a^2*Real.sinh q*Real.sinh (a*q)))/
            (a*Real.sinh q*Real.cosh (a*q))^2 -
      (a*Real.cosh (a*q)/Real.sinh (a*q) *
        (1+secantF a q)*(secantR a q-secantRho a q)*(1-secantF a q)/
          (1-a^2*secantRho a q)) =
      -Real.sinh (a*q)*(Real.cosh q*a*Real.sinh (a*q)-Real.sinh q*Real.cosh (a*q))*
        (Real.cosh q^2-Real.sinh q^2-Real.cosh (a*q)^2+Real.sinh (a*q)^2)/
        (Real.sinh q*a*Real.cosh (a*q)^2*(-Real.sinh q+Real.sinh (a*q))*
          (Real.sinh q+Real.sinh (a*q))) := by
    rw [hgeq]
    unfold secantF secantR secantRho
    field_simp [ha.ne',hsq.ne',hsa.ne',hca.ne',hgn,hm,hp]
    linear_combination (a^7*Real.cosh (a*q)^5*Real.sinh (a*q)^2*Real.sinh q^7*
      (Real.sinh q^2-Real.sinh (a*q)^2)*(Real.cosh (a*q)*Real.sinh q-a*Real.cosh q*Real.sinh (a*q)))*
        (Real.cosh_sq_sub_sinh_sq q)
  have hz : Real.cosh q^2-Real.sinh q^2-Real.cosh (a*q)^2+Real.sinh (a*q)^2=0 := by
    linarith [Real.cosh_sq_sub_sinh_sq q,Real.cosh_sq_sub_sinh_sq (a*q)]
  rw [hz,mul_zero,zero_div] at halg
  convert hd using 1
  dsimp only [Function.comp_apply,id_eq]
  convert (sub_eq_zero.mp halg).symm using 1 <;> ring

theorem secantRho_flow_general {a q : ℝ} (ha : 0<a) (hq : 0<q) :
    HasDerivAt (secantRho a)
      (-2*a*Real.cosh (a*q)/Real.sinh (a*q)*(secantR a q-1)*secantRho a q) q := by
  have hsq : 0<Real.sinh q := Real.sinh_pos_iff.mpr hq
  have hsa : 0<Real.sinh (a*q) := Real.sinh_pos_iff.mpr (mul_pos ha hq)
  have hca := Real.cosh_pos (a*q)
  have hd := ((((Real.hasDerivAt_sinh (a*q)).comp q ((hasDerivAt_id q).const_mul a))).div
    ((Real.hasDerivAt_sinh q).const_mul a) (mul_pos ha hsq).ne').pow 2
  convert hd using 1
  dsimp only [secantRho,secantR,id_eq,Function.comp_apply]
  field_simp [ha.ne',hsq.ne',hsa.ne',hca.ne']
  <;> ring



theorem actual_lower_cone {a q : ℝ} (ha : 1<a) (hau : a<3) (hq : 0<q) :
    1<secantF a q ∧ secantF a q<a ∧ a/secantF a q<secantRho a q ∧
      secantRho a q<lowerEnvelope a (secantF a q) := by
  obtain ⟨hf,hfa,hr⟩ := secant_lower_bounds ha hq
  have hf0 : 0<secantF a q := by linarith
  refine ⟨hf,hfa,?_,rho_lt_lowerEnvelope ha hau hf hfa (lowerSecantH_pos ha hau hq)⟩
  exact (div_lt_iff₀ hf0).mpr (by nlinarith [secant_product_gt ha hq])

end LeanVerification.PositiveDCompletion
