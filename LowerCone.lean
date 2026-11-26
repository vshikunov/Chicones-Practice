import LeanVerification.PositiveDCompletion.HyperbolicBounds
import Mathlib.Tactic.Positivity

/-! A strict, correlated cone for the actual secants with 1 < a < 3.
It follows from the same hyperbolic cube monotonicity used above the seam. -/
noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open ReflectedWedgeCompletion
set_option maxHeartbeats 8000000
set_option maxRecDepth 16000

def lowerSecantH (a f rho : ℝ) : ℝ :=
  (a-1)^3*f^3*(f+a^2*rho)-a^2*rho*(f-1)^2*(a^2*rho*(f^2+1)-2*f^2)

def lowerEnvelopeB (a f : ℝ) : ℝ :=
  -a^3*f+2*a^2*f^2+3*a^2*f+2*a^2-4*a*f^2-3*a*f-4*a+5*f

def lowerEnvelope (a f : ℝ) : ℝ :=
  f^2*(a-1)^3*(a*f^2+a-2*f)/(a^2*(f-1)^2*lowerEnvelopeB a f)

theorem lowerH_fraction (a A B s c : ℝ) (ha : a≠0) (hs : s≠0) (hB : B≠0) :
    lowerSecantH a (A*c/(s*B)) (A^2/(a^2*s^2))*(s^8*B^4)=
      A^4*((a-1)^3*s^3*c^3*(s*c+A*B)-
        (A*c-B*s)^2*(A^2*c^2+s^2*B^2-2*s^2*c^2)) := by
  unfold lowerSecantH
  field_simp [ha,hs,hB]
  <;> ring

theorem lowerH_hyperbolic_algebra (a A B s c : ℝ)
    (hB : B^2-A^2=1) (hc : c^2-s^2=1) :
    A^4*((a-1)^3*s^3*c^3*(s*c+A*B)-
        (A*c-B*s)^2*(A^2*c^2+s^2*B^2-2*s^2*c^2))=
      A^4*(A*c+B*s)*((a-1)^3*s^3*c^3*(B*c-A*s)-
        (A*c-B*s)^3*(c^2+s^2)) := by
  have hm : (A*c-B*s)*(A*c+B*s)=A^2-s^2 := by
    linear_combination A^2*hc-s^2*hB
  have hM : (B*c-A*s)*(A*c+B*s)=s*c+A*B := by
    linear_combination A*B*hc+s*c*hB
  have he : A^2*c^2+s^2*B^2-2*s^2*c^2=(A^2-s^2)*(c^2+s^2) := by
    linear_combination s^2*hB-s^2*hc
  rw [←hM,he,←hm]
  ring

theorem lowerSecantH_pos {a q : ℝ} (ha : 1<a) (hau : a<3) (hq : 0<q) :
    0<lowerSecantH a (secantF a q) (secantRho a q) := by
  have ha0 : 0<a := by linarith
  have ham : 0<a-1 := by linarith
  have hm : 0<(a-1)*q := mul_pos ham hq
  have h2q : 0<2*q := by positivity
  have hcmp := hyperbolicCube_strictMono hm h2q (by nlinarith : (a-1)*q<2*q)
  unfold hyperbolicCube at hcmp
  have hcross := (div_lt_div_iff₀
    (mul_pos (pow_pos hm 3) (Real.cosh_pos _))
    (mul_pos (pow_pos h2q 3) (Real.cosh_pos _))).mp hcmp
  rw [Real.sinh_two_mul,Real.cosh_two_mul] at hcross
  have hgap : 0<(a-1)^3*Real.sinh q^3*Real.cosh q^3*Real.cosh ((a-1)*q)-
      Real.sinh ((a-1)*q)^3*(Real.cosh q^2+Real.sinh q^2) := by
    have he : 0<8*q^3*((a-1)^3*Real.sinh q^3*Real.cosh q^3*Real.cosh ((a-1)*q)-
        Real.sinh ((a-1)*q)^3*(Real.cosh q^2+Real.sinh q^2)) := by
      nlinarith only [hcross]
    exact pos_of_mul_pos_right he (by positivity)
  have heq : (a-1)*q=a*q-q := by ring
  rw [heq,Real.sinh_sub,Real.cosh_sub] at hgap
  have hs : 0<Real.sinh q := Real.sinh_pos_iff.mpr hq
  have hA : 0<Real.sinh (a*q) := Real.sinh_pos_iff.mpr (mul_pos ha0 hq)
  have hc := Real.cosh_pos q
  have hB := Real.cosh_pos (a*q)
  have hidentity := lowerH_fraction a (Real.sinh (a*q)) (Real.cosh (a*q))
    (Real.sinh q) (Real.cosh q) ha0.ne' hs.ne' hB.ne'
  rw [lowerH_hyperbolic_algebra _ _ _ _ _
    (Real.cosh_sq_sub_sinh_sq (a*q)) (Real.cosh_sq_sub_sinh_sq q)] at hidentity
  have hr : secantRho a q=Real.sinh (a*q)^2/(a^2*Real.sinh q^2) := by
    unfold secantRho
    rw [div_pow,mul_pow]
  have hf : secantF a q=Real.sinh (a*q)*Real.cosh q/(Real.sinh q*Real.cosh (a*q)) := by
    unfold secantF secantR
    field_simp [ha0.ne',hs.ne',hB.ne']
    <;> ring
  rw [←hr,←hf] at hidentity
  have hp : 0<lowerSecantH a (secantF a q) (secantRho a q)*
      (Real.sinh q^8*Real.cosh (a*q)^4) := by
    rw [hidentity]
    exact mul_pos (mul_pos (pow_pos hA 4) (add_pos (mul_pos hA hc) (mul_pos hB hs))) hgap
  exact pos_of_mul_pos_left hp (by positivity)

theorem lowerEnvelopeB_cube_identity (x t : ℝ) :
    lowerEnvelopeB (1+2*x) (1+2*x*t)=4*x^2*
      (4*(1-x)^2*(1-t)^2+8*(1-x)^2*t*(1-t)+2*(1-x)^2*t^2+
       6*x*(1-x)*(1-t)^2+20*x*(1-x)*t*(1-t)+10*x*(1-x)*t^2+
       2*x^2*(1-t)^2+8*x^2*t*(1-t)+12*x^2*t^2) := by
  unfold lowerEnvelopeB
  ring

theorem lower_cube_coordinates {a f : ℝ} (ha : 1<a) (hau : a<3)
    (hf : 1<f) (hfa : f<a) :
    0<(a-1)/2 ∧ (a-1)/2<1 ∧ 0<(f-1)/(a-1) ∧ (f-1)/(a-1)<1 ∧
      1+2*((a-1)/2)=a ∧ 1+2*((a-1)/2)*((f-1)/(a-1))=f := by
  have ham : 0<a-1 := by linarith
  refine ⟨by positivity,by linarith,div_pos (by linarith) ham,
    (div_lt_one ham).mpr (by linarith),by ring,?_⟩
  field_simp [ham.ne']
  <;> ring

theorem lowerEnvelopeB_pos {a f : ℝ} (ha : 1<a) (hau : a<3)
    (hf : 1<f) (hfa : f<a) : 0<lowerEnvelopeB a f := by
  obtain ⟨hx,hxu,ht,htu,haeq,hfeq⟩ := lower_cube_coordinates ha hau hf hfa
  have hxc : 0<1-(a-1)/2 := by linarith
  have htc : 0<1-(f-1)/(a-1) := by linarith
  have he := lowerEnvelopeB_cube_identity ((a-1)/2) ((f-1)/(a-1))
  rw [haeq,hfeq] at he
  rw [he]
  positivity

theorem lowerEnvelope_tangent_identity (a f rho : ℝ) :
    f^2*(f^2*(a-1)^3*(a*f^2+a-2*f)-a^2*(f-1)^2*lowerEnvelopeB a f*rho)=
      (f-1)^2*lowerSecantH a f rho+
        (f^2+1)*(a^2*(f-1)^2*rho-(a-1)^2*f^2)^2 := by
  unfold lowerEnvelopeB lowerSecantH
  ring

theorem rho_lt_lowerEnvelope {a f rho : ℝ} (ha : 1<a) (hau : a<3)
    (hf : 1<f) (hfa : f<a) (hH : 0<lowerSecantH a f rho) :
    rho<lowerEnvelope a f := by
  have ha0 : 0<a := by linarith
  have hf0 : 0<f := by linarith
  have hfm : 0<f-1 := by linarith
  have hB := lowerEnvelopeB_pos ha hau hf hfa
  have hid := lowerEnvelope_tangent_identity a f rho
  have hp : 0<f^2*(f^2*(a-1)^3*(a*f^2+a-2*f)-a^2*(f-1)^2*lowerEnvelopeB a f*rho) := by
    rw [hid]
    exact add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos hfm) hH) (by positivity)
  have hd : 0<a^2*(f-1)^2*lowerEnvelopeB a f := by positivity
  apply (lt_div_iff₀ hd).mpr
  have hx := pos_of_mul_pos_right hp (sq_pos_of_pos hf0).le
  nlinarith only [hx]

end LeanVerification.PositiveDCompletion
