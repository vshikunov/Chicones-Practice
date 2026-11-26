import LeanVerification.PositiveDCompletion.LowerPolynomial08
import LeanVerification.PositiveDCompletion.LowerHomogeneous

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 16000000
set_option maxRecDepth 40000

theorem lower_factor_08 (a x t b g u c0 c1 c2 c3 c4 c5 c6 : ℝ) :
    (((a^(2 : ℕ)*t^(2 : ℕ)*b)^(6 : ℕ)*((1-t)^(2 : ℕ)*g)^(0 : ℕ)*(x^(10 : ℕ)*t^(0 : ℕ)*(1-t)^(5 : ℕ)*c0)*u^(0 : ℕ)+((a^(2 : ℕ)*t^(2 : ℕ)*b)^(5 : ℕ)*((1-t)^(2 : ℕ)*g)^(1 : ℕ)*(x^(9 : ℕ)*t^(0 : ℕ)*(1-t)^(3 : ℕ)*c1)*u^(1 : ℕ)+(a^(2 : ℕ)*t^(2 : ℕ)*b)^(4 : ℕ)*((1-t)^(2 : ℕ)*g)^(2 : ℕ)*(x^(8 : ℕ)*t^(0 : ℕ)*(1-t)^(2 : ℕ)*c2)*u^(2 : ℕ)))+(((a^(2 : ℕ)*t^(2 : ℕ)*b)^(3 : ℕ)*((1-t)^(2 : ℕ)*g)^(3 : ℕ)*(x^(7 : ℕ)*t^(0 : ℕ)*(1-t)^(1 : ℕ)*c3)*u^(3 : ℕ)+(a^(2 : ℕ)*t^(2 : ℕ)*b)^(2 : ℕ)*((1-t)^(2 : ℕ)*g)^(4 : ℕ)*(x^(6 : ℕ)*t^(0 : ℕ)*(1-t)^(0 : ℕ)*c4)*u^(4 : ℕ))+((a^(2 : ℕ)*t^(2 : ℕ)*b)^(1 : ℕ)*((1-t)^(2 : ℕ)*g)^(5 : ℕ)*(x^(5 : ℕ)*t^(0 : ℕ)*(1-t)^(0 : ℕ)*c5)*u^(5 : ℕ)+(a^(2 : ℕ)*t^(2 : ℕ)*b)^(0 : ℕ)*((1-t)^(2 : ℕ)*g)^(6 : ℕ)*(x^(4 : ℕ)*t^(1 : ℕ)*(1-t)^(0 : ℕ)*c6)*u^(6 : ℕ))))=x^(4 : ℕ)*t^(1 : ℕ)*(1-t)^(5 : ℕ)*((((x^(6 : ℕ)*a^(12 : ℕ)*t^(11 : ℕ)*(1-t)^(0 : ℕ)*b^(6 : ℕ)*g^(0 : ℕ)*c0)*u^(0 : ℕ)+((x^(5 : ℕ)*a^(10 : ℕ)*t^(9 : ℕ)*(1-t)^(0 : ℕ)*b^(5 : ℕ)*g^(1 : ℕ)*c1)*u^(1 : ℕ)+(x^(4 : ℕ)*a^(8 : ℕ)*t^(7 : ℕ)*(1-t)^(1 : ℕ)*b^(4 : ℕ)*g^(2 : ℕ)*c2)*u^(2 : ℕ)))+(((x^(3 : ℕ)*a^(6 : ℕ)*t^(5 : ℕ)*(1-t)^(2 : ℕ)*b^(3 : ℕ)*g^(3 : ℕ)*c3)*u^(3 : ℕ)+(x^(2 : ℕ)*a^(4 : ℕ)*t^(3 : ℕ)*(1-t)^(3 : ℕ)*b^(2 : ℕ)*g^(4 : ℕ)*c4)*u^(4 : ℕ))+((x^(1 : ℕ)*a^(2 : ℕ)*t^(1 : ℕ)*(1-t)^(5 : ℕ)*b^(1 : ℕ)*g^(5 : ℕ)*c5)*u^(5 : ℕ)+(x^(0 : ℕ)*a^(0 : ℕ)*t^(0 : ℕ)*(1-t)^(7 : ℕ)*b^(0 : ℕ)*g^(6 : ℕ)*c6)*u^(6 : ℕ))))) := by ring

theorem lowerNum08_map {x t u : ℝ} (hx : 0<x) (hxu : x<1) (ht : 0<t) (htu : t<1) :
    (lowerRhoDen (1+2*x) t)^(6 : ℕ)*lowerNum08 (1+2*x) (lowerCubeF (1+2*x) t)
      (lowerRhoNum (1+2*x) t u/lowerRhoDen (1+2*x) t)=
    (2*x)^(4 : ℕ)*t^(1 : ℕ)*(1-t)^(5 : ℕ)*lowerAtom08 x t u := by
  have ha : 1<1+2*x := by linarith
  have hau : 1+2*x<3 := by linarith
  have hB := lowerCubeB_pos ha hau ht htu
  have ha0 : 0<1+2*x := by linarith
  have hF : 0<lowerCubeF (1+2*x) t := by
    unfold lowerCubeF
    have hx0 : 0<(1+2*x)-1 := by linarith
    positivity
  have hD : 0<lowerCubeD (1+2*x) t := by
    unfold lowerCubeD
    positivity
  have he := lower_homogeneous_6 (1+2*x) (lowerCubeF (1+2*x) t)
    (lowerCubeD (1+2*x) t) ((1-t)^(2 : ℕ)*lowerCubeG (1+2*x) t) u
    (lowerNum08Coeff0 (1+2*x) (lowerCubeF (1+2*x) t)) (lowerNum08Coeff1 (1+2*x) (lowerCubeF (1+2*x) t)) (lowerNum08Coeff2 (1+2*x) (lowerCubeF (1+2*x) t)) (lowerNum08Coeff3 (1+2*x) (lowerCubeF (1+2*x) t)) (lowerNum08Coeff4 (1+2*x) (lowerCubeF (1+2*x) t)) (lowerNum08Coeff5 (1+2*x) (lowerCubeF (1+2*x) t)) (lowerNum08Coeff6 (1+2*x) (lowerCubeF (1+2*x) t)) hF.ne' hD.ne'
  rw [lowerCore08Coeff0_map,lowerCore08Coeff1_map,lowerCore08Coeff2_map,lowerCore08Coeff3_map,lowerCore08Coeff4_map,lowerCore08Coeff5_map,lowerCore08Coeff6_map] at he
  rw [show (1+2*x)-1=2*x by ring] at he
  have hf := lower_factor_08 (1+2*x) (2*x) t (lowerCubeB (1+2*x) t) (lowerCubeG (1+2*x) t) u
    (lowerCore08Coeff0 (1+2*x) t) (lowerCore08Coeff1 (1+2*x) t) (lowerCore08Coeff2 (1+2*x) t) (lowerCore08Coeff3 (1+2*x) t) (lowerCore08Coeff4 (1+2*x) t) (lowerCore08Coeff5 (1+2*x) t) (lowerCore08Coeff6 (1+2*x) t)
  change _=(2*x)^(4 : ℕ)*t^(1 : ℕ)*(1-t)^(5 : ℕ)*lowerAtom08 x t u at hf
  rw [←hf]
  simpa only [lowerRhoDen,lowerRhoNum,lowerCubeD,lowerNum08] using he

end LeanVerification.PositiveDCompletion
