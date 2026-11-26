import LeanVerification.PositiveDCompletion.SignedRegular
import LeanVerification.PositiveDCompletion.SourceNormalization

noncomputable section
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion

theorem secant_C_g_pos {a q : ℝ} (ha : 0<a) (ha1 : a≠1) (hq : 0<q) :
    0<sourceC a (secantF a q) (secantRho a q)*modelG a (secantRho a q) := by
  have hf0 := secantF_pos ha hq
  have hr0 := secantRho_pos ha hq
  rcases lt_or_gt_of_ne ha1 with hau|hal
  · have hf := (secantF_bounds ha hau hq).2
    have haf : a*secantF a q<1 := by
      nlinarith [mul_lt_mul_of_pos_left hf ha]
    have hc : 0<sourceC a (secantF a q) (secantRho a q) := by
      unfold sourceC
      exact mul_pos (mul_pos ha hr0) (by linarith)
    exact mul_pos hc (secant_g_pos ha hau hq)
  · obtain ⟨hf,hfa,hr⟩ := secant_lower_bounds hal hq
    have haf : 1<a*secantF a q := by
      nlinarith [mul_lt_mul_of_pos_left hf ha]
    have hc : sourceC a (secantF a q) (secantRho a q)<0 := by
      unfold sourceC
      exact mul_neg_of_pos_of_neg (mul_pos ha hr0) (by linarith)
    have hg : modelG a (secantRho a q)<0 := by
      unfold modelG
      nlinarith [mul_lt_mul_of_pos_left hr (sq_pos_of_pos ha)]
    exact mul_pos_of_neg_of_neg hc hg

theorem sign_product_cross {A N g : ℝ} (ha : 0<A*g) (hn : N*g<0) : A*N<0 := by
  have hg : g≠0 := by intro he;rw [he,mul_zero] at ha;linarith
  have he : (A*N)*g^2<0 := by
    convert mul_neg_of_pos_of_neg ha hn using 1 <;> ring
  exact neg_of_mul_neg_left he (sq_nonneg g)

theorem signed_numerator_domain {a f rho w : ℝ}
    (ha : 0<a) (hf : 0<f) (hz : 1+w<0)
    (hA : 0<modelA a f rho*modelG a rho)
    (hN : transportN a f rho w*modelG a rho<0)
    (hC : 0<sourceC a f rho*modelG a rho) :
    sourceC a f rho≠0 ∧ 0< -transportN a f rho w/sourceC a f rho ∧
      0<4*(1+w)*modelA a f rho*(transportN a f rho w)^3 ∧
      0<4*a*(1+f)*(1+w)*modelA a f rho*(transportN a f rho w)^5 := by
  have hc : sourceC a f rho≠0 := by intro he;rw [he,zero_mul] at hC;linarith
  have hn : transportN a f rho w≠0 := by intro he;rw [he,zero_mul] at hN;linarith
  have hAN := sign_product_cross hA hN
  have hCN := sign_product_cross hC hN
  have hncoord : 0< -transportN a f rho w/sourceC a f rho := by
    rcases mul_neg_iff.mp hCN with ⟨hcp,hnn⟩|⟨hcn,hnp⟩
    · exact div_pos (neg_pos.mpr hnn) hcp
    · exact div_pos_of_neg_of_neg (neg_neg_of_pos hnp) hcn
  have hprod : 0<(1+w)*(modelA a f rho*transportN a f rho w) :=
    mul_pos_of_neg_of_neg hz hAN
  have hN2 : 0<(transportN a f rho w)^2 := sq_pos_of_ne_zero hn
  have hN4 : 0<(transportN a f rho w)^4 := by positivity
  have hj : 0<1+f := by linarith
  refine ⟨hc,hncoord,?_,?_⟩
  · convert mul_pos (mul_pos (by norm_num : (0:ℝ)<4) hprod) hN2 using 1 <;> ring
  · convert mul_pos (mul_pos (mul_pos (mul_pos (by norm_num : (0:ℝ)<4) ha) hj) hprod) hN4 using 1 <;> ring

theorem actual_signed_numerator_domain {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    sourceC (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h)≠0 ∧
      0< -transportN (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)/
        sourceC (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) ∧
      0<4*(1+saddleOmega D F h)*modelA (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h)*
        (transportN (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h))^3 ∧
      0<4*lowerPhysicalA F*(1+wedgeF D F h)*(1+saddleOmega D F h)*
        modelA (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h)*
        (transportN (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h))^5 := by
  have ha := (positiveD_parameter_bounds hD hF0 hF1).1
  have hF : 0<F := by linarith
  have hq := wedgeLogSecant_pos hF hh
  have ha1 := lowerPhysicalA_ne_one hF hhalf
  exact signed_numerator_domain ha (secantF_pos ha hq)
    (by linarith [saddleOmega_lt_neg_one hD hF0 hF1 hh])
    (secant_A_sign ha ha1 hq) (physical_transportN_sign hD hF0 hF1 hhalf hh)
    (secant_C_g_pos ha ha1 hq)

end LeanVerification.PositiveDCompletion
