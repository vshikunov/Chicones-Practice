import LeanVerification.PositiveDCompletion.SignedNormalization
import LeanVerification.PositiveDCompletion.SecantGeometry
import LeanVerification.ReflectedWedgeCompletion.PhysicalTransport

noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 20000

def saddleRoot (D F h : ℝ) : ℝ :=
  wedgeGeometricMean D F h^(1+lowerPhysicalA F)*Real.sinh (wedgeLogSecant D F h)/
    Real.sinh (lowerPhysicalA F*wedgeLogSecant D F h)
def saddleBeta (D F : ℝ) : ℝ :=
  lowerPhysicalA F*(1-lowerPhysicalD D)/(1-lowerPhysicalA F)
def saddleOmega (D F h : ℝ) : ℝ :=
  lowerPhysicalA F*lowerPhysicalD D*saddleRoot D F h^2-1

theorem saddleRoot_pos {D F h : ℝ} (ha : 0<lowerPhysicalA F)
    (hF : 0<F) (hh : AdmissibleEnergy D F h) : 0<saddleRoot D F h := by
  unfold saddleRoot
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (wedgeGeometricMean_pos hh) _)
    (Real.sinh_pos_iff.mpr (wedgeLogSecant_pos hF hh)))
      (Real.sinh_pos_iff.mpr (mul_pos ha (wedgeLogSecant_pos hF hh)))

theorem saddleOmega_lt_neg_one {D F h : ℝ} (hD : 0<D)
    (hF0 : 1/4<F) (hF1 : F<1) (hh : AdmissibleEnergy D F h) : saddleOmega D F h< -1 := by
  obtain ⟨ha,hau,hd,he⟩ := positiveD_parameter_bounds hD hF0 hF1
  have hr := saddleRoot_pos ha (by linarith : 0<F) hh
  unfold saddleOmega
  have hm : lowerPhysicalA F*lowerPhysicalD D*saddleRoot D F h^2<0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ha (by linarith)) (sq_pos_of_pos hr)
  linarith

theorem signed_equal_potential_secant_equation
    {a d nu q : ℝ} (ha : 0<a) (ha1 : a≠1) (hnu : 0<nu)
    (hpot : wedgePotential a d (nu*Real.exp q)=wedgePotential a d (nu*Real.exp (-q))) :
    a*d*(nu^(1+a))^2*Real.sinh (2*q)+
      2*a*(1-d)/(1-a)*nu^(1+a)*Real.sinh ((1-a)*q)-Real.sinh (2*a*q)=0 := by
  have hpow := secant_power_relations hnu a
  have hdiff : wedgePotential a d (nu*Real.exp q)-wedgePotential a d (nu*Real.exp (-q))=
      d*nu^2*Real.sinh (2*q)+2*(1-d)/(1-a)*nu^(1-a)*Real.sinh ((1-a)*q)-
        1/a*nu^(-2*a)*Real.sinh (2*a*q) := by
    unfold wedgePotential
    calc
      _ = d/2*((nu*Real.exp q)^2-(nu*Real.exp (-q))^2)+
          (1-d)/(1-a)*((nu*Real.exp q)^(1-a)-(nu*Real.exp (-q))^(1-a))+
          1/(2*a)*((nu*Real.exp q)^(-2*a)-(nu*Real.exp (-q))^(-2*a)) := by ring
      _ = _ := by
        rw [←Real.rpow_two (nu*Real.exp q),←Real.rpow_two (nu*Real.exp (-q)),
          secant_power_difference hnu,secant_power_difference hnu,secant_power_difference hnu]
        have he : -2*a*q= -(2*a*q) := by ring
        rw [he,Real.sinh_neg,Real.rpow_two]
        ring
  have hzero : d*nu^2*Real.sinh (2*q)+2*(1-d)/(1-a)*nu^(1-a)*Real.sinh ((1-a)*q)-
      1/a*nu^(-2*a)*Real.sinh (2*a*q)=0 := by rw [hpot,sub_self] at hdiff;exact hdiff.symm
  calc
    _ = a*nu^(2*a)*(d*nu^2*Real.sinh (2*q)+2*(1-d)/(1-a)*nu^(1-a)*Real.sinh ((1-a)*q)-
      1/a*nu^(-2*a)*Real.sinh (2*a*q)) := by
        calc
          _ = a*d*(nu^(2*a)*nu^2)*Real.sinh (2*q)+
            2*a*(1-d)/(1-a)*(nu^(2*a)*nu^(1-a))*Real.sinh ((1-a)*q)-
              (nu^(2*a)*nu^(-2*a))*Real.sinh (2*a*q) := by rw [hpow.1,hpow.2.1,hpow.2.2];ring
          _ = _ := by
            field_simp [ha.ne',show 1-a≠0 by intro he;apply ha1;linarith]
            <;> ring
    _ = 0 := by rw [hzero,mul_zero]

theorem signed_quadratic_of_secant_equation
    {a d nu q : ℝ} (ha : 0<a) (ha1 : a≠1) (hq : 0<q)
    (heq : a*d*(nu^(1+a))^2*Real.sinh (2*q)+
      2*a*(1-d)/(1-a)*nu^(1+a)*Real.sinh ((1-a)*q)-Real.sinh (2*a*q)=0) :
    secantF a q*(a*d*(nu^(1+a)*Real.sinh q/Real.sinh (a*q))^2)+
      (a*(1-d)/(1-a))*(1-secantF a q)*(nu^(1+a)*Real.sinh q/Real.sinh (a*q))-1=0 := by
  have hs := Real.sinh_pos_iff.mpr hq
  have hsa := Real.sinh_pos_iff.mpr (mul_pos ha hq)
  have hc := Real.cosh_pos (a*q)
  have h1a : 1-a≠0 := by intro he;apply ha1;linarith
  have he : (1-a)*q=q-a*q := by ring
  rw [he,Real.sinh_sub,Real.sinh_two_mul,
    show 2*a*q=2*(a*q) by ring,Real.sinh_two_mul] at heq
  have heval :
      secantF a q*(a*d*(nu^(1+a)*Real.sinh q/Real.sinh (a*q))^2)+
        (a*(1-d)/(1-a))*(1-secantF a q)*(nu^(1+a)*Real.sinh q/Real.sinh (a*q))-1=
      (a*d*(nu^(1+a))^2*Real.sinh q*Real.cosh q+
        a*(1-d)/(1-a)*nu^(1+a)*(Real.sinh q*Real.cosh (a*q)-Real.cosh q*Real.sinh (a*q))-
          Real.sinh (a*q)*Real.cosh (a*q))/(Real.sinh (a*q)*Real.cosh (a*q)) := by
    unfold secantF secantR
    field_simp [ha.ne',hs.ne',hsa.ne',hc.ne',h1a]
    <;> ring
  rw [heval]
  apply div_eq_zero_iff.mpr
  left
  linear_combination (1 / 2 : ℝ) * heq

theorem lowerPhysicalA_ne_one {F : ℝ} (hF : 0<F) (hhalf : F≠1/2) :
    lowerPhysicalA F≠1 := by
  intro he
  unfold lowerPhysicalA at he
  have hi : 1/F=2 := by linarith
  have hx := (div_eq_iff hF.ne').mp hi
  apply hhalf
  linarith

theorem saddleRoot_quadratic {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    wedgeF D F h*(1+saddleOmega D F h)+
      saddleBeta D F*(1-wedgeF D F h)*saddleRoot D F h-1=0 := by
  obtain ⟨ha,hau,hd,he⟩ := positiveD_parameter_bounds hD hF0 hF1
  have hF : 0<F := by linarith
  have ha1 := lowerPhysicalA_ne_one hF hhalf
  have ht := wedge_turn_decomposition hh
  have hp := (signed_turns_same_potential hD hF hF1 hhalf hh).symm
  rw [ht.1,ht.2] at hp
  have hquad := signed_quadratic_of_secant_equation ha ha1 (wedgeLogSecant_pos hF hh)
    (signed_equal_potential_secant_equation ha ha1 (wedgeGeometricMean_pos hh) hp)
  convert hquad using 1
  unfold wedgeF saddleOmega saddleBeta saddleRoot
  ring

end LeanVerification.PositiveDCompletion
