import LeanVerification.PositiveDCompletion.PhysicalTurnJets

/-! The signed mixture lies on the actual physical branch. Its strict sign
comes from the two physical force signs, not from a continuation convention. -/
noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

theorem saddleForce_weighted {a d u : ℝ} (hu : 0<u) :
    u*saddleForce a d u=d*u^2+(1-d)*u^(1-a)-u^(-2*a) := by
  have h1 : u*u^(-a)=u^(1-a) := by
    calc
      _ = u^(1:ℝ)*u^(-a) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hu];congr 1 <;> ring
  have h2 : u*u^(-2*a-1)=u^(-2*a) := by
    calc
      _ = u^(1:ℝ)*u^(-2*a-1) := by rw [Real.rpow_one]
      _ = _ := by rw [←Real.rpow_add hu];congr 1 <;> ring
  unfold saddleForce
  calc
    _ = d*u^2+(1-d)*(u*u^(-a))-u*u^(-2*a-1) := by ring
    _ = _ := by rw [h1,h2]

theorem signed_force_secant_identity {a d nu q : ℝ}
    (ha : 0<a) (ha1 : a≠1) (hnu : 0<nu)
    (heq : wedgePotential a d (nu*Real.exp q)=wedgePotential a d (nu*Real.exp (-q))) :
    a*nu^(2*a)*((nu*Real.exp q)*saddleForce a d (nu*Real.exp q)-
      (nu*Real.exp (-q))*saddleForce a d (nu*Real.exp (-q)))=
        (1+a)*(a*d*(nu^(1+a))^2*Real.sinh (2*q)+Real.sinh (2*a*q)) := by
  have hp := secant_power_relations hnu a
  have hquad := signed_equal_potential_secant_equation ha ha1 hnu heq
  have h1a : 1-a≠0 := by intro he;apply ha1;linarith
  have he : (1-a)*(a*d*(nu^(1+a))^2*Real.sinh (2*q)-Real.sinh (2*a*q))+
      2*a*(1-d)*nu^(1+a)*Real.sinh ((1-a)*q)=0 := by
    field_simp [h1a] at hquad
    linear_combination hquad
  have hd : (nu*Real.exp q)*saddleForce a d (nu*Real.exp q)-
      (nu*Real.exp (-q))*saddleForce a d (nu*Real.exp (-q))=
      2*d*nu^2*Real.sinh (2*q)+2*(1-d)*nu^(1-a)*Real.sinh ((1-a)*q)+
        2*nu^(-2*a)*Real.sinh (2*a*q) := by
    rw [saddleForce_weighted (mul_pos hnu (Real.exp_pos q)),
      saddleForce_weighted (mul_pos hnu (Real.exp_pos (-q)))]
    calc
      _ = d*((nu*Real.exp q)^2-(nu*Real.exp (-q))^2)+
          (1-d)*((nu*Real.exp q)^(1-a)-(nu*Real.exp (-q))^(1-a))-
          ((nu*Real.exp q)^(-2*a)-(nu*Real.exp (-q))^(-2*a)) := by ring
      _ = _ := by
        rw [←Real.rpow_two (nu*Real.exp q),←Real.rpow_two (nu*Real.exp (-q)),
          secant_power_difference hnu,secant_power_difference hnu,secant_power_difference hnu,
          Real.rpow_two,show -2*a*q= -(2*a*q) by ring,Real.sinh_neg]
        ring
  rw [hd]
  calc
    _ = 2*a*d*(nu^(2*a)*nu^2)*Real.sinh (2*q)+
        2*a*(1-d)*(nu^(2*a)*nu^(1-a))*Real.sinh ((1-a)*q)+
        2*a*(nu^(2*a)*nu^(-2*a))*Real.sinh (2*a*q) := by ring
    _ = _ := by
      rw [hp.1,hp.2.1,hp.2.2]
      linear_combination he

theorem signed_branch_algebra {a d nu q : ℝ} (ha : 0<a) (hq : 0<q) :
    a*d*(nu^(1+a))^2*Real.sinh (2*q)+Real.sinh (2*a*q)=
      (2*Real.sinh (a*q)*Real.cosh (a*q))*
        (1+secantF a q*(a*d*(nu^(1+a)*Real.sinh q/Real.sinh (a*q))^2)) := by
  have hs := (Real.sinh_pos_iff.mpr hq).ne'
  have hsa := (Real.sinh_pos_iff.mpr (mul_pos ha hq)).ne'
  have hc := (Real.cosh_pos (a*q)).ne'
  rw [Real.sinh_two_mul,show 2*a*q=2*(a*q) by ring,Real.sinh_two_mul]
  unfold secantF secantR
  field_simp [ha.ne',hs,hsa,hc]
  <;> ring

theorem physical_signed_branch_negative {D F h : ℝ} (hD : 0<D)
    (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2) (hh : AdmissibleEnergy D F h) :
    1+wedgeF D F h*(1+saddleOmega D F h)<0 := by
  obtain ⟨ha,hau,hd,hes⟩ := positiveD_parameter_bounds hD hF0 hF1
  have hF : 0<F := by linarith
  have ha1 := lowerPhysicalA_ne_one hF hhalf
  have hp := wedge_turns_pos D F h hh
  have hf := saddle_turn_force_signs hD hF0 hF1 hhalf hh
  have ht := wedge_turn_decomposition hh
  have heq := (signed_turns_same_potential hD hF hF1 hhalf hh).symm
  have hweighted : wedgeRight D F h*saddleForce (lowerPhysicalA F) (lowerPhysicalD D) (wedgeRight D F h)-
      wedgeLeft D F h*saddleForce (lowerPhysicalA F) (lowerPhysicalD D) (wedgeLeft D F h)<0 := by
    have hn := mul_neg_of_pos_of_neg hp.2 hf.2
    have hg := mul_pos hp.1 hf.1
    linarith
  have hneg := mul_neg_of_pos_of_neg
    (mul_pos ha (Real.rpow_pos_of_pos (wedgeGeometricMean_pos hh) (2*lowerPhysicalA F))) hweighted
  rw [ht.1,ht.2] at heq hneg
  rw [signed_force_secant_identity ha ha1 (wedgeGeometricMean_pos hh) heq] at hneg
  have hi : lowerPhysicalA F*lowerPhysicalD D*(wedgeGeometricMean D F h^(1+lowerPhysicalA F))^2*
      Real.sinh (2*wedgeLogSecant D F h)+Real.sinh (2*lowerPhysicalA F*wedgeLogSecant D F h)<0 := by
    by_contra hn
    have hpos := mul_nonneg (show 0≤1+lowerPhysicalA F by linarith) (le_of_not_gt hn)
    linarith
  rw [signed_branch_algebra ha (wedgeLogSecant_pos hF hh)] at hi
  have hb : 1+secantF (lowerPhysicalA F) (wedgeLogSecant D F h)*
      (lowerPhysicalA F*lowerPhysicalD D*(wedgeGeometricMean D F h^(1+lowerPhysicalA F)*
        Real.sinh (wedgeLogSecant D F h)/Real.sinh (lowerPhysicalA F*wedgeLogSecant D F h))^2)<0 := by
    by_contra hn
    have hpos := mul_nonneg (show 0≤2*Real.sinh (lowerPhysicalA F*wedgeLogSecant D F h)*
      Real.cosh (lowerPhysicalA F*wedgeLogSecant D F h) from
        (mul_pos (mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (mul_pos ha (wedgeLogSecant_pos hF hh))))
          (Real.cosh_pos _)).le) (le_of_not_gt hn)
    linarith
  convert hb using 1
  unfold wedgeF saddleOmega saddleRoot
  ring

end LeanVerification.PositiveDCompletion
