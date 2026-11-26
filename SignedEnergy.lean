import LeanVerification.PositiveDCompletion.SignedTransport
import LeanVerification.ReflectedWedgeCompletion.PhysicalEnergyRatio

/-! Exact energy/width normalization for the signed positive-D branch. -/
noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion
set_option maxHeartbeats 16000000
set_option maxRecDepth 24000

theorem signed_energy_ratio_eliminate {f r z B K : ℝ}
    (hz : z≠0) (hf : 1-f≠0) (hA : f^2-r≠0)
    (hquad : f*z+B*(1-f)-1=0) (hK : (f^2-r)*K=1-r) :
    (f^2*K+1)/8+B*(f*K-1)/(4*z)+(K+1)/(8*z)=
      (1+f)^2*(1/z-r)/(8*(f^2-r)) := by
  let P := (f^2-r)*z*(f^2*K+1)+2*B*(f^2-r)*(f*K-1)+
    (f^2-r)*(K+1)-(1+f)^2*(1-r*z)
  have hP : (1-f)*P=0 := by
    dsimp only [P]
    linear_combination 2*(f^2-r)*(f*K-1)*hquad-(1+f)*(z*f^2-1)*hK
  have hP0 : P=0 := (mul_eq_zero.mp hP).resolve_left hf
  apply sub_eq_zero.mp
  calc
    _ = P/(8*z*(f^2-r)) := by
      dsimp only [P]
      field_simp [hz,hA]
      <;> ring
    _ = 0 := by rw [hP0,zero_div]

theorem signed_secant_energy_hyperbolic {a d nu q : ℝ}
    (ha : 0<a) (ha1 : a≠1) (hd : d≠0) (hnu : 0<nu) (hq : 0<q)
    (heq : wedgePotential a d (nu*Real.exp q)=wedgePotential a d (nu*Real.exp (-q))) :
    let R := nu^(1+a)*Real.sinh q/Real.sinh (a*q)
    let z := a*d*R^2
    let B := a*(1-d)/(1-a)*R
    wedgePotential a d (nu*Real.exp q)/(d*(2*nu*Real.sinh q)^2)=
      Real.cosh (2*q)/(8*Real.sinh q^2)+
        B*Real.cosh ((1-a)*q)/(4*z*Real.sinh q*Real.sinh (a*q))+
        Real.cosh (2*a*q)/(8*z*Real.sinh (a*q)^2) := by
  have hpow1 : nu^(1-a)=nu^2/nu^(1+a) := by
    rw [←Real.rpow_two,←Real.rpow_sub hnu]
    congr 1 <;> ring
  have hpow2 : nu^(-2*a)=nu^2/(nu^(1+a))^2 := by
    rw [←Real.rpow_two,←Real.rpow_two,←Real.rpow_mul hnu.le,←Real.rpow_sub hnu]
    congr 1 <;> ring
  have h1a : 1-a≠0 := by intro he;apply ha1;linarith
  have hs := (Real.sinh_pos_iff.mpr hq).ne'
  have hsa := (Real.sinh_pos_iff.mpr (mul_pos ha hq)).ne'
  have hn := (Real.rpow_pos_of_pos hnu (1+a)).ne'
  dsimp only
  rw [secant_potential_average hnu heq,hpow1,hpow2]
  field_simp [ha.ne',hd,h1a,hnu.ne',hs,hsa,hn]
  <;> ring

theorem signed_hyperbolic_energy_ratio {a q z B : ℝ}
    (ha : 0<a) (ha1 : a≠1) (hq : 0<q) (hz : z≠0)
    (hquad : secantF a q*z+B*(1-secantF a q)-1=0) :
    Real.cosh (2*q)/(8*Real.sinh q^2)+
      B*Real.cosh ((1-a)*q)/(4*z*Real.sinh q*Real.sinh (a*q))+
      Real.cosh (2*a*q)/(8*z*Real.sinh (a*q)^2)=
    (1+secantF a q)^2*(1/z-a^2*secantRho a q)/
      (8*((secantF a q)^2-a^2*secantRho a q)) := by
  have hs := Real.sinh_pos_iff.mpr hq
  have hsa := Real.sinh_pos_iff.mpr (mul_pos ha hq)
  have hc := Real.cosh_pos (a*q)
  have hfeq := secantF_fraction ha hq
  have hreq : a^2*secantRho a q=Real.sinh (a*q)^2/Real.sinh q^2 := by
    unfold secantRho
    field_simp [ha.ne',hs.ne']
    <;> ring
  let K := Real.cosh (a*q)^2/Real.sinh (a*q)^2
  have hK : ((secantF a q)^2-a^2*secantRho a q)*K=1-a^2*secantRho a q := by
    have hfirst : ((secantF a q)^2-a^2*secantRho a q)*K=
        (Real.cosh q^2-Real.cosh (a*q)^2)/Real.sinh q^2 := by
      rw [hfeq,hreq]
      dsimp only [K]
      field_simp [hs.ne',hsa.ne',hc.ne']
      <;> ring
    rw [hfirst,hreq]
    have hp : Real.cosh q^2-Real.cosh (a*q)^2=Real.sinh q^2-Real.sinh (a*q)^2 := by
      linarith [Real.cosh_sq_sub_sinh_sq q,Real.cosh_sq_sub_sinh_sq (a*q)]
    rw [hp]
    field_simp [hs.ne']
    <;> ring
  have hA : (secantF a q)^2-a^2*secantRho a q≠0 := by
    intro he
    have hg := secant_g_ne_zero ha ha1 hq
    rw [he,zero_mul] at hK
    exact hg hK.symm
  have hf : 1-secantF a q≠0 := by
    rcases lt_or_gt_of_ne ha1 with hl|hu
    · have h := (secantF_bounds ha hl hq).2
      linarith
    · have h := (secant_lower_bounds hu hq).1
      linarith
  have hterm1 : Real.cosh (2*q)/(8*Real.sinh q^2)=((secantF a q)^2*K+1)/8 := by
    rw [Real.cosh_two_mul,hfeq]
    dsimp only [K]
    field_simp [hs.ne',hsa.ne',hc.ne']
    <;> ring
  have hterm2 : B*Real.cosh ((1-a)*q)/(4*z*Real.sinh q*Real.sinh (a*q))=
      B*(secantF a q*K-1)/(4*z) := by
    rw [show (1-a)*q=q-a*q by ring,Real.cosh_sub,hfeq]
    dsimp only [K]
    field_simp [hs.ne',hsa.ne',hc.ne',hz]
    <;> ring
  have hterm3 : Real.cosh (2*a*q)/(8*z*Real.sinh (a*q)^2)=(K+1)/(8*z) := by
    rw [show 2*a*q=2*(a*q) by ring,Real.cosh_two_mul]
    dsimp only [K]
    field_simp [hsa.ne',hz]
    <;> ring_nf <;> simp
  rw [hterm1,hterm2,hterm3]
  exact signed_energy_ratio_eliminate hz hf hA hquad hK

theorem signedNormalizedEnergy_eq_potential {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    wedgeNormalizedEnergy D F h=
      wedgePotential (lowerPhysicalA F) (lowerPhysicalD D) (wedgeRight D F h)/lowerPhysicalD D := by
  have hF : 0<F := by linarith
  have hp := (wedge_turns_pos D F h hh).2
  have hv := (potential_branches_values D F h hh (show h∈Icc 0 h from ⟨hh.1.le,le_rfl⟩)).2
  have hR := signed_potential_at_position D F (potentialRightPosition D F h)
    hF hF1 hhalf hD.ne' hp
  rw [hv] at hR
  change h=wedgeEnergyScale D F*
    wedgePotential (lowerPhysicalA F) (lowerPhysicalD D) (wedgeRight D F h)+zeroEndpointHeight D F at hR
  have hd := (positiveD_parameter_bounds hD hF0 hF1).2.2.1
  have hs : wedgeEnergyScale D F≠0 := div_ne_zero (neg_ne_zero.mpr hD.ne') hF.ne'
  unfold wedgeNormalizedEnergy
  conv_lhs => rw [hR]
  field_simp [hs,show lowerPhysicalD D≠0 by linarith]
  <;> ring

theorem actual_signed_energy_ratio {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    wedgeNormalizedEnergy D F h/(wedgeWidth D F h)^2=
      secantEnergyRatio (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h) := by
  obtain ⟨ha,hau,hd,hes⟩ := positiveD_parameter_bounds hD hF0 hF1
  have hF : 0<F := by linarith
  have ha1 := lowerPhysicalA_ne_one hF hhalf
  have hq := wedgeLogSecant_pos hF hh
  have hnu := wedgeGeometricMean_pos hh
  have ht := wedge_turn_decomposition hh
  have hp := (signed_turns_same_potential hD hF hF1 hhalf hh).symm
  rw [ht.1,ht.2] at hp
  have he := signed_secant_energy_hyperbolic ha ha1 (show lowerPhysicalD D≠0 by linarith) hnu hq hp
  have hz : 1+saddleOmega D F h≠0 := by linarith [saddleOmega_lt_neg_one hD hF0 hF1 hh]
  have hquad : wedgeF D F h*(1+saddleOmega D F h)+
      (saddleBeta D F*saddleRoot D F h)*(1-wedgeF D F h)-1=0 := by
    nlinarith only [saddleRoot_quadratic hD hF0 hF1 hhalf hh]
  have hr := signed_hyperbolic_energy_ratio ha ha1 hq hz hquad
  rw [signedNormalizedEnergy_eq_potential hD hF0 hF1 hhalf hh,div_div,ht.1,wedgeWidth_hyperbolic hh,he]
  have homega : 1+saddleOmega D F h=lowerPhysicalA F*lowerPhysicalD D*saddleRoot D F h^2 := by
    unfold saddleOmega
    ring
  change Real.cosh (2*wedgeLogSecant D F h)/(8*Real.sinh (wedgeLogSecant D F h)^2)+
    (saddleBeta D F*saddleRoot D F h)*Real.cosh ((1-lowerPhysicalA F)*wedgeLogSecant D F h)/
      (4*(lowerPhysicalA F*lowerPhysicalD D*saddleRoot D F h^2)*Real.sinh (wedgeLogSecant D F h)*
        Real.sinh (lowerPhysicalA F*wedgeLogSecant D F h))+
    Real.cosh (2*lowerPhysicalA F*wedgeLogSecant D F h)/
      (8*(lowerPhysicalA F*lowerPhysicalD D*saddleRoot D F h^2)*Real.sinh (lowerPhysicalA F*wedgeLogSecant D F h)^2)=_
  rw [←homega,hr]
  rfl

theorem actual_signed_energy_width_identity {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    wedgeNormalizedEnergy D F h=(wedgeWidth D F h)^2*
      secantEnergyRatio (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h) := by
  have he := actual_signed_energy_ratio hD hF0 hF1 hhalf hh
  have hw := wedgeWidth_pos (by linarith : 0<F) hh
  exact (div_eq_iff (pow_ne_zero 2 hw.ne')).mp he |>.trans (mul_comm _ _)

end LeanVerification.PositiveDCompletion
