import LeanVerification.ReflectedWedgeCompletion.PhysicalSecants

/-! The exact physical normalization on the positive-D saddle family.
The raw reference height is used only as an affine energy offset. -/
noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion
set_option maxHeartbeats 4000000

theorem signed_potential_at_w (D F w : ℝ)
    (hF : 0<F) (hF1 : F<1) (hhalf : F≠1/2) (hD : D≠0) (hw : 0<w) :
    potential D F w=wedgeEnergyScale D F*
      wedgePotential (lowerPhysicalA F) (lowerPhysicalD D) (w^F)+zeroEndpointHeight D F := by
  have h2F : 2*F-1≠0 := by intro he;apply hhalf;linarith
  have h2Fm : 2*F-2≠0 := by linarith
  have h1F : 1-F≠0 := by linarith
  have ht : lowerT (lowerPhysicalA F) (w^F)=1/w := by
    unfold lowerT lowerPhysicalA
    rw [←Real.rpow_mul hw.le]
    have he : F*(-(1/F-1)-1)=(-1 : ℝ) := by field_simp
    rw [he,Real.rpow_neg_one,one_div]
  have hp := BoundaryAssembly.potential_minus_endpoint_factorization D F w hw
    (by linarith) h2F h2Fm
  have he : (w^F)^2=w^(2*F-2)*w^2 := by
    rw [←Real.rpow_two,←Real.rpow_mul hw.le]
    calc
      w^(F*2)=w^((2*F-2)+2) := by congr 1;ring
      _ = _ := by rw [Real.rpow_add hw,Real.rpow_two]
  rw [wedgePotential_t_form _ _ (Real.rpow_pos_of_pos hw _),ht,he]
  have hDn : D≠0 := hD
  have hak : lowerPhysicalA F=(1-F)/F := by unfold lowerPhysicalA;field_simp
  have hpk : 1-lowerPhysicalA F=(2*F-1)/F := by unfold lowerPhysicalA;field_simp;ring
  have ha0 : lowerPhysicalA F≠0 := by rw [hak];exact div_ne_zero h1F hF.ne'
  have h1a0 : 1-lowerPhysicalA F≠0 := by rw [hpk];exact div_ne_zero h2F hF.ne'
  have hc0 : wedgeEnergyScale D F*lowerPhysicalD D/2=(D+1)/(2*F) := by
    unfold wedgeEnergyScale lowerPhysicalD
    field_simp [hDn,hF.ne',h2F,h2Fm,h1F]
    <;> ring
  have hc1 : wedgeEnergyScale D F*(1-lowerPhysicalD D)/(1-lowerPhysicalA F)=
      -(2*D+1)/(2*F-1) := by
    rw [hpk]
    unfold wedgeEnergyScale lowerPhysicalD
    field_simp [hDn,hF.ne',h2F,h2Fm,h1F]
    <;> ring
  have hc2 : wedgeEnergyScale D F/(2*lowerPhysicalA F)=D/(2*F-2) := by
    rw [hak]
    unfold wedgeEnergyScale
    field_simp [hF.ne',h1F,h2Fm]
    <;> ring
  have hc : wedgeEnergyScale D F*(w^(2*F-2)*w^2*
      (lowerPhysicalD D/2+(1-lowerPhysicalD D)/(1-lowerPhysicalA F)*(1/w)+
        1/(2*lowerPhysicalA F)*(1/w)^2)) =
      w^(2*F-2)*((D+1)/(2*F)*w^2-(2*D+1)/(2*F-1)*w+D/(2*F-2)) := by
    calc
      _ = w^(2*F-2)*(wedgeEnergyScale D F*lowerPhysicalD D/2*w^2+
          wedgeEnergyScale D F*(1-lowerPhysicalD D)/(1-lowerPhysicalA F)*w+
          wedgeEnergyScale D F/(2*lowerPhysicalA F)) := by
        field_simp [hw.ne',ha0,h1a0]
        <;> ring
      _ = _ := by rw [hc0,hc1,hc2];ring
  rw [hc]
  dsimp only [BoundaryAssembly.exteriorQuadratic] at hp
  linear_combination hp

theorem signed_potential_at_position (D F X : ℝ)
    (hF : 0<F) (hF1 : F<1) (hhalf : F≠1/2) (hD : D≠0)
    (hX : mechanicalDomain F X) :
    potential D F (inversePosition F X)=wedgeEnergyScale D F*
      wedgePotential (lowerPhysicalA F) (lowerPhysicalD D) (1+F*X)+zeroEndpointHeight D F := by
  rw [signed_potential_at_w D F _ hF hF1 hhalf hD (inversePosition_pos F X hX)]
  rw [←RegionalReal.affineAux_eq_rpow F X hX]
  rfl

theorem positiveD_parameter_bounds {D F : ℝ} (hD : 0<D) (hF : 1/4<F) (hF1 : F<1) :
    0<lowerPhysicalA F ∧ lowerPhysicalA F<3 ∧ lowerPhysicalD D< -1 ∧
      0<wedgeEnergyScale D F*lowerPhysicalD D := by
  have hF0 : 0<F := by linarith
  have ha : 0<lowerPhysicalA F := by
    unfold lowerPhysicalA
    have hi : 1<1/F := (lt_div_iff₀ hF0).mpr (by linarith)
    linarith
  have hau : lowerPhysicalA F<3 := by
    unfold lowerPhysicalA
    have hi : 1/F<4 := (div_lt_iff₀ hF0).mpr (by linarith)
    linarith
  have hd : lowerPhysicalD D< -1 := by
    unfold lowerPhysicalD
    apply (div_lt_iff_of_neg (neg_neg_of_pos hD)).mpr
    linarith
  have he : wedgeEnergyScale D F*lowerPhysicalD D=(D+1)/F := by
    unfold wedgeEnergyScale lowerPhysicalD
    field_simp [hD.ne',hF0.ne']
    <;> ring
  exact ⟨ha,hau,hd,by rw [he];exact div_pos (by linarith) hF0⟩

theorem signed_turns_same_potential {D F h : ℝ}
    (hD : 0<D) (hF : 0<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    wedgePotential (lowerPhysicalA F) (lowerPhysicalD D) (wedgeLeft D F h)=
      wedgePotential (lowerPhysicalA F) (lowerPhysicalD D) (wedgeRight D F h) := by
  have hp := wedge_turns_pos D F h hh
  have hv := potential_branches_values D F h hh (show h∈Icc 0 h from ⟨hh.1.le,le_rfl⟩)
  have hL := signed_potential_at_position D F (potentialLeftPosition D F h)
    hF hF1 hhalf hD.ne' hp.1
  have hR := signed_potential_at_position D F (potentialRightPosition D F h)
    hF hF1 hhalf hD.ne' hp.2
  rw [hv.1] at hL
  rw [hv.2] at hR
  change h=wedgeEnergyScale D F*wedgePotential (lowerPhysicalA F) (lowerPhysicalD D) (wedgeLeft D F h)+zeroEndpointHeight D F at hL
  change h=wedgeEnergyScale D F*wedgePotential (lowerPhysicalA F) (lowerPhysicalD D) (wedgeRight D F h)+zeroEndpointHeight D F at hR
  have hscale : wedgeEnergyScale D F≠0 := div_ne_zero (neg_ne_zero.mpr hD.ne') hF.ne'
  apply (mul_left_cancel₀ hscale)
  linarith

end LeanVerification.PositiveDCompletion
