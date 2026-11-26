import LeanVerification.PositiveDCompletion.SignedQuadratic
import LeanVerification.ReflectedWedgeCompletion.PhysicalTransport
import LeanVerification.Loud.EnergyWidthRegular

noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion
set_option maxHeartbeats 8000000
set_option maxRecDepth 12000

theorem wedge_turn_derivative_signs {D F h : ℝ} (hF : 0<F)
    (hh : AdmissibleEnergy D F h) :
    deriv (wedgeLeft D F) h<0 ∧ 0<deriv (wedgeRight D F) h := by
  have hr : 0<Real.sqrt (2*h) := Real.sqrt_pos.mpr (by linarith [hh.1])
  have huL := morse_amplitude_in_range D F h hh
    (show -Real.sqrt (2*h)∈Icc (-Real.sqrt (2*h)) (Real.sqrt (2*h)) from ⟨le_rfl,by linarith⟩)
  have huR := morse_amplitude_in_range D F h hh
    (show Real.sqrt (2*h)∈Icc (-Real.sqrt (2*h)) (Real.sqrt (2*h)) from ⟨by linarith,le_rfl⟩)
  have hL := (analyticAt_morsePosition D F _ huL).differentiableAt.hasDerivAt.comp h
    (hasDerivAt_sqrt_two_energy hh.1).neg
  have hR := (analyticAt_morsePosition D F _ huR).differentiableAt.hasDerivAt.comp h
    (hasDerivAt_sqrt_two_energy hh.1)
  have hl : HasDerivAt (wedgeLeft D F)
      (F*(deriv (morsePosition D F) (-Real.sqrt (2*h))*(-(1/Real.sqrt (2*h))))) h :=
    (hL.const_mul F).const_add 1
  have hu : HasDerivAt (wedgeRight D F)
      (F*(deriv (morsePosition D F) (Real.sqrt (2*h))*(1/Real.sqrt (2*h)))) h :=
    (hR.const_mul F).const_add 1
  rw [hl.deriv,hu.deriv]
  exact ⟨mul_neg_of_pos_of_neg hF (mul_neg_of_pos_of_neg
    (morsePosition_deriv_pos D F _ huL) (neg_neg_of_pos (one_div_pos.mpr hr))),
    mul_pos hF (mul_pos (morsePosition_deriv_pos D F _ huR) (one_div_pos.mpr hr))⟩

theorem wedgeLogSecant_deriv_pos {D F h : ℝ} (hF : 0<F)
    (hh : AdmissibleEnergy D F h) : 0<deriv (wedgeLogSecant D F) h := by
  have hp := wedge_turns_pos D F h hh
  have ht := analyticAt_wedge_turns hh
  have hs := wedge_turn_derivative_signs hF hh
  have hd := ((ht.2.differentiableAt.hasDerivAt.log hp.2.ne').sub
    (ht.1.differentiableAt.hasDerivAt.log hp.1.ne')).div_const 2
  change HasDerivAt (wedgeLogSecant D F) _ h at hd
  rw [hd.deriv]
  exact div_pos (sub_pos.mpr ((div_neg_of_neg_of_pos hs.1 hp.1).trans
    (div_pos hs.2 hp.2))) (by norm_num)

def saddleForce (a d u : ℝ) : ℝ := d*u+(1-d)*u^(-a)-u^(-2*a-1)

theorem hasDerivAt_wedgePotential {a d u : ℝ} (ha : a≠0) (ha1 : a≠1) (hu : 0<u) :
    HasDerivAt (wedgePotential a d) (saddleForce a d u) u := by
  have h1a : 1-a≠0 := by intro he;apply ha1;linarith
  have h0 := (((hasDerivAt_id u).pow 2).const_mul d).div_const 2
  have h1 := ((hasDerivAt_id u).rpow_const (p := 1-a) (Or.inl hu.ne')).const_mul ((1-d)/(1-a))
  have h2 := ((hasDerivAt_id u).rpow_const (p := -2*a) (Or.inl hu.ne')).const_mul (1/(2*a))
  convert (h0.add h1).add h2 using 1
  dsimp only [saddleForce,id_eq]
  norm_num
  field_simp [ha,h1a]
  <;> ring

theorem signed_force_normalization {D F X : ℝ} (hD : 0<D)
    (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2) (hX : mechanicalDomain F X) :
    forceInPosition D F X= -D*saddleForce (lowerPhysicalA F) (lowerPhysicalD D) (1+F*X) := by
  have hF : 0<F := by linarith
  have ha := (positiveD_parameter_bounds hD hF0 hF1).1
  have ha1 := lowerPhysicalA_ne_one hF hhalf
  have hd := (((hasDerivAt_wedgePotential (d := lowerPhysicalD D) ha.ne' ha1 hX).comp X
    (((hasDerivAt_id X).const_mul F).const_add 1)).const_mul (wedgeEnergyScale D F)).add_const
      (zeroEndpointHeight D F)
  have he : (fun Z => potential D F (inversePosition F Z))=ᶠ[𝓝 X]
      fun Z => wedgeEnergyScale D F*wedgePotential (lowerPhysicalA F) (lowerPhysicalD D) (1+F*Z)+zeroEndpointHeight D F := by
    have hn : ∀ᶠ Z in 𝓝 X,0<1+F*Z :=
      (isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_id))).mem_nhds hX
    filter_upwards [hn] with Z hZ
    exact signed_potential_at_position D F Z hF hF1 hhalf hD.ne' hZ
  have hv := (hasDerivAt_potentialInPosition D F X hX).unique (hd.congr_of_eventuallyEq he)
  rw [hv]
  unfold wedgeEnergyScale
  field_simp [hF.ne']
  <;> ring

theorem saddle_turn_force_signs {D F h : ℝ} (hD : 0<D)
    (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2) (hh : AdmissibleEnergy D F h) :
    0<saddleForce (lowerPhysicalA F) (lowerPhysicalD D) (wedgeLeft D F h) ∧
      saddleForce (lowerPhysicalA F) (lowerPhysicalD D) (wedgeRight D F h)<0 := by
  have hp := wedge_turns_pos D F h hh
  have hr : 0<Real.sqrt (2*h) := Real.sqrt_pos.mpr (by linarith [hh.1])
  have hd := physical_regular_turn_data D F h (Real.sqrt (2*h)) hh le_rfl hr
  have hL := hd.2.2.2.1
  have hR := hd.2.2.2.2.1
  change deriv (fun X => potential D F (inversePosition F X)) (potentialLeftPosition D F h)<0 at hL
  change 0<deriv (fun X => potential D F (inversePosition F X)) (potentialRightPosition D F h) at hR
  rw [(hasDerivAt_potentialInPosition D F _ hp.1).deriv,
    signed_force_normalization hD hF0 hF1 hhalf hp.1] at hL
  rw [(hasDerivAt_potentialInPosition D F _ hp.2).deriv,
    signed_force_normalization hD hF0 hF1 hhalf hp.2] at hR
  change -D*saddleForce (lowerPhysicalA F) (lowerPhysicalD D) (wedgeLeft D F h)<0 at hL
  change 0< -D*saddleForce (lowerPhysicalA F) (lowerPhysicalD D) (wedgeRight D F h) at hR
  constructor
  · by_contra hn
    have hh' := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hD.le) (le_of_not_gt hn)
    linarith
  · by_contra hn
    have hh' := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hD.le) (le_of_not_gt hn)
    linarith

end LeanVerification.PositiveDCompletion
