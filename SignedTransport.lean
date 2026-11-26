import LeanVerification.PositiveDCompletion.PhysicalSheet

noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion
set_option maxHeartbeats 14000000
set_option maxRecDepth 26000

def saddleRootRate (D F h : ℝ) : ℝ := deriv (saddleRoot D F) h/saddleRoot D F h

theorem differentiableAt_saddleRoot {D F h : ℝ}
    (ha : 0<lowerPhysicalA F) (hF : 0<F) (hh : AdmissibleEnergy D F h) :
    DifferentiableAt ℝ (saddleRoot D F) h := by
  have hq := differentiableAt_wedgeLogSecant hh
  have hn := differentiableAt_wedgeGeometricMean hh
  exact ((hn.rpow_const (Or.inl (wedgeGeometricMean_pos hh).ne')).mul
    hq.sinh).div ((hq.const_mul _).sinh)
      (Real.sinh_pos_iff.mpr (mul_pos ha (wedgeLogSecant_pos hF hh))).ne'

theorem saddle_root_log_derivative {D F h : ℝ}
    (ha : 0<lowerPhysicalA F) (hF : 0<F) (hh : AdmissibleEnergy D F h)
    :
    deriv (saddleRoot D F) h/saddleRoot D F h=
      (1+lowerPhysicalA F)*deriv (wedgeGeometricMean D F) h/wedgeGeometricMean D F h+
        (Real.cosh (wedgeLogSecant D F h)/Real.sinh (wedgeLogSecant D F h)-
          lowerPhysicalA F*Real.cosh (lowerPhysicalA F*wedgeLogSecant D F h)/
            Real.sinh (lowerPhysicalA F*wedgeLogSecant D F h))*deriv (wedgeLogSecant D F) h := by
  have hn := (differentiableAt_wedgeGeometricMean hh).hasDerivAt
  have hq := (differentiableAt_wedgeLogSecant hh).hasDerivAt
  have hnu := wedgeGeometricMean_pos hh
  have hs := Real.sinh_pos_iff.mpr (wedgeLogSecant_pos hF hh)
  have hsa := Real.sinh_pos_iff.mpr (mul_pos ha (wedgeLogSecant_pos hF hh))
  have hp := hn.rpow_const (p := 1+lowerPhysicalA F) (Or.inl hnu.ne')
  have hd := (hp.mul hq.sinh).div
    ((hq.const_mul (lowerPhysicalA F)).sinh) hsa.ne'
  have hder : deriv (saddleRoot D F) h = _ := hd.deriv
  have hpow : wedgeGeometricMean D F h^(1+lowerPhysicalA F-1)=
      wedgeGeometricMean D F h^(1+lowerPhysicalA F)/wedgeGeometricMean D F h := by
    rw [Real.rpow_sub hnu,Real.rpow_one]
  rw [hder]
  dsimp only [saddleRoot]
  rw [hpow]
  field_simp [hnu.ne',hs.ne',hsa.ne',
    (Real.rpow_pos_of_pos hnu (1+lowerPhysicalA F)).ne']
  <;> ring

theorem saddle_log_transport_identity {D F h : ℝ}
    (ha : 0<lowerPhysicalA F) (hF : 0<F) (hh : AdmissibleEnergy D F h)
    :
    (1+lowerPhysicalA F)*wedgeRate D F h=saddleRootRate D F h+wedgeSecantRate D F h := by
  have hs := Real.sinh_pos_iff.mpr (wedgeLogSecant_pos hF hh)
  have hsa := Real.sinh_pos_iff.mpr (mul_pos ha (wedgeLogSecant_pos hF hh))
  have hc := Real.cosh_pos (lowerPhysicalA F*wedgeLogSecant D F h)
  have hcot : Real.cosh (wedgeLogSecant D F h)/Real.sinh (wedgeLogSecant D F h)=
      wedgeF D F h*Real.cosh (lowerPhysicalA F*wedgeLogSecant D F h)/
        Real.sinh (lowerPhysicalA F*wedgeLogSecant D F h) := by
    unfold wedgeF secantF secantR
    field_simp [ha.ne',hs.ne',hsa.ne',hc.ne']
    <;> ring
  unfold saddleRootRate wedgeSecantRate
  rw [wedge_width_log_derivative hF hh,saddle_root_log_derivative ha hF hh,hcot]
  ring

theorem hasDerivAt_wedgeF_general {D F h : ℝ}
    (ha : 0<lowerPhysicalA F) (ha1 : lowerPhysicalA F≠1)
    (hF : 0<F) (hh : AdmissibleEnergy D F h) :
    HasDerivAt (wedgeF D F)
      (wedgeSecantRate D F h*(wedgeF D F h-lowerPhysicalA F*wedgeRho D F h)*
        (1-wedgeF D F h)/(1-(lowerPhysicalA F)^2*wedgeRho D F h)) h := by
  have hq := (differentiableAt_wedgeLogSecant hh).hasDerivAt
  have hd := ((secantR_flow_general ha ha1 (wedgeLogSecant_pos hF hh)).const_mul (lowerPhysicalA F)).comp h hq
  convert hd using 1
  unfold wedgeSecantRate wedgeF wedgeRho secantF
  ring

theorem hasDerivAt_wedgeRho_general {D F h : ℝ}
    (ha : 0<lowerPhysicalA F) (ha1 : lowerPhysicalA F≠1)
    (hF : 0<F) (hh : AdmissibleEnergy D F h) :
    HasDerivAt (wedgeRho D F)
      (-2*wedgeSecantRate D F h*(wedgeF D F h-lowerPhysicalA F)*wedgeRho D F h/
        (lowerPhysicalA F*(1+wedgeF D F h))) h := by
  have hq := (differentiableAt_wedgeLogSecant hh).hasDerivAt
  have hf := secantF_pos ha (wedgeLogSecant_pos hF hh)
  have hj : 1+wedgeF D F h≠0 := by unfold wedgeF;linarith
  have hd := (secantRho_flow_general ha (wedgeLogSecant_pos hF hh)).comp h hq
  convert hd using 1
  have hsa := Real.sinh_pos_iff.mpr (mul_pos ha (wedgeLogSecant_pos hF hh))
  unfold wedgeF secantF at hj
  unfold wedgeSecantRate wedgeF wedgeRho secantF
  field_simp [ha.ne',hj,hsa.ne']
  <;> ring

theorem saddleF_ne_one {D F h : ℝ} (ha : 0<lowerPhysicalA F)
    (ha1 : lowerPhysicalA F≠1) (hF : 0<F) (hh : AdmissibleEnergy D F h) :
    1-wedgeF D F h≠0 := by
  have hq := wedgeLogSecant_pos hF hh
  rcases lt_or_gt_of_ne ha1 with hl|hu
  · have hf := (secantF_bounds ha hl hq).2
    change wedgeF D F h<1 at hf
    linarith
  · have hf := (secant_lower_bounds hu hq).1
    change 1<wedgeF D F h at hf
    linarith

theorem saddle_quadratic_log_derivative {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    (1+wedgeF D F h+wedgeF D F h*saddleOmega D F h)*saddleRootRate D F h+
      saddleOmega D F h*deriv (wedgeF D F) h/(1-wedgeF D F h)=0 := by
  obtain ⟨ha,hau,hd,hes⟩ := positiveD_parameter_bounds hD hF0 hF1
  have hF : 0<F := by linarith
  have ha1 := lowerPhysicalA_ne_one hF hhalf
  have hfd := (hasDerivAt_wedgeF_general ha ha1 hF hh).differentiableAt.hasDerivAt
  have hQd := (differentiableAt_saddleRoot ha hF hh).hasDerivAt
  have hder := ((hfd.mul ((hQd.pow 2).const_mul (lowerPhysicalA F*lowerPhysicalD D))).add
    (((hfd.const_sub 1).mul hQd).const_mul (saddleBeta D F))).sub_const 1
  have he : (fun t => wedgeF D F t*(lowerPhysicalA F*lowerPhysicalD D*saddleRoot D F t^2)+
      saddleBeta D F*((1-wedgeF D F t)*saddleRoot D F t)-1) =ᶠ[𝓝 h] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_admissibleEnergy D F).mem_nhds hh] with t ht
    have hquad := saddleRoot_quadratic hD hF0 hF1 hhalf ht
    unfold saddleOmega at hquad
    convert hquad using 1 <;> ring
  have hdz := (hder.congr_of_eventuallyEq he.symm).unique (hasDerivAt_const h (0 : ℝ))
  have hp := saddleRoot_quadratic hD hF0 hF1 hhalf hh
  have hQ := (saddleRoot_pos ha hF hh).ne'
  have h1f := saddleF_ne_one ha ha1 hF hh
  unfold saddleRootRate saddleOmega at *
  field_simp [hQ,h1f]
  linear_combination saddleRoot D F h*(1-wedgeF D F h)*hdz-
    ((1-wedgeF D F h)*deriv (saddleRoot D F) h-
      saddleRoot D F h*deriv (wedgeF D F) h)*hp

theorem hasDerivAt_saddleOmega {D F h : ℝ}
    (ha : 0<lowerPhysicalA F) (hF : 0<F) (hh : AdmissibleEnergy D F h) :
    HasDerivAt (saddleOmega D F) (2*(1+saddleOmega D F h)*saddleRootRate D F h) h := by
  have hd := (((differentiableAt_saddleRoot ha hF hh).hasDerivAt.pow 2).const_mul
    (lowerPhysicalA F*lowerPhysicalD D)).sub_const 1
  have hQ := (saddleRoot_pos ha hF hh).ne'
  convert hd using 1
  unfold saddleRootRate saddleOmega
  field_simp [hQ]
  <;> ring

theorem wedgeSecantRate_pos {D F h : ℝ}
    (ha : 0<lowerPhysicalA F) (hF : 0<F) (hh : AdmissibleEnergy D F h) :
    0<wedgeSecantRate D F h := by
  have hf := secantF_pos ha (wedgeLogSecant_pos hF hh)
  change 0<wedgeF D F h at hf
  unfold wedgeSecantRate
  exact mul_pos (mul_pos (div_pos (mul_pos ha (Real.cosh_pos _))
    (Real.sinh_pos_iff.mpr (mul_pos ha (wedgeLogSecant_pos hF hh)))) (by linarith))
      (wedgeLogSecant_deriv_pos hF hh)

theorem transportN_cleared_relation {a f rho omega lam c z df : ℝ}
    (hf : 1-f≠0) (hg : 1-a^2*rho≠0)
    (hlog : (1+a)*lam=z+c)
    (hquad : (1+f+f*omega)*z+omega*df/(1-f)=0)
    (hdf : df=c*(f-a*rho)*(1-f)/(1-a^2*rho)) :
    transportN a f rho omega*c=(1+a)*lam*(1-a^2*rho)*(1+f+f*omega) := by
  have hq : (1-a^2*rho)*(1+f+f*omega)*z+omega*(f-a*rho)*c=0 := by
    rw [hdf] at hquad
    field_simp [hg,hf] at hquad
    have he : ((1-a^2*rho)*(1+f+f*omega)*z+omega*(f-a*rho)*c)*(1-f)=0 := by
      linear_combination hquad
    exact (mul_eq_zero.mp he).resolve_right hf
  unfold transportN
  linear_combination -(1-a^2*rho)*(1+f+f*omega)*hlog-hq

theorem physical_transportN_sign {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    transportN (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)*
      (1-(lowerPhysicalA F)^2*wedgeRho D F h)<0 := by
  obtain ⟨ha,hau,hd,hes⟩ := positiveD_parameter_bounds hD hF0 hF1
  have hF : 0<F := by linarith
  have ha1 := lowerPhysicalA_ne_one hF hhalf
  have hg := secant_g_ne_zero ha ha1 (wedgeLogSecant_pos hF hh)
  change 1-(lowerPhysicalA F)^2*wedgeRho D F h≠0 at hg
  have hfd := hasDerivAt_wedgeF_general ha ha1 hF hh
  have hrel := transportN_cleared_relation (saddleF_ne_one ha ha1 hF hh) hg
    (saddle_log_transport_identity ha hF hh)
    (saddle_quadratic_log_derivative hD hF0 hF1 hhalf hh) hfd.deriv
  have hb := physical_signed_branch_negative hD hF0 hF1 hhalf hh
  have hb' : 1+wedgeF D F h+wedgeF D F h*saddleOmega D F h<0 := by nlinarith only [hb]
  have hc := wedgeSecantRate_pos ha hF hh
  have hl := wedgeRate_pos hF hh
  have hneg : (transportN (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)*
      (1-(lowerPhysicalA F)^2*wedgeRho D F h))*wedgeSecantRate D F h<0 := by
    calc
      _ = (transportN (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)*
        wedgeSecantRate D F h)*(1-(lowerPhysicalA F)^2*wedgeRho D F h) := by ring
      _ = (1+lowerPhysicalA F)*wedgeRate D F h*(1-(lowerPhysicalA F)^2*wedgeRho D F h)^2*
        (1+wedgeF D F h+wedgeF D F h*saddleOmega D F h) := by rw [hrel];ring
      _ < 0 := mul_neg_of_pos_of_neg
        (mul_pos (mul_pos (by linarith) hl) (sq_pos_of_ne_zero hg)) hb'
  by_contra hn
  have hp := mul_nonneg (le_of_not_gt hn) hc.le
  linarith

theorem actual_signed_secant_transport {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h) :
    HasDerivAt (wedgeF D F)
        (wedgeRate D F h*transportF (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)) h ∧
      HasDerivAt (wedgeRho D F)
        (wedgeRate D F h*transportRho (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)) h ∧
      HasDerivAt (saddleOmega D F)
        (wedgeRate D F h*transportOmega (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)) h := by
  obtain ⟨ha,hau,hd,hes⟩ := positiveD_parameter_bounds hD hF0 hF1
  have hF : 0<F := by linarith
  have ha1 := lowerPhysicalA_ne_one hF hhalf
  have hq := wedgeLogSecant_pos hF hh
  have hf := secantF_pos ha hq
  change 0<wedgeF D F h at hf
  have hn : transportN (lowerPhysicalA F) (wedgeF D F h) (wedgeRho D F h) (saddleOmega D F h)≠0 := by
    intro he
    have hs := physical_transportN_sign hD hF0 hF1 hhalf hh
    rw [he,zero_mul] at hs
    linarith
  have hg := secant_g_ne_zero ha ha1 hq
  have hfd := hasDerivAt_wedgeF_general ha ha1 hF hh
  have hrd := hasDerivAt_wedgeRho_general ha ha1 hF hh
  have hwd := hasDerivAt_saddleOmega ha hF hh
  have hs := solve_secant_transport ha.ne' (show 1+wedgeF D F h≠0 by linarith)
    (saddleF_ne_one ha ha1 hF hh) hg hn
    (saddle_log_transport_identity ha hF hh)
    (saddle_quadratic_log_derivative hD hF0 hF1 hhalf hh) hfd.deriv hrd.deriv hwd.deriv
  exact ⟨hs.1 ▸ hfd.differentiableAt.hasDerivAt,
    hs.2.1 ▸ hrd.differentiableAt.hasDerivAt,hs.2.2 ▸ hwd.differentiableAt.hasDerivAt⟩

end LeanVerification.PositiveDCompletion
