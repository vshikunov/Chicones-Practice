import LeanVerification.PositiveDCompletion.LowerCertificate07
import LeanVerification.PositiveDCompletion.LowerMap07

noncomputable section
namespace LeanVerification.PositiveDCompletion

theorem lowerNum07_pos {a f rho : ℝ} (ha : 1<a) (hau : a<3)
    (hf : 1<f) (hfa : f<a) (hr : a/f<rho) (hru : rho<lowerEnvelope a f) :
    0<lowerNum07 a f rho := by
  obtain ⟨x,t,u,hx,hxu,ht,htu,hu,huu,haeq,hfeq,hreq⟩ :=
    lower_correlated_coordinates ha hau hf hfa hr hru
  subst a
  rw [hfeq,hreq]
  have hp := lowerAtom07_pos hx hxu ht htu hu huu
  have htc : 0<1-t := by linarith
  have hxc : 0<2*x := by positivity
  have hfactor : 0<(2*x)^4*t^1*(1-t)^4 := by positivity
  have hprod := mul_pos hfactor hp
  rw [←lowerNum07_map hx hxu ht htu] at hprod
  exact pos_of_mul_pos_right hprod
    (pow_pos (lowerRhoDen_pos (by linarith : 1<1+2*x) (by linarith : 1+2*x<3) ht htu) 6).le

end LeanVerification.PositiveDCompletion
