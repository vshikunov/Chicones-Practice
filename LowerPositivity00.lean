import LeanVerification.PositiveDCompletion.LowerCertificate00
import LeanVerification.PositiveDCompletion.LowerMap00

noncomputable section
namespace LeanVerification.PositiveDCompletion

theorem lowerNum00_pos {a f rho : ℝ} (ha : 1<a) (hau : a<3)
    (hf : 1<f) (hfa : f<a) (hr : a/f<rho) (hru : rho<lowerEnvelope a f) :
    0<lowerNum00 a f rho := by
  obtain ⟨x,t,u,hx,hxu,ht,htu,hu,huu,haeq,hfeq,hreq⟩ :=
    lower_correlated_coordinates ha hau hf hfa hr hru
  subst a
  rw [hfeq,hreq]
  have hp := lowerAtom00_pos hx hxu ht htu hu huu
  have htc : 0<1-t := by linarith
  have hxc : 0<2*x := by positivity
  have hfactor : 0<(2*x)^2*t^1*(1-t)^2 := by positivity
  have hprod := mul_pos hfactor hp
  rw [←lowerNum00_map hx hxu ht htu] at hprod
  exact pos_of_mul_pos_right hprod
    (pow_pos (lowerRhoDen_pos (by linarith : 1<1+2*x) (by linarith : 1+2*x<3) ht htu) 2).le

end LeanVerification.PositiveDCompletion
