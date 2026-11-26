import LeanVerification.PositiveDCompletion.ActualCurvatureJet

noncomputable section
namespace LeanVerification.PositiveDCompletion
open Loud ReflectedCompletion ReflectedWedgeCompletion

theorem physical_width_schwarz_of_rx {D F h : ℝ}
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hh : AdmissibleEnergy D F h)
    (hRX : 0<saddleCurvature D F h → 0<saddleRX D F h)
    (hchi : 0<(deriv (physicalEnergyWidth D F) h)^2+
      physicalEnergyWidth D F h*deriv (deriv (physicalEnergyWidth D F)) h) :
    0<deriv (physicalEnergyWidth D F) h*deriv (deriv (deriv (physicalEnergyWidth D F))) h-
      3*(deriv (deriv (physicalEnergyWidth D F)) h)^2 := by
  have hF : 0<F := by linarith
  have he : wedgeWidth D F=fun t => F*physicalEnergyWidth D F t := by
    funext t
    exact wedgeWidth_eq D F t
  have hscale (w1 w2 w3 : ℝ) : (F*w1)*(F*w3)-3*(F*w2)^2=
      F^2*(w1*w3-3*w2^2) := by ring
  have hchis : 0<(deriv (wedgeWidth D F) h)^2+
      wedgeWidth D F h*deriv (deriv (wedgeWidth D F)) h := by
    simp only [he,deriv_const_mul_field']
    convert mul_pos (sq_pos_of_pos hF) hchi using 1 <;> ring
  have hp : 0<saddleCurvature D F h := by
    have hid := physical_curvature_identity hD hF0 hF1 hhalf hh
    have hpos := mul_pos hchis (saddleK_pos hD hF0 hF1 hhalf hh)
    rw [hid] at hpos
    exact pos_of_mul_pos_right hpos (sq_pos_of_pos (wedgeWidth_deriv_pos hF hh)).le
  have hs := width_schwarz_of_signed_curvature hD hF0 hF1 hhalf hh
    (hasDerivAt_saddleCurvature hD hF0 hF1 hhalf hh hp) (hRX hp) hchis
  simp only [he,deriv_const_mul_field',hscale] at hs
  exact pos_of_mul_pos_right hs (sq_pos_of_pos hF).le

theorem criticalPeriodBound_one_of_signed_rx (D F : ℝ)
    (hD : 0<D) (hF0 : 1/4<F) (hF1 : F<1) (hhalf : F≠1/2)
    (hRX : ∀h,AdmissibleEnergy D F h → 0<saddleCurvature D F h → 0<saddleRX D F h) :
    CriticalPeriodBound 1 D F := by
  apply criticalPeriodBound_one_of_width_schwarz D F
  intro h hh hchi
  exact (physical_width_schwarz_of_rx hD hF0 hF1 hhalf hh (hRX h hh) hchi).le

end LeanVerification.PositiveDCompletion
