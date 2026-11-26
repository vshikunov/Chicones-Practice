import LeanVerification.ReflectedWedgeCompletion.WidthPeriodTransfer

/-! A real inverse-width criterion for the complete physical period.
The final transfer includes the identically zero Abel-input alternative. -/
noncomputable section
open Set Filter
open scoped Topology
namespace LeanVerification.PositiveDCompletion
open Loud
set_option maxHeartbeats 1800000

theorem width_curvature_pos_of_Q_pos {w w1 w2 h : ℝ}
    (hw : 0<w) (hw1 : 0<w1)
    (hQ : 0< -w/4+h*w1+h^2*w2) :
    0<w1^2+w*w2 := by
  by_cases hw2 : 0≤w2
  · exact add_pos_of_pos_of_nonneg (sq_pos_of_pos hw1) (mul_nonneg hw.le hw2)
  · have hw2n : w2<0 := lt_of_not_ge hw2
    have hp := mul_pos (neg_pos.mpr hw2n) hQ
    nlinarith [sq_nonneg (w1+2*h*w2)]

theorem width_euler_algebra (w w1 w2 w3 h : ℝ) :
    4*w1*((-w/8+5*h*w1/4+7*h^2*w2/2+h^3*w3)-
      (-w/4+h*w1+h^2*w2)/2)=
      3*h*(w1+2*h*w2)^2+4*h^3*(w1*w3-3*w2^2) := by ring

theorem width_euler_pos_of_schwarz {w w1 w2 w3 h : ℝ}
    (hh : 0<h) (hw1 : 0<w1)
    (hQ : 0< -w/4+h*w1+h^2*w2)
    (hS : 0≤w1*w3-3*w2^2) :
    0< -w/8+5*h*w1/4+7*h^2*w2/2+h^3*w3 := by
  have hp : 0≤3*h*(w1+2*h*w2)^2+4*h^3*(w1*w3-3*w2^2) := by positivity
  rw [←width_euler_algebra w w1 w2 w3 h] at hp
  have hdiff := nonneg_of_mul_nonneg_right hp (mul_pos (by norm_num : (0:ℝ)<4) hw1)
  linarith

theorem physical_width_euler_of_schwarz (D F h : ℝ)
    (hh : AdmissibleEnergy D F h)
    (hS : 0<(deriv (physicalEnergyWidth D F) h)^2+
        physicalEnergyWidth D F h*deriv (deriv (physicalEnergyWidth D F)) h →
      0≤deriv (physicalEnergyWidth D F) h*deriv (deriv (deriv (physicalEnergyWidth D F))) h-
        3*(deriv (deriv (physicalEnergyWidth D F)) h)^2)
    (hQ : 0<InverseWidthComparison.widthQ (physicalEnergyWidth D F) h) :
    0<h*deriv (InverseWidthComparison.widthQ (physicalEnergyWidth D F)) h+
      (1/2:ℝ)*InverseWidthComparison.widthQ (physicalEnergyWidth D F) h := by
  have hw := physicalEnergyWidth_pos D F h hh
  have hw1 := physicalEnergyWidth_deriv_pos_of_width_chart D F h hh
  have ha : AnalyticAt ℝ (physicalEnergyWidth D F) h :=
    (analyticAt_physicalEnergyWidth_joint D F h hh).comp_of_eq
      (f := fun t : ℝ => ((D,F),t)) (analyticAt_const.prod analyticAt_id) rfl
  have hc := width_curvature_pos_of_Q_pos hw hw1 hQ
  have he := width_euler_pos_of_schwarz hh.1 hw1 hQ (hS hc)
  rw [InverseWidthComparison.deriv_widthQ ha]
  convert he using 1 <;> dsimp only [InverseWidthComparison.widthQ] <;> ring

theorem criticalPeriodBound_one_of_width_schwarz (D F : ℝ)
    (hS : ∀h,AdmissibleEnergy D F h →
      0<(deriv (physicalEnergyWidth D F) h)^2+
        physicalEnergyWidth D F h*deriv (deriv (physicalEnergyWidth D F)) h →
      0≤deriv (physicalEnergyWidth D F) h*deriv (deriv (deriv (physicalEnergyWidth D F))) h-
        3*(deriv (deriv (physicalEnergyWidth D F)) h)^2) :
    CriticalPeriodBound 1 D F :=
  ReflectedWedgeCompletion.criticalPeriodBound_one_of_width_euler D F
    (fun h hh hQ => (physical_width_euler_of_schwarz D F h hh (hS h hh) hQ).le)

end LeanVerification.PositiveDCompletion
