import LeanVerification.PositiveDCompletion.UpperPolynomial00
import LeanVerification.PositiveDCompletion.LowerPolynomial00Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum00_eq_upper (a f rho : ℝ) :
    lowerNum00 a f rho=upperNum00 a f rho := by
  unfold lowerNum00 upperNum00
  unfold lowerNum00Coeff0 lowerNum00Coeff1 lowerNum00Coeff2
  ring

end LeanVerification.PositiveDCompletion
