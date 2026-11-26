import LeanVerification.PositiveDCompletion.UpperPolynomial05
import LeanVerification.PositiveDCompletion.LowerPolynomial05Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum05_eq_upper (a f rho : ℝ) :
    lowerNum05 a f rho=-upperNum05 a f rho := by
  unfold lowerNum05 upperNum05
  unfold lowerNum05Coeff0 lowerNum05Coeff1 lowerNum05Coeff2 lowerNum05Coeff3 lowerNum05Coeff4
  unfold upperNum05Coeff0 upperNum05Coeff1 upperNum05Coeff2 upperNum05Coeff3 upperNum05Coeff4
  ring

end LeanVerification.PositiveDCompletion
