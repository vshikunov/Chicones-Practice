import LeanVerification.PositiveDCompletion.UpperPolynomial09Data
import LeanVerification.PositiveDCompletion.LowerPolynomial09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum09_eq_upper (a f rho : ℝ) :
    lowerNum09 a f rho=upperNum09 a f rho := by
  unfold lowerNum09 upperNum09
  unfold lowerNum09Coeff0 lowerNum09Coeff1 lowerNum09Coeff2 lowerNum09Coeff3 lowerNum09Coeff4 lowerNum09Coeff5 lowerNum09Coeff6
  unfold upperNum09Coeff0 upperNum09Coeff1 upperNum09Coeff2 upperNum09Coeff3 upperNum09Coeff4 upperNum09Coeff5 upperNum09Coeff6
  ring

end LeanVerification.PositiveDCompletion
