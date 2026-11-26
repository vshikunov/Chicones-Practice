import LeanVerification.PositiveDCompletion.UpperPolynomial07
import LeanVerification.PositiveDCompletion.LowerPolynomial07Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum07_eq_upper (a f rho : ℝ) :
    lowerNum07 a f rho=upperNum07 a f rho := by
  unfold lowerNum07 upperNum07
  unfold lowerNum07Coeff0 lowerNum07Coeff1 lowerNum07Coeff2 lowerNum07Coeff3 lowerNum07Coeff4 lowerNum07Coeff5 lowerNum07Coeff6
  unfold upperNum07Coeff0 upperNum07Coeff1 upperNum07Coeff2 upperNum07Coeff3 upperNum07Coeff4 upperNum07Coeff5 upperNum07Coeff6
  ring

end LeanVerification.PositiveDCompletion
