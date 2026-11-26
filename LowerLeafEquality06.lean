import LeanVerification.PositiveDCompletion.UpperPolynomial06
import LeanVerification.PositiveDCompletion.LowerPolynomial06Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum06_eq_upper (a f rho : ℝ) :
    lowerNum06 a f rho=upperNum06 a f rho := by
  unfold lowerNum06 upperNum06
  unfold lowerNum06Coeff0 lowerNum06Coeff1 lowerNum06Coeff2 lowerNum06Coeff3 lowerNum06Coeff4 lowerNum06Coeff5 lowerNum06Coeff6
  unfold upperNum06Coeff0 upperNum06Coeff1 upperNum06Coeff2 upperNum06Coeff3 upperNum06Coeff4 upperNum06Coeff5 upperNum06Coeff6
  ring

end LeanVerification.PositiveDCompletion
