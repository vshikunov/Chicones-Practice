import LeanVerification.PositiveDCompletion.UpperPolynomial03
import LeanVerification.PositiveDCompletion.LowerPolynomial03Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum03_eq_upper (a f rho : ℝ) :
    lowerNum03 a f rho=upperNum03 a f rho := by
  unfold lowerNum03 upperNum03
  unfold lowerNum03Coeff0 lowerNum03Coeff1 lowerNum03Coeff2 lowerNum03Coeff3 lowerNum03Coeff4
  unfold upperNum03Coeff0 upperNum03Coeff1 upperNum03Coeff2 upperNum03Coeff3 upperNum03Coeff4
  ring

end LeanVerification.PositiveDCompletion
