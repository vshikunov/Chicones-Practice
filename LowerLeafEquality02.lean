import LeanVerification.PositiveDCompletion.UpperPolynomial02
import LeanVerification.PositiveDCompletion.LowerPolynomial02Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum02_eq_upper (a f rho : ℝ) :
    lowerNum02 a f rho=upperNum02 a f rho := by
  unfold lowerNum02 upperNum02
  unfold lowerNum02Coeff0 lowerNum02Coeff1 lowerNum02Coeff2 lowerNum02Coeff3 lowerNum02Coeff4
  ring

end LeanVerification.PositiveDCompletion
