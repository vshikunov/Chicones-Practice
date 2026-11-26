import LeanVerification.PositiveDCompletion.UpperPolynomial08Data
import LeanVerification.PositiveDCompletion.LowerPolynomial08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum08_eq_upper (a f rho : ℝ) :
    lowerNum08 a f rho=upperNum08 a f rho := by
  unfold lowerNum08 upperNum08
  unfold lowerNum08Coeff0 lowerNum08Coeff1 lowerNum08Coeff2 lowerNum08Coeff3 lowerNum08Coeff4 lowerNum08Coeff5 lowerNum08Coeff6
  unfold upperNum08Coeff0 upperNum08Coeff1 upperNum08Coeff2 upperNum08Coeff3 upperNum08Coeff4 upperNum08Coeff5 upperNum08Coeff6
  ring

end LeanVerification.PositiveDCompletion
