import LeanVerification.PositiveDCompletion.UpperPolynomial04
import LeanVerification.PositiveDCompletion.LowerPolynomial04Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum04_eq_upper (a f rho : ℝ) :
    lowerNum04 a f rho=upperNum04 a f rho := by
  unfold lowerNum04 upperNum04
  unfold lowerNum04Coeff0 lowerNum04Coeff1 lowerNum04Coeff2 lowerNum04Coeff3 lowerNum04Coeff4
  unfold upperNum04Coeff0 upperNum04Coeff1 upperNum04Coeff2 upperNum04Coeff3 upperNum04Coeff4
  ring

end LeanVerification.PositiveDCompletion
