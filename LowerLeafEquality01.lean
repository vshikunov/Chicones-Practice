import LeanVerification.PositiveDCompletion.UpperPolynomial01
import LeanVerification.PositiveDCompletion.LowerPolynomial01Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 10000000
set_option maxRecDepth 30000

theorem lowerNum01_eq_upper (a f rho : ℝ) :
    lowerNum01 a f rho=-upperNum01 a f rho := by
  unfold lowerNum01 upperNum01
  unfold lowerNum01Coeff0 lowerNum01Coeff1 lowerNum01Coeff2 lowerNum01Coeff3
  ring

end LeanVerification.PositiveDCompletion
