import LeanVerification.PositiveDCompletion.UpperPolynomial08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum08_clear (a f rho : ℝ) :
    f^(6 : ℕ)*upperNum08 a f rho=upperCorrelated08 a f (f*rho) := by
  unfold upperNum08 upperCorrelated08
  ring

end LeanVerification.PositiveDCompletion
