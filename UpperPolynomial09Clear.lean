import LeanVerification.PositiveDCompletion.UpperPolynomial09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum09_clear (a f rho : ℝ) :
    f^(6 : ℕ)*upperNum09 a f rho=upperCorrelated09 a f (f*rho) := by
  unfold upperNum09 upperCorrelated09
  ring

end LeanVerification.PositiveDCompletion
