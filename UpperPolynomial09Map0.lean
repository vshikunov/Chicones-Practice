import LeanVerification.PositiveDCompletion.UpperPolynomial09Map0Kernel
import LeanVerification.PositiveDCompletion.UpperPolynomial09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum09Coeff0_map (a t : ℝ) :
    upperNum09Coeff0 a (a+(1-a)*t)*(a+(1-a)*t)^(6 : ℕ)*a^(0 : ℕ)=(1-a)^(4 : ℕ)*upperAtom09Coeff0 a t := by
  exact upperNum09Coeff0_map_source_value a t

end LeanVerification.PositiveDCompletion
