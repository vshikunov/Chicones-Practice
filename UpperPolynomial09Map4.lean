import LeanVerification.PositiveDCompletion.UpperPolynomial09Map4Kernel
import LeanVerification.PositiveDCompletion.UpperPolynomial09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum09Coeff4_map (a t : ℝ) :
    upperNum09Coeff4 a (a+(1-a)*t)*(a+(1-a)*t)^(2 : ℕ)*a^(4 : ℕ)=(1-a)^(4 : ℕ)*upperAtom09Coeff4 a t := by
  exact upperNum09Coeff4_map_source_value a t

end LeanVerification.PositiveDCompletion
