import LeanVerification.PositiveDCompletion.UpperPolynomial09Map6Kernel
import LeanVerification.PositiveDCompletion.UpperPolynomial09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum09Coeff6_map (a t : ℝ) :
    upperNum09Coeff6 a (a+(1-a)*t)*(a+(1-a)*t)^(0 : ℕ)*a^(6 : ℕ)=(1-a)^(4 : ℕ)*upperAtom09Coeff6 a t := by
  exact upperNum09Coeff6_map_source_value a t

end LeanVerification.PositiveDCompletion
