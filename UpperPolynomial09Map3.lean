import LeanVerification.PositiveDCompletion.UpperPolynomial09Map3Kernel
import LeanVerification.PositiveDCompletion.UpperPolynomial09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum09Coeff3_map (a t : ℝ) :
    upperNum09Coeff3 a (a+(1-a)*t)*(a+(1-a)*t)^(3 : ℕ)*a^(3 : ℕ)=(1-a)^(4 : ℕ)*upperAtom09Coeff3 a t := by
  exact upperNum09Coeff3_map_source_value a t

end LeanVerification.PositiveDCompletion
