import LeanVerification.PositiveDCompletion.LowerPolynomial09Map6Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore09Coeff6_map (a t : ℝ) :
    (1 : ℝ)*lowerNum09Coeff6 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(0 : ℕ)=(a-1)^(4 : ℕ)*t^(1 : ℕ)*(1-t)^(0 : ℕ)*lowerCore09Coeff6 a t := by
  exact lowerCore09Coeff6_map_source_value a t

end LeanVerification.PositiveDCompletion
