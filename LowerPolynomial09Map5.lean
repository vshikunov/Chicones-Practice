import LeanVerification.PositiveDCompletion.LowerPolynomial09Map5Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore09Coeff5_map (a t : ℝ) :
    ((1 : ℝ)*lowerNum09Coeff5 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(6 : ℝ)*lowerNum09Coeff6 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(0 : ℕ))=(a-1)^(5 : ℕ)*t^(0 : ℕ)*(1-t)^(0 : ℕ)*lowerCore09Coeff5 a t := by
  exact lowerCore09Coeff5_map_source_value a t

end LeanVerification.PositiveDCompletion
