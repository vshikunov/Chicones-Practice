import LeanVerification.PositiveDCompletion.LowerPolynomial09Map3Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial09Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore09Coeff3_map (a t : ℝ) :
    (((1 : ℝ)*lowerNum09Coeff3 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(3 : ℕ)+(4 : ℝ)*lowerNum09Coeff4 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(2 : ℕ))+((10 : ℝ)*lowerNum09Coeff5 a (lowerCubeF a t)*a^(2 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(20 : ℝ)*lowerNum09Coeff6 a (lowerCubeF a t)*a^(3 : ℕ)*(lowerCubeF a t)^(0 : ℕ)))=(a-1)^(7 : ℕ)*t^(0 : ℕ)*(1-t)^(1 : ℕ)*lowerCore09Coeff3 a t := by
  exact lowerCore09Coeff3_map_source_value a t

end LeanVerification.PositiveDCompletion
