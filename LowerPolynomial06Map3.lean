import LeanVerification.PositiveDCompletion.LowerPolynomial06Map3Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial06Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore06Coeff3_map (a t : ℝ) :
    (((1 : ℝ)*lowerNum06Coeff3 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(3 : ℕ)+(4 : ℝ)*lowerNum06Coeff4 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(2 : ℕ))+((10 : ℝ)*lowerNum06Coeff5 a (lowerCubeF a t)*a^(2 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(20 : ℝ)*lowerNum06Coeff6 a (lowerCubeF a t)*a^(3 : ℕ)*(lowerCubeF a t)^(0 : ℕ)))=(a-1)^(7 : ℕ)*t^(0 : ℕ)*(1-t)^(0 : ℕ)*lowerCore06Coeff3 a t := by
  exact lowerCore06Coeff3_map_source_value a t

end LeanVerification.PositiveDCompletion
