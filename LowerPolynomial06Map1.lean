import LeanVerification.PositiveDCompletion.LowerPolynomial06Map1Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial06Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore06Coeff1_map (a t : ℝ) :
    (((1 : ℝ)*lowerNum06Coeff1 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(5 : ℕ)+((2 : ℝ)*lowerNum06Coeff2 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(4 : ℕ)+(3 : ℝ)*lowerNum06Coeff3 a (lowerCubeF a t)*a^(2 : ℕ)*(lowerCubeF a t)^(3 : ℕ)))+((4 : ℝ)*lowerNum06Coeff4 a (lowerCubeF a t)*a^(3 : ℕ)*(lowerCubeF a t)^(2 : ℕ)+((5 : ℝ)*lowerNum06Coeff5 a (lowerCubeF a t)*a^(4 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(6 : ℝ)*lowerNum06Coeff6 a (lowerCubeF a t)*a^(5 : ℕ)*(lowerCubeF a t)^(0 : ℕ))))=(a-1)^(9 : ℕ)*t^(0 : ℕ)*(1-t)^(2 : ℕ)*lowerCore06Coeff1 a t := by
  exact lowerCore06Coeff1_map_source_value a t

end LeanVerification.PositiveDCompletion
