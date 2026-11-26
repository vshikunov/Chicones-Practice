import LeanVerification.PositiveDCompletion.LowerPolynomial06Map0Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial06Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore06Coeff0_map (a t : ℝ) :
    (((1 : ℝ)*lowerNum06Coeff0 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(6 : ℕ)+((1 : ℝ)*lowerNum06Coeff1 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(5 : ℕ)+(1 : ℝ)*lowerNum06Coeff2 a (lowerCubeF a t)*a^(2 : ℕ)*(lowerCubeF a t)^(4 : ℕ)))+(((1 : ℝ)*lowerNum06Coeff3 a (lowerCubeF a t)*a^(3 : ℕ)*(lowerCubeF a t)^(3 : ℕ)+(1 : ℝ)*lowerNum06Coeff4 a (lowerCubeF a t)*a^(4 : ℕ)*(lowerCubeF a t)^(2 : ℕ))+((1 : ℝ)*lowerNum06Coeff5 a (lowerCubeF a t)*a^(5 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(1 : ℝ)*lowerNum06Coeff6 a (lowerCubeF a t)*a^(6 : ℕ)*(lowerCubeF a t)^(0 : ℕ))))=(a-1)^(10 : ℕ)*t^(0 : ℕ)*(1-t)^(3 : ℕ)*lowerCore06Coeff0 a t := by
  exact lowerCore06Coeff0_map_source_value a t

end LeanVerification.PositiveDCompletion
