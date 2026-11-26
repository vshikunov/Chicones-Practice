import LeanVerification.PositiveDCompletion.LowerPolynomial05Map1Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial05Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore05Coeff1_map (a t : ℝ) :
    (((1 : ℝ)*lowerNum05Coeff1 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(3 : ℕ)+(2 : ℝ)*lowerNum05Coeff2 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(2 : ℕ))+((3 : ℝ)*lowerNum05Coeff3 a (lowerCubeF a t)*a^(2 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(4 : ℝ)*lowerNum05Coeff4 a (lowerCubeF a t)*a^(3 : ℕ)*(lowerCubeF a t)^(0 : ℕ)))=(a-1)^(6 : ℕ)*t^(0 : ℕ)*(1-t)^(1 : ℕ)*lowerCore05Coeff1 a t := by
  exact lowerCore05Coeff1_map_source_value a t

end LeanVerification.PositiveDCompletion
