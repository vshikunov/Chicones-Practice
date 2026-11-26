import LeanVerification.PositiveDCompletion.LowerPolynomial05Map0Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial05Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore05Coeff0_map (a t : ℝ) :
    (((1 : ℝ)*lowerNum05Coeff0 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(4 : ℕ)+(1 : ℝ)*lowerNum05Coeff1 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(3 : ℕ))+((1 : ℝ)*lowerNum05Coeff2 a (lowerCubeF a t)*a^(2 : ℕ)*(lowerCubeF a t)^(2 : ℕ)+((1 : ℝ)*lowerNum05Coeff3 a (lowerCubeF a t)*a^(3 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(1 : ℝ)*lowerNum05Coeff4 a (lowerCubeF a t)*a^(4 : ℕ)*(lowerCubeF a t)^(0 : ℕ))))=(a-1)^(7 : ℕ)*t^(0 : ℕ)*(1-t)^(2 : ℕ)*lowerCore05Coeff0 a t := by
  exact lowerCore05Coeff0_map_source_value a t

end LeanVerification.PositiveDCompletion
