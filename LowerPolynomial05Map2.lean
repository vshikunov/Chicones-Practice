import LeanVerification.PositiveDCompletion.LowerPolynomial05Map2Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial05Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore05Coeff2_map (a t : ℝ) :
    ((1 : ℝ)*lowerNum05Coeff2 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(2 : ℕ)+((3 : ℝ)*lowerNum05Coeff3 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(6 : ℝ)*lowerNum05Coeff4 a (lowerCubeF a t)*a^(2 : ℕ)*(lowerCubeF a t)^(0 : ℕ)))=(a-1)^(5 : ℕ)*t^(0 : ℕ)*(1-t)^(0 : ℕ)*lowerCore05Coeff2 a t := by
  exact lowerCore05Coeff2_map_source_value a t

end LeanVerification.PositiveDCompletion
