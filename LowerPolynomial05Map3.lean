import LeanVerification.PositiveDCompletion.LowerPolynomial05Map3Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial05Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore05Coeff3_map (a t : ℝ) :
    ((1 : ℝ)*lowerNum05Coeff3 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(4 : ℝ)*lowerNum05Coeff4 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(0 : ℕ))=(a-1)^(4 : ℕ)*t^(0 : ℕ)*(1-t)^(0 : ℕ)*lowerCore05Coeff3 a t := by
  exact lowerCore05Coeff3_map_source_value a t

end LeanVerification.PositiveDCompletion
