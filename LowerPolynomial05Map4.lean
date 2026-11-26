import LeanVerification.PositiveDCompletion.LowerPolynomial05Map4Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial05Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore05Coeff4_map (a t : ℝ) :
    (1 : ℝ)*lowerNum05Coeff4 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(0 : ℕ)=(a-1)^(3 : ℕ)*t^(1 : ℕ)*(1-t)^(0 : ℕ)*lowerCore05Coeff4 a t := by
  exact lowerCore05Coeff4_map_source_value a t

end LeanVerification.PositiveDCompletion
