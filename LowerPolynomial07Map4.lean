import LeanVerification.PositiveDCompletion.LowerPolynomial07Map4Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial07Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore07Coeff4_map (a t : ℝ) :
    ((1 : ℝ)*lowerNum07Coeff4 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(2 : ℕ)+((5 : ℝ)*lowerNum07Coeff5 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(15 : ℝ)*lowerNum07Coeff6 a (lowerCubeF a t)*a^(2 : ℕ)*(lowerCubeF a t)^(0 : ℕ)))=(a-1)^(6 : ℕ)*t^(0 : ℕ)*(1-t)^(0 : ℕ)*lowerCore07Coeff4 a t := by
  exact lowerCore07Coeff4_map_source_value a t

end LeanVerification.PositiveDCompletion
