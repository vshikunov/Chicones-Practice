import LeanVerification.PositiveDCompletion.LowerPolynomial07Map5Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial07Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore07Coeff5_map (a t : ℝ) :
    ((1 : ℝ)*lowerNum07Coeff5 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(6 : ℝ)*lowerNum07Coeff6 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(0 : ℕ))=(a-1)^(5 : ℕ)*t^(0 : ℕ)*(1-t)^(0 : ℕ)*lowerCore07Coeff5 a t := by
  exact lowerCore07Coeff5_map_source_value a t

end LeanVerification.PositiveDCompletion
