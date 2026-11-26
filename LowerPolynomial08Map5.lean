import LeanVerification.PositiveDCompletion.LowerPolynomial08Map5Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore08Coeff5_map (a t : ℝ) :
    ((1 : ℝ)*lowerNum08Coeff5 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(1 : ℕ)+(6 : ℝ)*lowerNum08Coeff6 a (lowerCubeF a t)*a^(1 : ℕ)*(lowerCubeF a t)^(0 : ℕ))=(a-1)^(5 : ℕ)*t^(0 : ℕ)*(1-t)^(0 : ℕ)*lowerCore08Coeff5 a t := by
  exact lowerCore08Coeff5_map_source_value a t

end LeanVerification.PositiveDCompletion
