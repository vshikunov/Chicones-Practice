import LeanVerification.PositiveDCompletion.LowerPolynomial06Map6Kernel
import LeanVerification.PositiveDCompletion.LowerPolynomial06Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem lowerCore06Coeff6_map (a t : ℝ) :
    (1 : ℝ)*lowerNum06Coeff6 a (lowerCubeF a t)*a^(0 : ℕ)*(lowerCubeF a t)^(0 : ℕ)=(a-1)^(4 : ℕ)*t^(1 : ℕ)*(1-t)^(0 : ℕ)*lowerCore06Coeff6 a t := by
  exact lowerCore06Coeff6_map_source_value a t

end LeanVerification.PositiveDCompletion
