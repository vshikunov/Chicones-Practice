import LeanVerification.PositiveDCompletion.UpperPolynomial08Map1Kernel
import LeanVerification.PositiveDCompletion.UpperPolynomial08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum08Coeff1_map (a t : ℝ) :
    upperNum08Coeff1 a (a+(1-a)*t)*(a+(1-a)*t)^(5 : ℕ)*a^(1 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff1 a t := by
  exact upperNum08Coeff1_map_source_value a t

end LeanVerification.PositiveDCompletion
