import LeanVerification.PositiveDCompletion.UpperPolynomial08Map4Kernel
import LeanVerification.PositiveDCompletion.UpperPolynomial08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum08Coeff4_map (a t : ℝ) :
    upperNum08Coeff4 a (a+(1-a)*t)*(a+(1-a)*t)^(2 : ℕ)*a^(4 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff4 a t := by
  exact upperNum08Coeff4_map_source_value a t

end LeanVerification.PositiveDCompletion
