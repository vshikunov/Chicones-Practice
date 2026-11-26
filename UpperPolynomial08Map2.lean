import LeanVerification.PositiveDCompletion.UpperPolynomial08Map2Kernel
import LeanVerification.PositiveDCompletion.UpperPolynomial08Data

noncomputable section
namespace LeanVerification.PositiveDCompletion
set_option Elab.async false
set_option maxHeartbeats 96000000
set_option maxRecDepth 100000

theorem upperNum08Coeff2_map (a t : ℝ) :
    upperNum08Coeff2 a (a+(1-a)*t)*(a+(1-a)*t)^(4 : ℕ)*a^(2 : ℕ)=(1-a)^(4 : ℕ)*upperAtom08Coeff2 a t := by
  exact upperNum08Coeff2_map_source_value a t

end LeanVerification.PositiveDCompletion
